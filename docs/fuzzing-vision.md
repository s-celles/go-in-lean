# Fuzzing différentiel piloté par les spécifications Lean — vision et positionnement

Étude des fuzzers existants (Mozilla Security, Project Zero, cedar-spec) et
architecture cible pour go-in-lean : réutiliser les moteurs existants et faire de
la sémantique formelle la valeur ajoutée — à la fois comme oracle et comme
producteur de programmes de test.

## 1. Ce que font les frameworks étudiés

| Framework | Mécanisme | Ce qu'on en retient pour go-in-lean |
|---|---|---|
| [jsfunfuzz](https://github.com/MozillaSecurity/funfuzz)/[funfuzz](https://github.com/MozillaSecurity/funfuzz) | Génération grammaticale de corps de fonctions JS, mode `--compare-jit` (différentiel interprète/JIT/versions), réduction par Lithium. | C'est *déjà* notre approche : générateurs par formes + oracle différentiel cross-configuration (GODEBUG, GOARCH, opt vs `-N`). Notre valeur ajoutée est ailleurs. |
| [Fuzzilli](https://github.com/googleprojectzero/fuzzilli) (NDSS 2023) | Coverage-guidé sur une **IR typée** (FuzzIL) + mutations préservant la validité + propriétés de correction ; différentiel interprète/JIT. | L'IR typée : nos générateurs émergent déjà des IR typées (chaînes typées de `simd_fuzz.py`, IR de `metamorphic_fuzz.py`). Le coverage-guidé est une optimisation possible, pas un changement de méthode — il compense par la force brute ce que le ciblage sémantique fait directement. |
| [cedar-drt](https://github.com/cedar-policy/cedar-spec/tree/main/cedar-drt) | **Fuzzing différentiel de l'implémentation Rust contre la spec Lean** (DRT) + property-based testing (round-trip, général) ; `build_lean_lib.sh` compile la spec en bibliothèque appelée depuis les cibles de fuzz ; `synthesize_tests.sh` synthétise des tests. | Le patron exact de notre trajectoire : la spec Lean devient l'**oracle dans la boucle** (pas seulement l'outil de réfutation hors ligne) et une source de **tests synthétisés**. |
| [dharma](https://github.com/MozillaSecurity/dharma)/Peach/ffuf | Grammaires context-free, model-based, fuzzing web. | Hors domaine (formats/protocoles), pas d'oracle sémantique. |

Pourquoi pas AFL++/libFuzzer/Atheris : ils mutent des octets vers des *crashes*
sur des parsers. Notre cible a une entrée structurée (programmes valides), un
coût par exécution élevé (build+run), et des bugs *silencieux* (wrong code) qu'aucun
crash ne révèle — l'oracle sémantique est indispensable. Notre méthode est celle de
Csmith/jsfunfuzz : générateur grammatical + test différentiel. Le verdict des trois
derniers jours (13 issues/CLs + 1 build failure trouvées par ciblage de classes)
plaide pour garder le ciblage sémantique comme mécanisme de guidage.

## 2. Ce que go-in-lean a déjà (état 2026-11-03)

- Sémantique opérationnelle : `GoInLean/Compiler/OpSem.lean`, `GenericSem.lean`
  (SSA op → sémantique sur vecteurs de bits), `KnownBits.lean` (analyse de bits
  connus, l'analogue du compilateur).
- Règles traduites : `GeneratedRules.lean`/`GeneratedFolds.lean` (lowering + folds
  constants générés depuis les `.rules`), familles ARM64/AMD64/MIPS/PPC64/RISCV/S390X.
- 13 `findings/*/property.lean` : chaque bug trouvé formalisé en propriété Lean.
- Le workflow existant : théorème (comportement documenté) → preuve (kernel,
  `bv_decide`) → échec de preuve = contre-exemple → test Go concret → exécution
  contre le toolchain épinglé. Une réfutation n'est jamais un bug tant qu'elle ne
  reproduit pas en Go.
- Les générateurs spécialisés « par langage/zone » : `metamorphic_fuzz.py`
  (dépassements d'entiers, conversions, replis tardifs, flags x86, late/bits/countvar
  /carry/branchy), `float_fuzz.py` (floats, conversions, FMA, `--late`),
  `bce_fuzz.py` (élimination de bounds checks), `simd_fuzz.py` (chaînes SIMD) —
  exactement les zones listées : overflows, conversions, ordre, optimisations SSA,
  différences d'architectures.

Ce qui manque pour la vision « Lean producteur *et* oracle » :
1. l'oracle Lean **dans** la boucle de fuzz (aujourd'hui l'oracle est
   cross-configuration ; Lean n'intervient qu'en amont, à la réfutation) ;
2. la **synthèse de tests dirigée par le modèle** (aujourd'hui le modèle produit
   des contre-exemples de propriétés déjà écrites, pas des programmes de fuzz).

## 3. Architecture cible

```
Modèle Lean (OpSem, GenericSem, KnownBits, GeneratedRules)
   │
   ├─ (a) Oracle : GoInLean compilé en bibliothèque (patron build_lean_lib.sh
   │      de cedar-drt) → évaluation sémantique d'un programme généré, comparée
   │      à l'exécution du binaire réel.
   │
   ├─ (b) Producteur : contre-exemples et frontières de préconditions
   │      (bv_decide / dites) → seeds et formes pour les générateurs
   │      (le fuzzer attaque systématiquement les zones où les théorèmes sont
   │      serrés : carry/borrow, largeurs mixtes, replis en chaîne, NaN, masques).
   │
   └─ (c) Réfutation : nouvelle règle lowering/fold traduite (rules_to_lean.py)
          → propriété → échec = nouveau finding (boucle actuelle, conservée).

Générateurs spécialisés (par langage/zone) → programmes Go
   → oracle (a) + oracle différentiel cross-config (existant, conservé)
   → mismatch → minimisation → finding → issue/CL (workflow établi)
```

Les deux oracles se complètent : le différentiel cross-config attrape les écarts
*entre implémentations* (et couvre tout ce que le modèle ne formalise pas encore),
l'oracle Lean compare à la *sémantique documentée* — il attrape les classes où
toutes les implémentations se trompent ensemble, invisibles au différentiel.

## 4. Jalons

1. **J1 — Patron cedar-drt sur notre sous-ensemble** : brancher un oracle Lean
   sur `metamorphic_fuzz.py --bits` (entiers, `math/bits`, le sous-ensemble déjà
   modélisé), en **sous-processus** dans un premier temps : un exécutable Lean
   évalue une expression sérialisée émise par le générateur (notre coût dominant
   est le build Go, pas l'évaluation, donc pas besoin de l'FFI in-process de
   cedar-lean-ffi ; voir `docs/cedar-notes.md` pour le patron exact et la
   variante FFI). Critère de succès : le fuzzer signale les contre-exemples
   connus (les 13 property.lean doivent être retrouvées par les
   graines) et rien de faux.
2. **J2 — Synthèse dirigée** : `synthesize_tests` à la cedar-drt : générer des
   programmes aux frontières des théorèmes (points où une hypothèse de
   précondition change de vérité) et les injecter comme seeds/formes des
   générateurs. Critère : densité de formes sémantiquement chaudes par graine
   supérieure à la génération aléatoire (mesurée en flags/1000 graines).
3. **J3 — Étendre le modèle** aux zones non couvertes : sémantique des masques
   SIMD (SIMD-MASKED-SHIFT-NOIMM a montré que le domaine est jeune), puis floats.
   Chaque extension du modèle = nouveau domaine pour (a) et (b).
4. **J4 (optionnel) — guidance par couverture** : si la génération par classes
   sature, ajouter un feedback de couverture du compilateur aux générateurs
   (à la Fuzzilli, mais sur nos IR typées).

## 5. Positionnement

Ne pas construire un concurrent généraliste d'AFL++ : les moteurs de fuzzing et
les corpus existent. La contribution de go-in-lean est la sémantique formelle —
modèle bit-précis des règles de lowering de Go, preuves kernel-checked, et
l'exploitation du modèle comme oracle et comme stratège de génération. C'est le
rapprochement de cedar-drt (spec Lean comme oracle d'implémentation) avec la
tradition Csmith/jsfunfuzz (génération de programmes), appliqué à un compilateur.
