# cedar-spec / cedar-drt — anatomie et enseignements pour go-in-lean

Comment Cedar (AWS) formalise son langage de policies en Lean 4 et s'en sert
comme oracle *dans* la boucle de fuzz. Source : dépôt
[cedar-policy/cedar-spec](https://github.com/cedar-policy/cedar-spec) (README,
cedar-drt/README, cedar-lean-ffi/README, scripts buildés), novembre 2026.

## 1. Structure

| Composant | Rôle |
|---|---|
| `cedar-lean` | La formalisation Lean 4 de Cedar (sémantique exécutable + preuves), buildée par `lake build Cedar` |
| `cedar-lean-ffi` | **Le pont** : Rust bindings vers la spec Lean ; `build_lean_lib.sh` fait `lake build CedarFFI:static` (bibliothèque statique avec le runtime Lean embarqué) |
| `cedar-drt` | Cibles `cargo fuzz` (libFuzzer) : différentiel Rust-vs-Lean (DRT) + property-based testing (PBT) |
| `cedar-policy-generators` | Générateurs de schemas/entities/policies/requests via la crate `arbitrary` (côté Rust, pas Lean) |

## 2. Les trois décisions techniques qui rendent l'oracle Lean praticable

1. **Sérialisation plutôt que marshalling de types.** Le FFI ne convertit pas les
   types Rust en types Lean : les structures Cedar passent en **Protobuf**
   (feature protobuf de la crate Cedar côté Rust, target `CedarProto` côté Lean).
   Le pont ne transporte que des octets. C'est ce qui rend le pont maintenable :
   les deux côtés évoluent indépendamment, le contrat est le schéma.
2. **La spec Lean est *exécutable*.** L'oracle n'invoque pas de preuve à runtime :
   `lake build CedarFFI:static` compile la sémantique opérationnelle de Cedar en
   code C natif via le compilateur Lean ; le runtime Lean (`libleanshared.so`)
   est lié statiquement. Les preuves (decidability, théorèmes) garantissent
   en amont que la sémantique évaluée est la bonne — l'oracle est la sémantique
   *prouvée*, exécutée.
3. **Le générateur vit côté hôte, pas côté Lean.** `cedar-policy-generators`
   produit les entrées (souvent « type-directed », c'est-à-dire façonnées vers
   des entrées bien typées — l'équivalent de nos chaînes typées). Lean n'est
   que l'arbitre. C'est la même séparation que la nôtre : génération par
   classes côté Python, sémantique côté Lean.

## 3. La boucle DRT

```
arbitrary/générateur → entrée (policy, entités, requête)
   → évaluation par l'implémentation Rust (cedar)
   → évaluation par la spec Lean (via protobuf + FFI)
   → divergence = bug (réduit, dumpé comme test de régression)
```

- ~18 cibles : authorizer, evaluator, validator, entités/requêtes, et la
  famille TPE (autorisation partielle : décisions, catégorisations de policies,
  expressions résiduelles).
- `synthesize_tests.sh` n'est **pas** un générateur : c'est le harness qui,
  quand `DUMP_TEST_DIR` est positionné, rejoue le corpus et **dump** chaque
  entrée comme test de régression. La « synthèse » vient du fuzzing lui-même.
- Le tout tourne sous `cargo fuzz` (libFuzzer) — throughput in-process élevé,
  d'où l'FFI plutôt qu'un sous-processus.

## 4. Traduction pour go-in-lean (affinage de J1)

Le patron transposé, du plus simple au plus fidèle :

1. **Oracle par sous-processus (J1a, suffisant à notre échelle).** Notre
   coût dominant est un build+run Go par graine (secondes), pas des millions
   d'exécutations/seconde : point de besoin d'FFI in-process. Un exécutable
   Lean (`lake build goinlean-oracle`) qui lit une expression sérialisée
   (s-expression émise par le générateur à côté du programme Go) sur stdin,
   l'évalue selon `OpSem`/`GenericSem`, imprime le résultat — comparé au
   checksum du binaire réel. Contrat = la forme sérialisée, l'équivalent de
   leur protobuf.
2. **Oracle par FFI (J1b, si le throughput le justifie un jour).** Leur schéma
   exact : cible Lean `:static` + un canal binaire minimal. À ne construire
   que si l'oracle par processus devient le goulot.
3. **Tests synthétisés (J2).** Deux sens chez Cedar, à garder tous les deux :
   (a) dump de régression à partir du fuzzing (le leur) — notre triage fait
   déjà l'équivalent ; (b) notre ajout propre : **générer aux frontières des
   théorèmes** (les entrées où une précondition du modèle change de vérité —
   là où `bv_decide` produit ses contre-exemples) et injecter ces points
   comme seeds/formes. C'est le point où go-in-lean va au-delà de cedar-drt :
   leur modèle n'oriente pas la génération, le nôtre le peut.

Ce qu'il faut vérifier avant J1 (dette de modèle) : la sémantique exécutable
de `OpSem`/`GenericSem` couvre-t-elle *toutes* les opérations que le
générateur émet (sinon l'oracle refuse des programmes valides), et le
modèle est-il d'accord avec la spec Go sur les coins déjà prouvés (les 13
property.lean retrouvées par l'oracle = critère de recevabilité de J1).

## 5. Pour aller plus loin

- Blog AWS Science : « How we built Cedar with automated reasoning and
  differential testing » ; « Lean Into Verified Software Development ».
- `Cedar.SymCC` (target présente dans build_lean_lib.sh) : piste de leur côté
  vers l'analyse symbolique depuis la spec — à regarder si l'on veut un jour
  des contre-exemples SMT plutôt que seulement l'évaluation.
