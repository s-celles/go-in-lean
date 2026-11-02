#!/usr/bin/env python3
"""Generate the go-in-lean visual identity (assets/brand/*.svg) from its construction.

Every shape is computed here from integer coordinates on a 64-unit grid, so the
identity is reproducible and reviewable like the rest of the repository. Run
with --check to verify that the committed SVG files are up to date, and with
--png to also rasterise the PNG exports (needs `rsvg-convert`, from librsvg).

The mark ("goéland", French for seagull) is two mirror-image wings: the left
one in cyan (Go), the right one in ink (Lean). Same shape on both sides of the
axis: an implementation and its model, checked to agree. See docs/brand.md.
"""
import math, os, shutil, subprocess, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
OUT = os.path.join(ROOT, "assets", "brand")

# --- palette -----------------------------------------------------------------
INK = "#14202B"      # Lean half, wordmark, text on light backgrounds
PAPER = "#FFFFFF"
NIGHT = "#0D151C"    # dark background
MIST = "#E6EDF2"     # Lean half, wordmark, text on dark backgrounds
CYAN = "#0A8DB3"     # Go half on light backgrounds
CYAN_D = "#3CC0E4"   # Go half on dark backgrounds
SIGNAL = "#B06A00"   # counterexamples / findings only, never decorative (light bg)
SIGNAL_D = "#E39B17" # same role on dark backgrounds
SLATE = "#5B6B78"    # secondary text on light
SLATE_D = "#8FA1AE"  # secondary text on dark

# --- the mark: construction on a 64 x 64 integer grid --------------------------
# Leading edge of the arm rises with slope 3:4 (a 3-4-5 triangle), leading edge
# of the hand falls with slope 1:2; the trailing edge of the arm is parallel to
# its leading edge. Every vertex is an integer point.
T = (32, 34)   # top of the axis (shoulder)
W = (16, 22)   # wrist, leading edge:   T + 4*(-4, -3)
P = (2, 29)    # wing tip:              W + 7*(-2, 1)
B = (32, 42)   # bottom of the axis (body)
U = (20, 33)   # wrist, trailing edge:  B + 3*(-4, -3)
GAP = 1        # each half is moved 1 unit off the axis: the axis stays visible
LEFT = [(x - GAP, y) for x, y in (P, W, T, B, U)]

# Optical-size cut for 16-32 px (favicon): same leading edges, arm 12 units
# thick instead of 8 so the wings survive pixel snapping.
FAV_LEFT = [(x - GAP, y) for x, y in ((2, 27), (16, 20), (32, 32), (32, 44), (20, 35))]


def mirror(pts):
    return [(64 - x, y) for x, y in pts]


def num(v):
    s = f"{v:.3f}".rstrip("0").rstrip(".")
    return "0" if s == "-0" else s


def pts(points):
    return " ".join(f"{num(x)},{num(y)}" for x, y in points)


def polygon(points, fill, extra=""):
    return f'<polygon points="{pts(points)}" fill="{fill}"{extra}/>'


def mark(go, lean, dx=0.0, dy=0.0, s=1.0):
    """The mark, translated by (dx, dy) and scaled by s about the origin."""
    tr = lambda p: [(dx + s * x, dy + s * y) for x, y in p]
    return polygon(tr(LEFT), go) + polygon(tr(mirror(LEFT)), lean)


def svg(w, h, body, title, view=None, extra=""):
    view = view or f"0 0 {num(w)} {num(h)}"
    return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{num(w)}" height="{num(h)}" '
            f'viewBox="{view}" role="img" aria-label="{title}"{extra}>\n'
            f'<title>{title}</title>\n{body}\n</svg>\n')


# --- wordmark: monoline lowercase built on the same grid -----------------------
# x-height 20, ascender 28, descender 8, 45-degree chamfers of 4, stroke 3.6.
XH, ASC, DESC, CH, STROKE, LW = 20, 28, 8, 4, 3.6, 13


def glyph(ch, x):
    """Centre-line path of one glyph at pen position x (baseline y = 0); returns (d, advance)."""
    w, c, X = LW, CH, XH
    M = lambda *p: "M" + " L".join(f"{num(x + a)},{num(b)}" for a, b in p)
    if ch == "o":
        return M((c, -X), (w - c, -X), (w, -X + c), (w, -c), (w - c, 0), (c, 0), (0, -c), (0, -X + c)) + " Z", w
    if ch == "a":
        return M((w, 0), (c, 0), (0, -c), (0, -X + c), (c, -X), (w, -X), (w, 0)), w
    if ch == "g":
        return (M((w, 0), (c, 0), (0, -c), (0, -X + c), (c, -X), (w, -X), (w, DESC - c), (w - c, DESC), (1, DESC)), w)
    if ch == "e":
        return M((0, -X / 2), (w, -X / 2), (w, -X + c), (w - c, -X), (c, -X), (0, -X + c), (0, -c), (c, 0), (w - 1, 0)), w
    if ch == "n":
        return M((0, 0), (0, -X), (w - c, -X), (w, -X + c), (w, 0)), w
    if ch == "i":
        e = 0.1  # the dot: a tiny closed square, stroked into a square of side STROKE
        return M((0, 0), (0, -X)) + " " + M((-e, -X - 8 - e), (e, -X - 8 - e), (e, -X - 8 + e), (-e, -X - 8 + e)) + " Z", 0
    if ch == "l":
        return M((0, 0), (0, -ASC)), 0
    if ch == "-":
        return M((0, -X / 2), (8, -X / 2)), 8
    raise KeyError(ch)


def wordmark(text="go-in-lean", track=7.5):
    """Returns (path d, width) for the wordmark, outer stroke edge at x = 0."""
    x, parts = STROKE / 2, []
    for i, ch in enumerate(text):
        d, adv = glyph(ch, x)
        parts.append(d)
        x += adv + (track if ch != "-" and (i + 1 == len(text) or text[i + 1] != "-") else track - 1.5)
    return " ".join(parts), x - track + STROKE / 2


def word(fill, dx, dy, s):
    d, _ = wordmark()
    return (f'<path d="{d}" transform="translate({num(dx)} {num(dy)}) scale({num(s)})" fill="none" '
            f'stroke="{fill}" stroke-width="{STROKE}" stroke-linejoin="miter" stroke-linecap="square"/>')


# --- outputs ------------------------------------------------------------------
TITLE = "go-in-lean"


def mark_file(go, lean, title=TITLE + " mark"):
    # tight box around the 64-grid silhouette with a 2-unit margin, so the
    # file sits well in a line of text and in badges; square variant below.
    return svg(64, 64, mark(go, lean), title)


def favicon():
    style = ("<style>.g{fill:%s}.l{fill:%s}"
             "@media (prefers-color-scheme: dark){.g{fill:%s}.l{fill:%s}}</style>" % (CYAN, INK, CYAN_D, MIST))
    body = style + f'<polygon class="g" points="{pts(FAV_LEFT)}"/><polygon class="l" points="{pts(mirror(FAV_LEFT))}"/>'
    return svg(64, 64, body, TITLE)


def lockup(go, lean, text_col, bg=None):
    # mark height on canvas: 20 grid units * s; wordmark x-height aligned to it.
    s = 4.0                          # mark scale
    h_mark = 20 * s                  # 80 px tall silhouette (y 22..42 on the grid)
    k = h_mark / (ASC + DESC)    # wordmark scale: ascender to descender = mark height
    _, ww = wordmark()
    pad, gutter = 8, 28
    mark_w = 60 * s
    width = pad + mark_w + gutter + ww * k + pad
    height = h_mark + 2 * pad
    body = (f'<rect width="100%" height="100%" fill="{bg}"/>' if bg else "")
    body += mark(go, lean, dx=pad - 2 * s, dy=pad - 22 * s, s=s)
    body += word(text_col, pad + mark_w + gutter, pad + ASC * k, k)
    return svg(width, height, body, TITLE)


def construction():
    """Construction drawing of the mark for docs/brand.md (light background)."""
    s, o = 9, 24
    g = lambda p: (o + s * p[0], o + s * p[1])
    body = [f'<rect width="100%" height="100%" fill="{PAPER}"/>']
    for i in range(0, 65, 2):
        w = "0.6" if i % 8 else "1"
        col = "#DCE3E8" if i % 8 else "#C5D0D8"
        body.append(f'<line x1="{o + s*i}" y1="{o + s*14}" x2="{o + s*i}" y2="{o + s*50}" stroke="{col}" stroke-width="{w}"/>')
    for j in range(14, 51, 2):
        w = "0.6" if j % 8 else "1"
        col = "#DCE3E8" if j % 8 else "#C5D0D8"
        body.append(f'<line x1="{o}" y1="{o + s*j}" x2="{o + s*64}" y2="{o + s*j}" stroke="{col}" stroke-width="{w}"/>')
    body.append(f'<g opacity="0.92">{mark(CYAN, INK, dx=o, dy=o, s=s)}</g>')
    body.append(f'<line x1="{o + s*32}" y1="{o + s*15}" x2="{o + s*32}" y2="{o + s*49}" stroke="{SIGNAL}" stroke-width="1.5" stroke-dasharray="6 5"/>')
    font = 'font-family="ui-monospace, SFMono-Regular, Menlo, Consolas, monospace" font-size="15"'
    labels = {"T": T, "W": W, "P": P, "B": B, "U": U}
    offs = {"T": (10, -6), "W": (-6, -12), "P": (-4, -12), "B": (10, 18), "U": (-4, 22)}
    for name, p in labels.items():
        x, y = g((p[0] - GAP, p[1]))
        body.append(f'<rect x="{num(x - 4)}" y="{num(y - 4)}" width="8" height="8" fill="{PAPER}" stroke="{INK}" stroke-width="1.5"/>')
        dx, dy = offs[name]
        body.append(f'<text x="{num(x + dx)}" y="{num(y + dy)}" {font} fill="{INK}" stroke="{PAPER}" '
                    f'stroke-width="5" stroke-linejoin="round" paint-order="stroke">{name} {p}</text>')
    notes = ["arm  T→W  slope 3:4  (3-4-5 triangle)", "hand W→P  slope 1:2",
             "B→U parallel to T→W", "halves offset 1 unit from the axis"]
    for i, n in enumerate(notes):
        body.append(f'<text x="{o}" y="{o + s*54 + 22*i}" {font} fill="{SLATE}">{n}</text>')
    # the drawing spans grid rows 14..50: shift it up so the canvas starts there
    inner = "\n".join(body[1:])
    return svg(o * 2 + s * 64, o + s * 40 + 22 * len(notes) + 10,
               body[0] + f'\n<g transform="translate(0 {-s * 14})">\n{inner}\n</g>', TITLE + " construction")


def social():
    W_, H_ = 1280, 640
    body = [f'<rect width="{W_}" height="{H_}" fill="{NIGHT}"/>']
    # the construction grid, faint: 8-unit majors of the mark grid
    for x in range(0, W_ + 1, 40):
        body.append(f'<line x1="{x}" y1="0" x2="{x}" y2="{H_}" stroke="#16222C" stroke-width="1"/>')
    for y in range(0, H_ + 1, 40):
        body.append(f'<line x1="0" y1="{y}" x2="{W_}" y2="{y}" stroke="#16222C" stroke-width="1"/>')
    s = 7.5
    body.append(mark(CYAN_D, MIST, dx=640 - 32 * s, dy=250 - 32 * s, s=s))
    _, ww = wordmark()
    k = 2.6
    body.append(word(MIST, 640 - ww * k / 2, 420, k))
    font = 'font-family="ui-sans-serif, -apple-system, Segoe UI, Helvetica, Arial, sans-serif"'
    body.append(f'<text x="640" y="500" text-anchor="middle" {font} font-size="30" fill="{SLATE_D}">'
                f'Lean 4 models of Go: integer semantics, standard library, SSA rewrite rules</text>')
    body.append(f'<text x="640" y="548" text-anchor="middle" {font} font-size="24" fill="{SLATE_D}">'
                f'kernel-checked proofs · counterexamples replayed in real Go</text>')
    return svg(W_, H_, "\n".join(body), TITLE)


def avatar():
    s = 0.84
    return svg(64, 64, f'<rect width="64" height="64" fill="{PAPER}"/>' + mark(CYAN, INK, dx=32 * (1 - s), dy=32 * (1 - s), s=s), TITLE)


# --- exploration (kept for the record; not for use) ---------------------------
def clip(poly, a, b, c):
    """Sutherland-Hodgman: keep the part of convex poly with a*x + b*y + c >= 0."""
    out = []
    for i, p in enumerate(poly):
        q = poly[(i + 1) % len(poly)]
        fp, fq = a * p[0] + b * p[1] + c, a * q[0] + b * q[1] + c
        if fp >= 0:
            out.append(p)
        if (fp >= 0) != (fq >= 0):
            t = fp / (fp - fq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def keep(poly, p0, p1, gap, ref):
    """Part of poly on ref's side of line p0-p1, set back by gap/2."""
    dx, dy = p1[0] - p0[0], p1[1] - p0[1]
    n = math.hypot(dx, dy)
    a, b = -dy / n, dx / n
    c = -(a * p0[0] + b * p0[1])
    if a * ref[0] + b * ref[1] + c < 0:
        a, b, c = -a, -b, -c
    return clip(poly, a, b, c - gap / 2)


def concept_a(go, lean, sig):
    return mark(go, lean)


def concept_b(go, lean, sig, gap=1.6):
    """Origami / bitvector: each wing cut into 4 facets, 8 in all (a byte); one flipped bit."""
    hand = keep([P, W, U], W, U, gap, P)
    arm = keep([W, T, B, U], W, U, gap, T)
    d = (U[0] - W[0], U[1] - W[1])
    h0 = (9, 22); a0 = (24, 28)
    facets = [keep(hand, h0, (h0[0] + d[0], h0[1] + d[1]), gap, P),
              keep(hand, h0, (h0[0] + d[0], h0[1] + d[1]), gap, W),
              keep(arm, a0, (a0[0] + d[0], a0[1] + d[1]), gap, W),
              keep(arm, a0, (a0[0] + d[0], a0[1] + d[1]), gap, T)]
    out = []
    for i, f in enumerate(facets):
        f = [(x - GAP, y) for x, y in f]
        out.append(polygon(f, go))
        out.append(polygon(mirror(f), sig if i == 1 else lean))
    return "".join(out)


def concept_c(go, lean, sig):
    """SSA graph / flight path: the wing skeleton as a value graph; one node is a counterexample."""
    C = (32, 38)
    nodes = [P, W, C, mirror([W])[0], mirror([P])[0]]
    out = []
    for i, (p, q) in enumerate(zip(nodes, nodes[1:])):
        out.append(f'<line x1="{p[0]}" y1="{p[1]}" x2="{q[0]}" y2="{q[1]}" stroke="{go if i < 2 else lean}" stroke-width="3"/>')
    for i, p in enumerate(nodes):
        r = 3.6
        out.append(polygon([(p[0], p[1] - r), (p[0] + r, p[1]), (p[0], p[1] + r), (p[0] - r, p[1])],
                           sig if i == 4 else (go if i < 2 else lean)))
    return "".join(out)


CONCEPTS = [("A", "Geometric seagull: two mirror-image wings, Go and Lean", concept_a),
            ("B", "Origami / bitvector: 8 facets, one flipped bit", concept_b),
            ("C", "SSA graph: the wing skeleton as a value graph", concept_c)]


def exploration_sheet():
    sizes, cellw = [16, 32, 64, 192], 360
    rowh = 250
    W_, H_ = 2 * (cellw + 40) + 40 + 300, len(CONCEPTS) * rowh + 40
    font = 'font-family="ui-monospace, SFMono-Regular, Menlo, Consolas, monospace"'
    body = [f'<rect width="100%" height="100%" fill="{PAPER}"/>']
    for r, (name, desc, fn) in enumerate(CONCEPTS):
        y0 = 20 + r * rowh
        body.append(f'<text x="20" y="{y0 + 24}" {font} font-size="20" font-weight="bold" fill="{INK}">{name}</text>')
        body.append(f'<text x="20" y="{y0 + 48}" {font} font-size="12" fill="{SLATE}">{desc.split(":")[0]}</text>')
        for c, dark in enumerate((False, True)):
            x0 = 320 + c * (cellw + 40 + 40)
            go, lean, sig, bg = (CYAN_D, MIST, SIGNAL_D, NIGHT) if dark else (CYAN, INK, SIGNAL, "#F3F6F8")
            body.append(f'<rect x="{x0}" y="{y0}" width="{cellw + 40}" height="{rowh - 20}" fill="{bg}"/>')
            x = x0 + 16
            for sz in sizes[:3]:
                body.append(f'<svg x="{x}" y="{y0 + 30}" width="{sz}" height="{sz}" viewBox="0 0 64 64">{fn(go, lean, sig)}</svg>')
                x += sz + 20
            big = sizes[3]
            body.append(f'<svg x="{x0 + cellw + 40 - big - 10}" y="{y0 + (rowh - 20 - big) / 2}" width="{big}" height="{big}" viewBox="0 0 64 64">{fn(go, lean, sig)}</svg>')
    return svg(W_, H_, "\n".join(body), TITLE + " concept exploration")


def files():
    out = {
        "mark.svg": mark_file(CYAN, INK),
        "mark-dark.svg": mark_file(CYAN_D, MIST),
        "mark-mono-black.svg": mark_file("#000000", "#000000"),
        "mark-mono-white.svg": mark_file("#FFFFFF", "#FFFFFF"),
        "favicon.svg": favicon(),
        "lockup.svg": lockup(CYAN, INK, INK),
        "lockup-dark.svg": lockup(CYAN_D, MIST, MIST),
        "avatar.svg": avatar(),
        "social-preview.svg": social(),
        "construction.svg": construction(),
        "exploration/sheet.svg": exploration_sheet(),
    }
    for name, desc, fn in CONCEPTS:
        out[f"exploration/concept-{name.lower()}.svg"] = svg(64, 64, fn(CYAN, INK, SIGNAL), f"{TITLE} concept {name}")
    return out


PNGS = [("social-preview.svg", "social-preview.png", 1280), ("avatar.svg", "avatar-512.png", 512),
        ("mark.svg", "mark-512.png", 512), ("mark-dark.svg", "mark-dark-512.png", 512),
        ("favicon.svg", "favicon-32.png", 32), ("favicon.svg", "apple-touch-icon.png", 180)]


def main(argv):
    check = "--check" in argv
    stale = []
    for name, content in files().items():
        path = os.path.join(OUT, name)
        if check:
            if not os.path.exists(path) or open(path, encoding="utf-8").read() != content:
                stale.append(name)
            continue
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(content)
    if check:
        if stale:
            raise SystemExit("brand assets out of date (run scripts/gen_brand.py): " + ", ".join(stale))
        print("brand assets up to date")
        return
    if "--png" in argv:
        exe = shutil.which("rsvg-convert") or sys.exit("--png needs rsvg-convert (librsvg)")
        os.makedirs(os.path.join(OUT, "png"), exist_ok=True)
        for src, dst, w in PNGS:
            # rsvg ignores the favicon's dark-mode media query: PNGs use the light colours
            subprocess.run([exe, "-w", str(w), os.path.join(OUT, src), "-o", os.path.join(OUT, "png", dst)], check=True)
    print(f"wrote {len(files())} SVG files to assets/brand/")


if __name__ == "__main__":
    main(sys.argv[1:])
