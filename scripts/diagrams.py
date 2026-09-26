#!/usr/bin/env python3
"""Generate the SVG diagrams used in README.md.

    python3 scripts/diagrams.py

Writes images/voronoi.svg (a jittered Voronoi diagram) and images/witness_3_0.svg,
images/witness_3_1.svg (the witnesses showing that the cells (3, 0) and (3, 1) are needed).
Voronoi cells are computed by clipping a bounding box against the bisector half-planes of the
other sites, so no dependencies beyond the standard library are needed.
"""
import math
import random
from fractions import Fraction as Fr

EPS = Fr(1, 100)
# In the witness figures the sites are pulled inside their cells by a larger amount than the
# `0.01` used in Witness.lean, so that it is clear which cell each site belongs to.  The
# configuration is re-checked below, so it is still a valid witness.
DISPLAY_EPS = Fr(8, 100)


# ----------------------------------------------------------------------------- geometry

def clip(poly, a, b, c):
    """Clip a convex polygon to the half-plane a*x + b*y <= c."""
    out = []
    n = len(poly)
    for i in range(n):
        p, q = poly[i], poly[(i + 1) % n]
        fp, fq = a * p[0] + b * p[1] - c, a * q[0] + b * q[1] - c
        if fp <= 0:
            out.append(p)
        if (fp < 0 < fq) or (fq < 0 < fp):
            t = fp / (fp - fq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def voronoi_cell(site, others, box):
    """The Voronoi cell of `site` among `others`, clipped to `box` = (x0, y0, x1, y1)."""
    x0, y0, x1, y1 = box
    poly = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
    sx, sy = site
    for (ox, oy) in others:
        if (ox, oy) == (sx, sy):
            continue
        # points closer to site than to other: 2(o - s).p <= |o|^2 - |s|^2
        a, b = 2 * (ox - sx), 2 * (oy - sy)
        c = ox * ox + oy * oy - sx * sx - sy * sy
        poly = clip(poly, a, b, c)
        if not poly:
            break
    return poly


# ----------------------------------------------------------------------------- svg helpers

class Svg:
    def __init__(self, box, scale=60, margin=10):
        self.x0, self.y0, self.x1, self.y1 = box
        self.s, self.m = scale, margin
        self.w = (self.x1 - self.x0) * scale + 2 * margin
        self.h = (self.y1 - self.y0) * scale + 2 * margin
        self.parts = []
        self.prims = []  # (kind, data) for the optional PNG preview

    def X(self, x):
        return self.m + (x - self.x0) * self.s

    def Y(self, y):
        return self.m + (self.y1 - y) * self.s

    def pt(self, p):
        return f"{self.X(p[0]):.2f},{self.Y(p[1]):.2f}"

    def polygon(self, poly, fill, stroke="none", width=1, dash=None, opacity=1):
        d = f' stroke-dasharray="{dash}"' if dash else ""
        pts = " ".join(self.pt(p) for p in poly)
        self.parts.append(f'<polygon points="{pts}" fill="{fill}" stroke="{stroke}" '
                          f'stroke-width="{width}"{d} fill-opacity="{opacity}"/>')
        self.prims.append(("polygon", [(self.X(p[0]), self.Y(p[1])) for p in poly], fill, stroke, width, opacity))

    def line(self, p, q, stroke, width=1, dash=None):
        d = f' stroke-dasharray="{dash}"' if dash else ""
        self.parts.append(f'<line x1="{self.X(p[0]):.2f}" y1="{self.Y(p[1]):.2f}" '
                          f'x2="{self.X(q[0]):.2f}" y2="{self.Y(q[1]):.2f}" '
                          f'stroke="{stroke}" stroke-width="{width}"{d}/>')
        self.prims.append(("line", (self.X(p[0]), self.Y(p[1]), self.X(q[0]), self.Y(q[1])), stroke, width))

    def circle(self, c, r, fill="none", stroke="none", width=1, dash=None, radius_units=True):
        rr = r * self.s if radius_units else r
        d = f' stroke-dasharray="{dash}"' if dash else ""
        self.parts.append(f'<circle cx="{self.X(c[0]):.2f}" cy="{self.Y(c[1]):.2f}" r="{rr:.2f}" '
                          f'fill="{fill}" stroke="{stroke}" stroke-width="{width}"{d}/>')
        self.prims.append(("circle", (self.X(c[0]), self.Y(c[1]), rr), fill, stroke, width))

    def text(self, p, s, dx=0, dy=0, size=12, fill="#222", anchor="start", weight="normal"):
        self.parts.append(f'<text x="{self.X(p[0]) + dx:.2f}" y="{self.Y(p[1]) + dy:.2f}" '
                          f'font-family="Helvetica, Arial, sans-serif" font-size="{size}" '
                          f'fill="{fill}" text-anchor="{anchor}" font-weight="{weight}">{s}</text>')
        self.prims.append(("text", (self.X(p[0]) + dx, self.Y(p[1]) + dy), s, size, fill))

    def grid(self, stroke="#999", width=1, dash="2,3"):
        for i in range(int(self.x0), int(self.x1) + 1):
            self.line((i, self.y0), (i, self.y1), stroke, width, dash)
        for j in range(int(self.y0), int(self.y1) + 1):
            self.line((self.x0, j), (self.x1, j), stroke, width, dash)

    def preview_png(self, path, zoom=2):
        """Rough rasterisation with Pillow, for checking the figures without an SVG viewer."""
        from PIL import Image, ImageDraw
        img = Image.new("RGBA", (int(self.w * zoom), int(self.h * zoom)), "white")
        draw = ImageDraw.Draw(img, "RGBA")

        def col(c, opacity=1.0):
            if c == "none":
                return None
            if c == "white":
                return (255, 255, 255, int(255 * opacity))
            c = c.lstrip("#")
            if len(c) == 3:
                c = "".join(ch * 2 for ch in c)
            r, g, b = int(c[0:2], 16), int(c[2:4], 16), int(c[4:6], 16)
            return (r, g, b, int(255 * opacity))

        for prim in self.prims:
            kind = prim[0]
            if kind == "polygon":
                _, pts, fill, stroke, width, opacity = prim
                pts = [(x * zoom, y * zoom) for x, y in pts]
                if len(pts) >= 3:
                    draw.polygon(pts, fill=col(fill, opacity))
                    if stroke != "none":
                        draw.line(pts + [pts[0]], fill=col(stroke), width=max(1, int(width * zoom)))
            elif kind == "line":
                _, (x1, y1, x2, y2), stroke, width = prim
                draw.line([(x1 * zoom, y1 * zoom), (x2 * zoom, y2 * zoom)], fill=col(stroke),
                          width=max(1, int(width * zoom)))
            elif kind == "circle":
                _, (cx, cy, r), fill, stroke, width = prim
                bb = [(cx - r) * zoom, (cy - r) * zoom, (cx + r) * zoom, (cy + r) * zoom]
                draw.ellipse(bb, fill=col(fill), outline=col(stroke), width=max(1, int(width * zoom)))
            elif kind == "text":
                _, (x, y), txt, size, fill = prim
                draw.text((x * zoom, (y - size) * zoom), txt, fill=col(fill))
        img.save(path)

    def save(self, path):
        body = "\n".join(self.parts)
        svg = (f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w:.0f}" height="{self.h:.0f}" '
               f'viewBox="0 0 {self.w:.0f} {self.h:.0f}">\n<rect width="100%" height="100%" fill="white"/>\n'
               f'{body}\n</svg>\n')
        with open(path, "w") as fh:
            fh.write(svg)


PALETTE = ["#cfe8f3", "#fde2c8", "#d6efd0", "#efd6ef", "#fff3c4", "#d9e4f5", "#f6d5d5", "#dff0ec"]


# ----------------------------------------------------------------------------- diagram 1

def diagram_voronoi(path, n=8, seed=3, preview=None):
    rng = random.Random(seed)
    margin = 3  # extra cells so the visible cells are correct
    sites = {(a, b): (a + rng.random(), b + rng.random())
             for a in range(-margin, n + margin) for b in range(-margin, n + margin)}
    box = (0, 0, n, n)
    svg = Svg(box, scale=50)
    allsites = list(sites.values())
    k = 0
    for (a, b), s in sites.items():
        if not (-1 <= a <= n and -1 <= b <= n):
            continue
        cell = voronoi_cell(s, allsites, (-1, -1, n + 1, n + 1))
        cell = clip(clip(clip(clip(cell, -1, 0, 0), 1, 0, n), 0, -1, 0), 0, 1, n)
        if cell:
            svg.polygon(cell, PALETTE[(a * 3 + b * 5) % len(PALETTE)], stroke="#555", width=1.2)
        k += 1
    svg.grid(stroke="#999", width=0.8)
    for (a, b), s in sites.items():
        if 0 <= a < n and 0 <= b < n:
            svg.circle(s, 3, fill="#333", radius_units=False)
    svg.save(path)
    if preview:
        svg.preview_png(preview)


# ----------------------------------------------------------------------------- diagram 2

# Witness data from JitteredVoronoi/Witness.lean (origin's site, test point, site in the cell).
WITNESSES = {
    (3, 0): ((Fr("0.9"), Fr("0.25")), (Fr("2.05"), Fr("0")), (Fr("3.01"), Fr("0.01"))),
    (3, 1): ((Fr("0.95"), Fr("0.99")), (Fr("2.1"), Fr("1")), (Fr("3.01"), Fr("1.01"))),
}

NBHD = [(a, b) for a in range(-3, 4) for b in range(-3, 4) if abs(a) + abs(b) <= 4]


def far(u, a, eps=EPS, low_eps=Fr(0)):
    """The end of the cell `[a, a+1)` farthest from `u`, pulled inside the cell by `eps` at the
    excluded end and by `low_eps` at the included end (the latter only for the figures)."""
    return a + 1 - eps if u <= a + Fr(1, 2) else a + low_eps


def diagram_witness(cell, path, preview=None):
    origin, test, site = WITNESSES[cell]
    # exaggerate the offsets from the cell corners for legibility (see DISPLAY_EPS); the
    # origin's site is kept at least DISPLAY_EPS inside its cell as well
    site = (cell[0] + DISPLAY_EPS, cell[1] + DISPLAY_EPS)
    origin = tuple(min(max(t, DISPLAY_EPS), 1 - DISPLAY_EPS) for t in origin)
    box = (-3, -3, 4, 4)
    svg = Svg(box, scale=60, margin=12)
    R = 6
    sites = {}
    for a in range(-R, R + 1):
        for b in range(-R, R + 1):
            if (a, b) == (0, 0):
                sites[(a, b)] = origin
            elif (a, b) == cell:
                sites[(a, b)] = site
            else:
                sites[(a, b)] = (far(test[0], a, DISPLAY_EPS, DISPLAY_EPS),
                                 far(test[1], b, DISPLAY_EPS, DISPLAY_EPS))
    # the displayed configuration must still be a witness
    r2 = lambda q: (test[0] - q[0]) ** 2 + (test[1] - q[1]) ** 2
    assert r2(site) < r2(origin), "site in the tested cell must be closer than the origin's"
    assert all(r2(origin) <= r2(sites[c]) for c in NBHD if c != cell), "a neighbourhood site is too close"
    f = {k: (float(v[0]), float(v[1])) for k, v in sites.items()}
    p = (float(test[0]), float(test[1]))
    # shading: neighbourhood cells and the cell under test
    for (a, b) in NBHD:
        svg.polygon([(a, b), (a + 1, b), (a + 1, b + 1), (a, b + 1)], "#e3eaf5")
    a, b = cell
    svg.polygon([(a, b), (a + 1, b), (a + 1, b + 1), (a, b + 1)], "#fde2c8")
    svg.grid(stroke="#999", width=0.8)
    # Voronoi cell of the origin's site: from the neighbourhood only, and from all sites
    clipbox = (-3.5, -3.5, 4.5, 4.5)
    local = voronoi_cell(f[(0, 0)], [f[c] for c in NBHD if c != cell], clipbox)
    true = voronoi_cell(f[(0, 0)], list(f.values()), clipbox)
    svg.polygon(local, "#2e86c1", stroke="#2e86c1", width=2, dash="6,4", opacity=0.10)
    svg.polygon(true, "#27ae60", stroke="#27ae60", width=2, opacity=0.25)
    # the empty circle through the origin's site around the test point
    r = math.dist(p, f[(0, 0)])
    svg.circle(p, r, stroke="#c0392b", width=1.5, dash="3,3")
    # sites
    for c, s in f.items():
        if c in NBHD:  # only the neighbourhood's sites are shown
            col = "#c0392b" if c == cell else ("#1a5276" if c == (0, 0) else "#333")
            svg.circle(s, 4 if c in (cell, (0, 0)) else 3, fill=col, radius_units=False)
    svg.circle(p, 4, fill="white", stroke="#c0392b", width=2, radius_units=False)
    svg.text(p, "p", dx=6, dy=-6, size=14, fill="#c0392b", weight="bold")
    svg.text(f[(0, 0)], "f(0,0)", dx=-8, dy=16, size=12, fill="#1a5276", weight="bold")
    svg.text(f[cell], f"f{cell}", dx=6, dy=16, size=12, fill="#c0392b", weight="bold")
    svg.save(path)
    if preview:
        svg.preview_png(preview)


if __name__ == "__main__":
    import sys
    # optional: a directory for rough PNG previews (needs Pillow)
    pv = sys.argv[1] if len(sys.argv) > 1 else None
    diagram_voronoi("images/voronoi.svg", preview=pv and f"{pv}/voronoi.png")
    diagram_witness((3, 0), "images/witness_3_0.svg", preview=pv and f"{pv}/witness_3_0.png")
    diagram_witness((3, 1), "images/witness_3_1.svg", preview=pv and f"{pv}/witness_3_1.png")
    print("wrote images/voronoi.svg images/witness_3_0.svg images/witness_3_1.svg")
