# SPDX-License-Identifier: LGPL-3.0-or-later
"""Generates the diagrams that accompany the proofs of the paper.

The tilings are those listed by the search or are regenerated from their records by the figure generator; staircases that no tiling has are obtained by placing tiles with free sides or orientations for which a tile does not fit, and are computed by the placing procedure.
"""

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import sympy as sp
from matplotlib.patches import FancyArrowPatch, Polygon, Rectangle
from matplotlib.path import Path as MplPath

from make_diagrams import CODES, DATA, EPS, FIT_NAMES, OUT, base_tiling, classes, construction_choice, extends, listing, mark_anchors, moves_of, outline_rest, stages
from make_figures import COLOURS, Tier, draw, witness_tiles

LETTERS = {v: k for k, v in CODES.items()}


def fplace(tiers, i, fit, tall, side, x):
    """Places a tile on a real staircase, returning the new staircase and the tile."""
    t = tiers[i]
    if fit == "inside":
        w, h = (side, x * side) if tall else (x * side, side)
    elif fit == "full-height":
        h = t.wall
        w = h / x if tall else x * h
    elif fit == "full-width":
        w = t.floor
        h = x * w if tall else w / x
    else:
        w, h = t.floor, t.wall
    return fplace_tile(tiers, i, fit, w, h), (t.ax, t.ay, w, h)


def fplace_tile(tiers, i, fit, w, h):
    """Returns the staircase after a tile of a given size is placed with a given fit."""
    t = tiers[i]
    low, narrow = fit in ("inside", "full-width"), fit in ("inside", "full-height")
    new = [Tier(u.ax, u.ay, u.floor, u.wall, True, u.started) for u in tiers[:i]]
    if not low and i > 0:
        p = new[i - 1]
        new[i - 1] = Tier(p.ax, p.ay, p.floor + w, p.wall, False, p.started)
    if fit == "inside":
        new += [Tier(t.ax, t.ay + h, w, t.wall - h), Tier(t.ax + w, t.ay, t.floor - w, h, False, True)]
    elif fit == "full-height":
        new.append(Tier(t.ax + w, t.ay, t.floor - w, t.wall, False, True))
    elif fit == "full-width":
        new.append(Tier(t.ax, t.ay + h, t.floor, t.wall - h))
    rest = list(tiers[i + 1 :])
    if not narrow and rest:
        b = rest[0]
        rest[0] = Tier(b.ax, b.ay, b.floor, b.wall + h, b.stale, b.started)
    return new + rest


def same(t, g, tol=1e-8):
    """Whether two rectangles coincide."""
    return max(abs(c - d) for c, d in zip(t, g)) < tol


def crossings(tiles):
    """Returns the points that are the top-left corner of a tile and the bottom-right corner of another."""
    out = []
    for x, y, w, h in tiles:
        q = (x, y + h)
        if any(abs(a + c - q[0]) < EPS and abs(b - q[1]) < EPS for a, b, c, _ in tiles):
            out.append(q)
    return sorted(out)


def build(tiles, chosen=()):
    """Returns the record of a tiling of the unit square that places each tile at the first tier whose floor extends only to a chosen crossing, as the tiles in order, the placements and the staircases."""
    tiers = [Tier(0.0, 0.0, 1.0, 1.0)]
    left = list(tiles)
    order, moves, sts = [], [], [tiers]
    while tiers:
        i = next(j for j, t in enumerate(tiers) if not (extends(tiles, t.ax + t.floor, t.ay) and not any(abs(t.ax + t.floor - q[0]) < EPS and abs(t.ay - q[1]) < EPS for q in chosen)))
        t = tiers[i]
        tile = next(r for r in left if abs(r[0] - t.ax) < EPS and abs(r[1] - t.ay) < EPS)
        left.remove(tile)
        _, _, w, h = tile
        assert w <= t.floor + EPS and h <= t.wall + EPS
        narrow, low = w < t.floor - EPS, h < t.wall - EPS
        fit = "inside" if narrow and low else "full-height" if narrow else "full-width" if low else "full"
        assert not t.stale and not (not low and i > 0 and tiers[i - 1].started)
        tiers = fplace_tile(tiers, i, fit, w, h)
        order.append(tile)
        moves.append((i, fit, h > w + EPS))
        sts.append(tiers)
    assert not left
    return order, moves, sts


def witness(moves):
    """Encodes placements as a witness."""
    return " ".join(f"{i}{LETTERS[fit]}{'T' if tall else 'W'}" for i, fit, tall in moves)


def regenerate(tiles, proportion, chosen=()):
    """Returns the tiles that the figure generator computes from a record of a tiling given by exact coordinates, in the order of the record, checking that they are the given ones."""
    given = [tuple(float(c) for c in t) for t in tiles]
    order, moves, sts = build(given, chosen)
    drawn = witness_tiles(str(sp.Rational(proportion).evalf(30)), witness(moves))
    assert len(drawn) == len(order) and all(same(t, g) for t, g in zip(drawn, order)), witness(moves)
    return drawn, moves, sts


def box(x, y, w, h):
    """Returns the corners of a rectangle."""
    return [(x, y), (x + w, y), (x + w, y + h), (x, y + h)]


MARKS = {
    "dot": dict(marker="o", ms=0.9, mew=0),
    "plus": dict(marker="+", ms=2.4, mew=0.35),
    "cross": dict(marker="x", ms=2.0, mew=0.35),
    "dagger": dict(marker="$\\dagger$", ms=3.0, mew=0),
    "asterisk": dict(marker=(6, 2, 0), ms=2.4, mew=0.3),
    "tri": dict(marker="1", ms=2.6, mew=0.35),
}


def marks(ax, points, kind, step=0.05):
    """Fills a polygon with a grid of small black marks of a given kind."""
    xs, ys = [p[0] for p in points], [p[1] for p in points]
    if max(xs) - min(xs) < EPS or max(ys) - min(ys) < EPS:
        return
    clip = Polygon(points, closed=True, fc="none", ec="none")
    ax.add_patch(clip)
    grid = [(step * (u + 0.5 * (v % 2)), step * v * 0.866) for u in range(-2, 40) for v in range(-2, 40)]
    inside = [g for g in grid if min(xs) < g[0] < max(xs) and min(ys) < g[1] < max(ys)]
    (line,) = ax.plot([g[0] for g in inside], [g[1] for g in inside], ls="none", color="k", zorder=3.5, **MARKS[kind])
    line.set_clip_path(clip)


def frame(ax, width=1.0, height=1.0, pad=0.05):
    """Prepares axes for a main rectangle."""
    ax.add_patch(Rectangle((0, 0), width, height, fc="none", ec="k", lw=0.6, zorder=5))
    ax.set_xlim(-pad, width + pad)
    ax.set_ylim(-pad, height + pad)
    ax.set_aspect("equal")
    ax.axis("off")


def strips(ax, tiers, right=1.0, **style):
    """Fills the strips of a staircase."""
    for t in tiers:
        if t.wall > 0 and right - t.ax > 0:
            ax.add_patch(Rectangle((t.ax, t.ay), right - t.ax, t.wall, **style))


def coloured(ax, tiles, colours, **style):
    """Draws tiles in given colours."""
    for (x, y, w, h), c in zip(tiles, colours):
        ax.add_patch(Rectangle((x, y), w, h, fc=c, ec="k", lw=0.35, **style))


def region_figure(path, value, wit):
    """Draws, for one placement of each fit of a listed tiling, the strip of its tier divided into the tile and the parts above it and to its right."""
    tiles, sts = stages(value, wit)
    moves = moves_of(wit)
    picks = sorted((max((k for k, (_, f, _) in enumerate(moves) if f == fit), key=lambda k: min(tiles[k][2], tiles[k][3])), fit) for fit in CODES.values())
    fig, axes = plt.subplots(1, 4, figsize=(6.8, 2.05))
    notes = []
    for ax, (k, fit) in zip(axes, picks):
        i = moves[k][0]
        t = sts[k][i]
        x, y, w, h = tiles[k]
        draw(ax, tiles[: k + 1])
        marks(ax, box(x, y + h, 1 - x, t.wall - h), "dot")
        if 1 - x - w > EPS:
            u = next(v for v in sts[k + 1] if v.ax <= x + w + EPS and v.ay <= y + EPS and y + h <= v.ay + v.wall + EPS and v.ax >= x + w - EPS)
            marks(ax, box(u.ax, u.ay, 1 - u.ax, u.wall), "plus")
        for u in sts[k + 1]:
            ax.plot([u.ax, 1], [u.ay + u.wall, u.ay + u.wall], color="0.35", lw=0.5, ls=(0, (3, 2)), zorder=4)
        ax.add_patch(Rectangle((t.ax, t.ay), 1 - t.ax, t.wall, fc="none", ec="k", lw=1.2, zorder=4))
        ax.text(x + w / 2, y + h / 2, "$T$", fontsize=7, ha="center", va="center", zorder=6)
        if t.wall - h > 0.05:
            ax.text((x + 1) / 2, y + h + (t.wall - h) / 2, "$A$", fontsize=7, ha="center", va="center", zorder=6, bbox=dict(fc="w", ec="none", pad=1))
        if 1 - x - w > 0.05:
            ax.text((x + w + 1) / 2, y + h / 2, "$B$", fontsize=7, ha="center", va="center", zorder=6, bbox=dict(fc="w", ec="none", pad=1))
        merged = fit in ("full-width", "full") and i + 1 < len(sts[k])
        mark_anchors(ax, [Tier(u.ax, u.ay, u.floor, u.wall) for u in sts[k + 1]], size=3.6)
        frame(ax)
        ax.set_title(f"placement {k + 1}: {FIT_NAMES[fit]}", fontsize=7, pad=3)
        notes.append((k + 1, fit, i, merged))
    fig.tight_layout(pad=0.2, w_pad=0.5)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return notes


def misfit_figure(path, value, wit, k, i):
    """Draws, on a staircase of a listed tiling, a tile of full height that is wider than its floor and a tile of full width that is higher than its wall."""
    tiles, sts = stages(value, wit)
    tiers = sts[k]
    x = float(value)
    cases = (("inside", False, "inside, wider than the floor"), ("full-width", True, "full width, higher than the wall"))
    fig, axes = plt.subplots(1, 2, figsize=(4.4, 2.3))
    notes = []
    for ax, (fit, tall, title) in zip(axes, cases):
        t = tiers[i]
        after, tile = fplace(tiers, i, fit, tall, (t.floor + 0.5 * (1 - t.ax - t.floor)) / x, x)
        a, b, w, h = tile
        assert (w > t.floor + 0.02 and h < t.wall - 0.02) if fit == "inside" else (h > t.wall + 0.02)
        draw(ax, tiles[:k])
        ax.add_patch(Rectangle((a, b), w, h, fc=COLOURS[k % len(COLOURS)], ec="k", lw=0.5, zorder=3))
        for u in after:
            ax.plot([u.ax, 1], [u.ay + u.wall, u.ay + u.wall], color="0.35", lw=0.5, ls=(0, (3, 2)), zorder=4)
        for u in tiers:
            ax.plot([u.ax, u.ax + u.floor], [u.ay, u.ay], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
            ax.plot([u.ax, u.ax], [u.ay, u.ay + u.wall], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
        mark_anchors(ax, after, size=4.2, flags=True)
        for j, u in enumerate(after):
            ax.text(u.ax + 0.02, u.ay - 0.02, f"$T_{j}$", fontsize=6.5, ha="left", va="top", zorder=7)
        frame(ax)
        ax.set_title(title, fontsize=7, pad=3)
        notes.append((fit, [(round(u.floor, 4), round(u.wall, 4)) for u in after]))
    fig.tight_layout(pad=0.2, w_pad=0.8)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return notes


def skeleton(ax, tiers, defect=None, kind=None):
    """Draws the floors and the walls of a real staircase, a defective floor or wall being thick and dashed."""
    for j, t in enumerate(tiers):
        for part, (xs, ys) in (("floor", ([t.ax, t.ax + t.floor], [t.ay, t.ay])), ("wall", ([t.ax, t.ax], [t.ay, t.ay + t.wall]))):
            bad = j == defect and part == kind
            ax.plot(xs, ys, color="red" if bad else "k", lw=2.2 if bad else 0.9, ls=(0, (1.6, 1)) if bad else "-", solid_capstyle="butt", zorder=5 if bad else 4)


def defect_tier(tiers, kind):
    """Returns the index of the tier that makes a staircase defective, or None."""
    if kind == "floor":
        return next((j for j, t in enumerate(tiers) if t.floor <= 0 and (t.started or j == len(tiers) - 1)), None)
    return next((j for j, t in enumerate(tiers) if t.wall <= 0 and all(u.stale for u in tiers[:j])), None)


def defect_figure(path):
    """Draws a staircase that becomes floor-defective, and one that becomes wall-defective, with allowed placements after which the defect remains."""
    x = 1.5
    start = [Tier(0.0, 0.0, 1.0, 1.0)]
    s1, a = fplace(start, 0, "inside", False, 0.3, x)
    s2, b = fplace(s1, 1, "inside", False, 0.12, x)
    rows = (
        ("floor", ("full-height", False), (("at $T_0$", 0, "inside", False, 0.2), ("at $T_1$", 1, "full-height", True, None), ("at $T_2$", 2, "inside", False, 0.06))),
        ("wall", ("full-width", True), (("at $T_1$", 1, "full-width", False, None), ("at $T_2$", 2, "full-height", True, None))),
    )
    fig, axes = plt.subplots(2, 5, figsize=(6.9, 3.05))
    notes = []
    for row, (kind, (fit, tall), nexts) in zip(axes, rows):
        s3, c = fplace(s2, 1, fit, tall, None, x)
        j = defect_tier(s3, kind)
        assert defect_tier(s2, kind) is None and j == 1
        panels = [(s2, [a, b], None, "before"), (s3, [a, b, c], None, f"the tile does not fit: $T_1$ has a {kind} $< 0$")]
        for label, i, f, o, side in nexts:
            low = f in ("inside", "full-width")
            assert not s3[i].stale and not (not low and i > 0 and s3[i - 1].started)
            s4, d = fplace(s3, i, f, o, side, x)
            assert d[2] > 0 and d[3] > 0 and defect_tier(s4, kind) is not None
            panels.append((s4, [a, b, c, d], defect_tier(s4, kind), f"then a tile {label}"))
        for ax in row:
            ax.axis("off")
        for ax, (tiers, tiles, _, title) in zip(row, panels):
            coloured(ax, tiles, COLOURS, zorder=2)
            jd = defect_tier(tiers, kind)
            skeleton(ax, tiers, jd, kind)
            mark_anchors(ax, tiers, size=3.8, flags=True)
            for m, t in enumerate(tiers):
                ax.text(t.ax + 0.02, t.ay + 0.02, f"$T_{m}$", fontsize=5.5, ha="left", va="bottom", zorder=7)
            frame(ax)
            ax.set_title(title, fontsize=5.6, pad=2)
            notes.append((kind, title, [(round(t.floor, 3), round(t.wall, 3), t.stale, t.started) for t in tiers]))
    fig.tight_layout(pad=0.2, w_pad=0.4, h_pad=0.8)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return notes


def unfit_figure(path):
    """Draws a record on the unit square in which the positivity constraints of the first two placements hold and the second tile is wider than its floor."""
    x = 1.5
    s0 = [Tier(0.0, 0.0, 1.0, 1.0)]
    s1, a = fplace(s0, 0, "inside", False, 0.5, x)
    assert not s1[0].started
    s2, b = fplace(s1, 1, "full-height", True, None, x)
    assert b[2] > s1[1].floor and b[3] > 0 and s2[1].floor < 0 and s2[1].started
    fig, axes = plt.subplots(1, 2, figsize=(3.4, 1.75))
    for ax, tiles, tiers, title in zip(axes, ([a], [a, b]), (s1, s2), ("inside, wide", "full height, tall, at $T_1$")):
        coloured(ax, tiles, COLOURS, zorder=2)
        skeleton(ax, tiers, defect_tier(tiers, "floor"), "floor")
        mark_anchors(ax, tiers, size=4.2, flags=True)
        for m, t in enumerate(tiers):
            ax.text(t.ax + 0.02, t.ay + 0.02, f"$T_{m}$", fontsize=6.5, ha="left", va="bottom", zorder=7)
        frame(ax)
        ax.set_xlim(-0.05, 1.15)
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return a, b, s2[1].floor


def regions_figure(path, value, wit):
    """Draws the regions of the staircases along the record of a listed tiling."""
    tiles, sts = stages(value, wit)
    fig, axes = plt.subplots(1, len(sts), figsize=(6.9, 1.4))
    for k, (ax, tiers) in enumerate(zip(axes, sts)):
        draw(ax, tiles[:k])
        if tiers:
            top = tiers[0].ay + tiers[0].wall
            points = [(tiers[0].ax, top)]
            for j, t in enumerate(tiers):
                points += [(t.ax, t.ay), (tiers[j + 1].ax if j + 1 < len(tiers) else 1.0, t.ay)]
            points.append((1.0, top))
            ax.add_patch(Polygon(points, closed=True, fc="none", ec="k", lw=1.5, joinstyle="miter", zorder=6))
        ax.set_title(f"$U(S_{k})$" + (r"$ = \emptyset$" if k == len(sts) - 1 else ""), fontsize=6.5, pad=2)
    fig.tight_layout(pad=0.15, w_pad=0.3)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def tiling_map(tiles):
    """Returns the permutations and the root of the map of a tiling of the unit square, the darts being pairs of a side and the index of a tile, or None for the additional edge."""
    n = len(tiles)

    def at(corner, point):
        return next((j for j in range(n) if abs(corner(tiles[j])[0] - point[0]) < EPS and abs(corner(tiles[j])[1] - point[1]) < EPS), None)

    top_left = lambda t: (t[0], t[1] + t[3])
    bottom_right = lambda t: (t[0] + t[2], t[1])
    sigma = {}
    for k, (x, y, w, h) in enumerate(tiles):
        p = (x + w, y + h)
        j, m = at(top_left, p), at(bottom_right, p)
        sigma[("u", k)] = ("u", j) if j is not None else ("l", m) if m is not None else ("u", None)
        p = (x, y)
        j, m = at(bottom_right, p), at(top_left, p)
        sigma[("l", k)] = ("l", j) if j is not None else ("u", m) if m is not None else ("l", None)
    sigma[("u", None)] = ("u", at(top_left, (0, 1)))
    sigma[("l", None)] = ("l", at(bottom_right, (1, 0)))
    assert sorted(sigma.values(), key=str) == sorted(sigma, key=str)
    alpha = {(s, k): ("l" if s == "u" else "u", k) for s, k in sigma}
    return sigma, alpha, ("l", None)


def orbits(perm):
    """Returns the orbits of a permutation."""
    seen, out = set(), []
    for d in perm:
        if d not in seen:
            orbit = [d]
            while perm[orbit[-1]] != d:
                orbit.append(perm[orbit[-1]])
            seen.update(orbit)
            out.append(orbit)
    return out


def canonical(sigma, alpha, root):
    """Returns a form of a connected rooted map that is the same for isomorphic rooted maps, and the order in which it lists the darts."""
    index, queue = {root: 0}, [root]
    for d in queue:
        for e in (sigma[d], alpha[d]):
            if e not in index:
                index[e] = len(index)
                queue.append(e)
    assert len(index) == len(sigma)
    return tuple((index[sigma[d]], index[alpha[d]]) for d in queue), queue


def segments(tiles):
    """Returns the maximal segments of the union of the horizontal sides of the tiles, as triples of the two ends and the level."""
    out = []
    for y in sorted({round(v, 9) for _, b, _, h in tiles for v in (b, b + h)}):
        spans = sorted((x, x + w) for x, b, w, h in tiles if abs(b - y) < EPS or abs(b + h - y) < EPS)
        start, end = spans[0]
        for a, b in spans[1:]:
            if a <= end + EPS:
                end = max(end, b)
            else:
                out.append((start, end, y))
                start, end = a, b
        out.append((start, end, y))
    return out


def map_choice():
    """Selects the listed tiling without crossings in which two maximal horizontal segments are at the same level, with as few tiles as possible and, amongst those, with the largest smallest tile."""
    for n in range(4, 8):
        best = None
        for value, wit in listing(n):
            tiles = witness_tiles(value, wit)
            segs = segments(tiles)
            if len(segs) == len({s[2] for s in segs}) or crossings(tiles) or float(value) < 1.05:
                continue
            score = min(min(w, h) for _, _, w, h in tiles)
            if best is None or score > best[0]:
                best = (score, value, wit)
        if best:
            return best[1], best[2]


def arc(ax, a, b, bend, **style):
    """Draws a curved arrow between two points."""
    ax.annotate("", xy=b, xytext=a, arrowprops=dict(arrowstyle="-|>", shrinkA=3, shrinkB=3, mutation_scale=6, connectionstyle=f"arc3,rad={bend:.3f}", **style))


def through(ax, a, b, c, **style):
    """Draws an arrow between two points along the parabola that passes through a third point halfway."""
    control = (2 * c[0] - (a[0] + b[0]) / 2, 2 * c[1] - (a[1] + b[1]) / 2)
    curve = MplPath([a, control, b], [MplPath.MOVETO, MplPath.CURVE3, MplPath.CURVE3])
    ax.add_patch(FancyArrowPatch(path=curve, arrowstyle="-|>", mutation_scale=6, shrinkA=3, shrinkB=3, **style))


def map_figure(path, value, wit):
    """Draws a listed tiling, its map with the additional edge and the root, and its network of the levels."""
    tiles = witness_tiles(value, wit)
    n = len(tiles)
    sigma, alpha, root = tiling_map(tiles)
    vertices = orbits(sigma)
    faces = orbits({d: sigma[alpha[d]] for d in sigma})
    assert len(vertices) + len(faces) == n + 1 + 2
    segs = segments(tiles)
    level = lambda d: 1.0 if d == ("u", None) else 0.0 if d == ("l", None) else tiles[d[1]][1] + (tiles[d[1]][3] if d[0] == "u" else 0)
    centre = lambda d: tiles[d[1]][0] + tiles[d[1]][2] / 2

    def seg_of(orbit):
        y = level(orbit[0])
        assert all(abs(level(d) - y) < EPS for d in orbit)
        xs = [centre(d) for d in orbit if d[1] is not None]
        return next(s for s in segs if abs(s[2] - y) < EPS and s[0] - EPS <= min(xs) and max(xs) <= s[1] + EPS)

    where = {}
    for orbit in vertices:
        s = seg_of(orbit)
        for d in orbit:
            where[d] = s
    assert len(set(where.values())) == len(vertices) == len(segs)
    inner = sorted((s for s in segs if 0 < s[2] < 1 - EPS), key=lambda s: (s[2], s[0]))
    names = {s: f"v_{k + 1}" for k, s in enumerate(inner)}
    names.update({s: "t" for s in segs if s[2] < EPS})
    names.update({s: "s" for s in segs if s[2] > 1 - EPS})
    node = {s: ((s[0] + s[1]) / 2, s[2]) for s in segs}
    first = sigma_inverse(sigma)[root][1]
    assert same(tiles[first][:2], (0.0, 0.0), EPS)
    fig, (left, mid, right) = plt.subplots(1, 3, figsize=(6.9, 2.5), gridspec_kw=dict(width_ratios=[1.1, 1.45, 1.0]))
    draw(left, tiles)
    for s in segs:
        left.plot([s[0], s[1]], [s[2], s[2]], color="k", lw=1.3, solid_capstyle="butt", zorder=3)
        side = s[1] > 1 - EPS and s[0] > EPS
        left.text(s[1] + 0.03 if side else s[0] - 0.03, s[2], f"${names[s]}$", fontsize=7, va="center", ha="left" if side else "right")
    for k, (x, y, w, h) in enumerate(tiles):
        left.text(x + w / 2, y + h / 2, "$x$" if h > w else "$1/x$", fontsize=6.5, ha="center", va="center")
    left.set_xlim(-0.16, 1.16)
    row = [s for s in inner if s[2] < max(v[2] for v in inner) - EPS]
    spot = dict(node)
    if row and all(where[("l", k)] in row or where[("u", k)] in row or where[("u", k)] not in inner or where[("l", k)] not in inner for k in range(n)):
        height = max(s[2] for s in row)
        for j, s in enumerate(sorted(row, key=lambda s: s[0] + s[1])):
            spot[s] = (0.12 + 0.86 * j / max(len(row) - 1, 1), height)
    pairs = [(where[("u", k)], where[("l", k)]) for k in range(n)]
    for k, (x, y, w, h) in enumerate(tiles):
        a, b = spot[pairs[k][0]], spot[pairs[k][1]]
        if pairs.count(pairs[k]) == 1:
            arc(mid, a, b, 0.0, color=COLOURS[k % len(COLOURS)], lw=2.4 if k == first else 1.2)
        else:
            through(mid, a, b, (x + w / 2, y + h / 2), color=COLOURS[k % len(COLOURS)], lw=2.4 if k == first else 1.2)
    (sx, sy), (tx, ty), reach = spot[where[("u", None)]], spot[where[root]], 1.15
    curve = MplPath([(sx + 0.03, sy), (sx + reach, sy), (tx + reach, ty), (tx + 0.03, ty)], [MplPath.MOVETO, MplPath.CURVE4, MplPath.CURVE4, MplPath.CURVE4])
    mid.add_patch(FancyArrowPatch(path=curve, arrowstyle="-", color="k", lw=0.7, ls="--"))
    mid.text(sx + 0.75 * reach + 0.03, 0.5, "$e_0$", fontsize=7, va="center", ha="left")
    node = spot
    for s, (x, y) in node.items():
        mid.plot([x], [y], marker="o", mfc="w", mec="k", ms=4, zorder=3)
        mid.text(x - 0.06, y, f"${names[s]}$", fontsize=7, va="center", ha="right")
    mid.set_xlim(-0.2, 1.6)
    mid.set_ylim(-0.1, 1.07)
    mid.set_aspect("equal")
    mid.axis("off")
    levels = sorted({s[2] for s in segs})
    for k, (x, y, w, h) in enumerate(tiles):
        ends = [(round(t[1] + t[3], 9), round(t[1], 9)) for t in tiles]
        bend = 0.0 if ends.count(ends[k]) == 1 and not any(ends[k][1] < v < ends[k][0] for v in {c for e in ends for c in e}) else -1.3 * (x + w / 2 - 0.5) / max(h, 0.3)
        arc(right, (0.5, y + h), (0.5, y), bend, color=COLOURS[k % len(COLOURS)], lw=1.2)
    for v in levels:
        right.plot([0.5], [v], marker="o", mfc="w", mec="k", ms=4, zorder=3)
        label = "s = 1" if v > 1 - EPS else "t = 0" if v < EPS else f"{v:.3f}"
        right.text(-0.05, v, f"${label}$", fontsize=6.5, va="center", ha="right")
        right.plot([-0.03, 0.47], [v, v], color="0.6", lw=0.4, ls=(0, (1, 2)), zorder=1)
    right.set_xlim(-0.35, 1.05)
    right.set_ylim(-0.1, 1.07)
    right.set_aspect("equal")
    right.axis("off")
    for ax, title in zip((left, mid, right), ("the tiling", "its map, with the edge $e_0$", "its network of the levels")):
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.3)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return len(vertices), len(faces), len(levels), first


def sigma_inverse(sigma):
    """Returns the inverse of a permutation."""
    return {v: k for k, v in sigma.items()}


def orientation_vector(tiles, sigma, alpha, root):
    """Returns the orientations of the tiles of a tiling in the order in which the canonical form of its map lists their edges."""
    form, queue = canonical(sigma, alpha, root)
    seen, out = set(), []
    for d in queue:
        if d[1] is not None and d[1] not in seen:
            seen.add(d[1])
            out.append("T" if tiles[d[1]][3] > tiles[d[1]][2] + EPS else "W")
    return form, "".join(out)


def isomorphic_choice():
    """Selects listed tilings of different proportions whose rooted maps are isomorphic, without small tiles, with as few tiles as possible."""
    for n in (3, 4, 5):
        groups = {}
        for value, wit in listing(n):
            tiles = witness_tiles(value, wit)
            if float(value) < 1.05 or min(min(w, h) for _, _, w, h in tiles) < 0.1:
                continue
            form, vector = orientation_vector(tiles, *tiling_map(tiles))
            groups.setdefault(form, {}).setdefault(vector, (value, wit))
        best = max(groups.values(), key=len)
        if len(best) >= 2:
            return list(best.items())[:3]


def isomorphic_figure(path, choice):
    """Draws listed tilings of different proportions whose rooted maps are isomorphic, with the orientations of their tiles."""
    fig, axes = plt.subplots(1, len(choice), figsize=(1.75 * len(choice), 1.95))
    for ax, (vector, (value, wit)) in zip(axes, choice):
        tiles = witness_tiles(value, wit)
        draw(ax, tiles)
        for x, y, w, h in tiles:
            ax.text(x + w / 2, y + h / 2, "$x$" if h > w else "$1/x$", fontsize=6.5, ha="center", va="center")
        ax.set_title(f"$x = {float(value):.4f}$", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def bag_choice():
    """Selects two classes of tilings listed by the search that have the same bag, with as few tiles as possible."""
    for n in (4, 5):
        seen = {}
        for value, size, wit in classes(n):
            if float(value) < 1.05:
                continue
            tiles = witness_tiles(value, wit)
            bag = (value, tuple(sorted(round(min(w, h), 7) for _, _, w, h in tiles)))
            if bag in seen and min(min(w, h) for _, _, w, h in tiles) > 0.1:
                return seen[bag], (value, size, wit)
            seen.setdefault(bag, (value, size, wit))


def orbit_of(tiles):
    """Returns the distinct images of a tiling of the unit square under the eight symmetries of the square."""
    out = []
    current = list(tiles)
    for flip in range(2):
        for _ in range(4):
            current = [(1 - y - h, x, h, w) for x, y, w, h in current]
            if not any(all(any(same(t, g) for g in other) for t in current) for other in out):
                out.append(current)
        current = [(y, x, h, w) for x, y, w, h in current]
    return out


def same_bag_figure(path, choice):
    """Draws all the tilings of two classes that have the same bag, each from its record, the tiles of equal short side having the same colour."""
    orbits_ = [orbit_of(witness_tiles(value, wit)) for value, _, wit in choice]
    assert [len(o) for o in orbits_] == [size for _, size, _ in choice]
    sides = sorted({round(min(w, h), 7) for _, _, w, h in orbits_[0][0]})
    columns = max(len(o) for o in orbits_)
    fig, axes = plt.subplots(2, columns, figsize=(0.82 * columns, 1.75), squeeze=False)
    records = []
    for row, orbit, (value, size, _) in zip(axes, orbits_, choice):
        for ax in row:
            ax.axis("off")
        for ax, image in zip(row, orbit):
            record = witness(build(image)[1])
            tiles = witness_tiles(value, record)
            assert len(tiles) == len(image) and all(any(same(t, g) for g in image) for t in tiles)
            coloured(ax, tiles, [COLOURS[sides.index(round(min(w, h), 7))] for _, _, w, h in tiles])
            frame(ax)
            records.append(record)
    assert len(set(records)) == len(records)
    fig.tight_layout(pad=0.2, w_pad=0.3, h_pad=0.5)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return sides, records


def crossing_choice():
    """Selects a class of tilings listed by the search, of proportion larger than one, with exactly one crossing."""
    for n in (4, 5):
        for value, size, wit in classes(n):
            tiles = witness_tiles(value, wit)
            if float(value) > 1.05 and len(crossings(tiles)) == 1 and min(min(w, h) for _, _, w, h in tiles) > 0.1:
                return value, wit


def numbered(ax, tiles, ids, upto, total, fontsize=6.5):
    """Draws the tiles placed so far in the colours of their identities, numbered in the order of placement, and outlines the others."""
    for k, t in enumerate(tiles[:upto]):
        ax.add_patch(Rectangle(t[:2], t[2], t[3], fc=COLOURS[ids[k] % len(COLOURS)], ec="k", lw=0.35))
        ax.text(t[0] + t[2] / 2, t[1] + t[3] / 2, str(k + 1), fontsize=fontsize, ha="center", va="center")
    outline_rest(ax, tiles[upto:])
    frame(ax)


def crossing_figure(path, value, wit):
    """Draws the two records of a listed tiling with one crossing, one staircase after another, numbering the tiles in the order of placement."""
    base = witness_tiles(value, wit)
    (q,) = crossings(base)
    rows = []
    for chosen in ((), (q,)):
        order, moves, sts = build(base, chosen)
        drawn = witness_tiles(value, witness(moves))
        assert all(same(t, g) for t, g in zip(drawn, order))
        rows.append((drawn, [next(j for j, g in enumerate(base) if same(t, g)) for t in drawn], sts, moves))
    n = len(base)
    fig, axes = plt.subplots(2, n, figsize=(6.2, 2.75))
    for row, (drawn, ids, sts, moves), label in zip(axes, rows, ("$X = \\emptyset$", "$X = \\{q\\}$")):
        for k, ax in enumerate(row):
            numbered(ax, drawn, ids, k + 1, n)
            mark_anchors(ax, sts[k + 1], size=3.4, flags=True)
            ax.plot([q[0]], [q[1]], marker="D", mfc="w", mec="k", ms=3.4, zorder=8)
        row[0].text(-0.12, 0.5, label, fontsize=7, rotation=90, ha="right", va="center")
    fig.tight_layout(pad=0.2, w_pad=0.3, h_pad=0.6)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    lower = next(j for j, t in enumerate(base) if abs(t[0] - q[0]) < EPS and abs(t[1] + t[3] - q[1]) < EPS)
    upper = next(j for j, t in enumerate(base) if abs(t[0] + t[2] - q[0]) < EPS and abs(t[1] - q[1]) < EPS)
    return q, [witness(m) for _, _, _, m in rows], [(ids.index(upper) + 1, ids.index(lower) + 1) for _, ids, _, _ in rows]


def grid_tiling(columns, rows):
    """Returns the tiling of the unit square by a grid of congruent rectangles, with exact coordinates."""
    return [(sp.Rational(u, columns), sp.Rational(v, rows), sp.Rational(1, columns), sp.Rational(1, rows)) for v in range(rows) for u in range(columns)]


def subsets_figure(path):
    """Draws the four records of the tiling of the square by a grid of two by three rectangles, numbering the tiles in the order of placement."""
    exact = grid_tiling(2, 3)
    base = [tuple(float(c) for c in t) for t in exact]
    qs = crossings(base)
    assert len(qs) == 2
    fig, axes = plt.subplots(1, 4, figsize=(5.6, 1.6))
    records = []
    for ax, chosen, label in zip(axes, ((), (qs[0],), (qs[1],), tuple(qs)), ("\\emptyset", "\\{q_1\\}", "\\{q_2\\}", "\\{q_1, q_2\\}")):
        drawn, moves, _ = regenerate(exact, sp.Rational(3, 2), chosen)
        ids = [next(j for j, g in enumerate(base) if same(t, g)) for t in drawn]
        numbered(ax, drawn, ids, len(drawn), len(drawn))
        for name, q in zip(("q_1", "q_2"), qs):
            ax.plot([q[0]], [q[1]], marker="D", mfc="k" if q in chosen else "w", mec="k", ms=3.6, zorder=8)
        ax.set_title(f"$X = {label}$", fontsize=7, pad=3)
        records.append(witness(moves))
    assert len(set(records)) == 4
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return qs, records


def quarter_turn_tiling():
    """Returns a tiling of the unit square by eight rectangles of proportion two that is fixed by a quarter turn, with exact coordinates."""
    half, quarter = sp.Rational(1, 2), sp.Rational(1, 4)
    out = [(0, 0, half, quarter), (0, quarter, half, quarter)]
    for _ in range(3):
        out += [(1 - y - h, x, h, w) for x, y, w, h in out[-2:]]
    return out


def symmetric_figure(path, value, wit):
    """Draws a listed tiling beside its transpose, its corner tile with the image of that tile under the reflection in the diagonal, and a tiling fixed by a quarter turn."""
    tiles = witness_tiles(value, wit)
    moves = moves_of(wit)
    flipped = witness(build([(y, x, h, w) for x, y, w, h in tiles])[1])
    transposed = witness_tiles(value, flipped)
    assert all(any(same(t, (y, x, h, w)) for x, y, w, h in tiles) for t in transposed)
    ids = [next(j for j, (x, y, w, h) in enumerate(tiles) if same(t, (y, x, h, w))) for t in transposed]
    turned, _, _ = regenerate(quarter_turn_tiling(), 2)
    assert all(any(same(t, (1 - y - h, x, h, w)) for x, y, w, h in turned) for t in turned)
    fig, axes = plt.subplots(1, 3, figsize=(5.0, 1.85))
    draw(axes[0], tiles)
    coloured(axes[1], transposed, [COLOURS[j] for j in ids])
    frame(axes[1])
    orbit = [turned[0]]
    for _ in range(3):
        x, y, w, h = orbit[-1]
        orbit.append(next(t for t in turned if same(t, (1 - y - h, x, h, w))))
    coloured(axes[2], turned, [COLOURS[1] if any(same(t, g) for g in orbit) else "w" for t in turned])
    axes[2].plot([0.5], [0.5], marker="D", mfc="w", mec="k", ms=3.8, zorder=8)
    frame(axes[2])
    for ax, title in zip(axes, ("a tiling", "its transpose", "fixed by a quarter turn")):
        ax.set_title(title, fontsize=6.5, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return flipped, len(crossings(turned))


def bags_figure(path):
    """Draws the tiling of the square by a wide tile above two congruent ones, and the two tilings with three more tiles obtained by cutting a tile of each size into four, with the short sides of their tiles."""
    half, third = sp.Rational(1, 2), sp.Rational(1, 3)
    base = [(0, 0, half, third), (half, 0, half, third), (0, third, 1, 2 * third)]
    cut = lambda t: [(t[0] + t[2] * u / 2, t[1] + t[3] * v / 2, t[2] / 2, t[3] / 2) for v in range(2) for u in range(2)]
    cases = (base, base[:2] + cut(base[2]), [base[1], base[2]] + cut(base[0]))
    fig, axes = plt.subplots(1, 3, figsize=(4.8, 2.0))
    bags = []
    for ax, exact in zip(axes, cases):
        drawn, _, _ = regenerate(exact, sp.Rational(3, 2))
        sides = sorted((min(sp.Rational(t[2]), sp.Rational(t[3])) for t in exact), reverse=True)
        kinds = sorted(set(sp.Rational(1, d) for d in (3, 6, 12)) | {2 * third}, reverse=True)
        coloured(ax, drawn, [COLOURS[kinds.index(sp.nsimplify(min(t[2], t[3]), rational=True, tolerance=1e-9))] for t in drawn])
        frame(ax)
        ax.set_title(", ".join(f"${s.p}/{s.q}$" for s in sides), fontsize=6.5, pad=3)
        bags.append(tuple(sides))
    assert bags[1] != bags[2] and len(bags[1]) == len(bags[2]) == 6
    fig.tight_layout(pad=0.2, w_pad=0.8)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return bags


def main():
    """Generates the diagrams and prints the facts on which their captions rely."""
    value, wit, k = base_tiling()
    print("region:", region_figure(OUT / "region.svg", value, wit))
    print("misfit:", misfit_figure(OUT / "misfit.svg", value, wit, 3, 1))
    for note in defect_figure(OUT / "defect.svg"):
        print("defect:", note)
    print("unfit:", unfit_figure(OUT / "unfit.svg"))
    cvalue, cwit = construction_choice()
    regions_figure(OUT / "regions.svg", cvalue, cwit)
    mvalue, mwit = map_choice()
    print("map:", mvalue, mwit, map_figure(OUT / "tiling-map.svg", mvalue, mwit))
    choice = isomorphic_choice()
    print("isomorphic:", choice)
    isomorphic_figure(OUT / "isomorphic.svg", choice)
    choice = bag_choice()
    print("same bag:", choice, same_bag_figure(OUT / "same-bag.svg", choice))
    xvalue, xwit = crossing_choice()
    print("crossing:", xvalue, xwit, crossing_figure(OUT / "crossing.svg", xvalue, xwit))
    print("subsets:", subsets_figure(OUT / "crossing-subsets.svg"))
    print("symmetric:", symmetric_figure(OUT / "symmetric.svg", cvalue, cwit))
    print("bags:", bags_figure(OUT / "bags.svg"))


if __name__ == "__main__":
    main()
