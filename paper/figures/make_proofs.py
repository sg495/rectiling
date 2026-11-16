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

TINT_A = "#cfe8f7"
TINT_B = "#fde3b0"
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
        coloured(ax, tiles[:k], ["0.9"] * k)
        ax.add_patch(Rectangle((x, y + h), 1 - x, t.wall - h, fc=TINT_A, ec="none", zorder=1))
        ax.add_patch(Rectangle((x + w, y), 1 - x - w, h, fc=TINT_B, ec="none", zorder=1))
        ax.add_patch(Rectangle((x, y), w, h, fc=COLOURS[k % len(COLOURS)], ec="k", lw=0.5, zorder=3))
        for u in sts[k + 1]:
            ax.plot([u.ax, 1], [u.ay + u.wall, u.ay + u.wall], color="0.35", lw=0.5, ls=(0, (3, 2)), zorder=4)
        ax.add_patch(Rectangle((t.ax, t.ay), 1 - t.ax, t.wall, fc="none", ec="k", lw=1.2, zorder=4))
        ax.text(x + w / 2, y + h / 2, "$T$", fontsize=7, ha="center", va="center", zorder=6)
        if t.wall - h > 0.05:
            ax.text((x + 1) / 2, y + h + (t.wall - h) / 2, "$A$", fontsize=7, ha="center", va="center", zorder=6)
        if 1 - x - w > 0.05:
            ax.text((x + w + 1) / 2, y + h / 2, "$B$", fontsize=7, ha="center", va="center", zorder=6)
        merged = fit in ("full-width", "full") and i + 1 < len(sts[k])
        if merged:
            u = sts[k + 1][i + (fit == "full-width")]
            ax.add_patch(Rectangle((u.ax, u.ay), 1 - u.ax, u.wall, fc="none", ec="k", lw=0.9, ls=(0, (1, 1.2)), zorder=5))
        mark_anchors(ax, [Tier(u.ax, u.ay, u.floor, u.wall) for u in sts[k + 1]], size=3.6)
        frame(ax)
        ax.set_title(f"placement {k + 1}: {FIT_NAMES[fit]}", fontsize=7, pad=3)
        notes.append((k + 1, fit, i, merged))
    fig.tight_layout(pad=0.2, w_pad=0.5)
    fig.savefig(path)
    plt.close(fig)
    return notes


def misfit_figure(path, value, wit, k, i):
    """Draws, on a staircase of a listed tiling, a tile of full height that is wider than its floor and a tile of full width that is higher than its wall."""
    tiles, sts = stages(value, wit)
    tiers = sts[k]
    x = float(value)
    cases = (("full-height", False, "full height, wider than the floor"), ("full-width", True, "full width, higher than the wall"))
    fig, axes = plt.subplots(1, 2, figsize=(4.4, 2.3))
    notes = []
    for ax, (fit, tall, title) in zip(axes, cases):
        after, tile = fplace(tiers, i, fit, tall, None, x)
        a, b, w, h = tile
        t = tiers[i]
        assert (w > t.floor + 0.02) if fit == "full-height" else (h > t.wall + 0.02)
        coloured(ax, tiles[:k], ["0.82"] * k)
        strips(ax, after, fc=TINT_A, ec="none", zorder=1)
        ax.add_patch(Rectangle((a, b), w, h, fc=COLOURS[0], ec="k", lw=0.5, hatch="///", alpha=0.8, zorder=3))
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
    fig.savefig(path)
    plt.close(fig)
    return notes


def skeleton(ax, tiers, defect=None, kind=None):
    """Draws the floors and the walls of a real staircase, a defective floor or wall being thick and dashed."""
    for j, t in enumerate(tiers):
        for part, (xs, ys) in (("floor", ([t.ax, t.ax + t.floor], [t.ay, t.ay])), ("wall", ([t.ax, t.ax], [t.ay, t.ay + t.wall]))):
            bad = j == defect and part == kind
            ax.plot(xs, ys, color="k", lw=2.2 if bad else 0.9, ls=(0, (1.6, 1)) if bad else "-", solid_capstyle="butt", zorder=5 if bad else 4)


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
    fig.savefig(path)
    plt.close(fig)
    return notes


def unfit_figure(path):
    """Draws the record of the worked example with a width of the main rectangle for which the second tile is wider than its floor."""
    x = float(sp.real_roots(sp.Poly(sp.Symbol("x") ** 3 - 2 * sp.Symbol("x") ** 2 + sp.Symbol("x") - 1))[-1])
    width = 0.36
    s0 = [Tier(0.0, 0.0, width, 1.0)]
    s1, a = fplace(s0, 0, "full-width", False, None, x)
    s2, b = fplace(s1, 0, "full-height", True, None, x)
    assert b[2] > s1[0].floor and s2[0].floor < 0 and s2[0].started
    fig, axes = plt.subplots(1, 3, figsize=(4.6, 2.5))
    for ax, tiles, tiers, title in zip(axes, ([a], [a, b], [a, b]), (s1, s2, s2), ("full width, wide", "full height, tall", "full: its floor is negative")):
        coloured(ax, tiles, COLOURS, zorder=2)
        skeleton(ax, tiers, 0 if tiers is s2 else None, "floor")
        mark_anchors(ax, tiers, size=4.2, flags=True)
        ax.add_patch(Rectangle((0, 0), width, 1, fc="none", ec="k", lw=0.6, zorder=5))
        ax.set_xlim(-0.08, 0.62)
        ax.set_ylim(-0.05, 1.05)
        ax.set_aspect("equal")
        ax.axis("off")
        ax.set_title(title, fontsize=6.5, pad=3)
    t = s2[0]
    axes[2].annotate("$L - w < 0$", (t.ax + t.floor / 2, t.ay), (0.52, 0.12), fontsize=6.5, ha="center", arrowprops=dict(arrowstyle="-", lw=0.4))
    axes[1].text(b[0] + b[2] / 2, b[1] + b[3] / 2, "$w > L$", fontsize=6.5, ha="center", va="center", rotation=90)
    fig.tight_layout(pad=0.2, w_pad=0.4)
    fig.savefig(path)
    plt.close(fig)
    return x, width, a, b, s2[0].floor


def regions_figure(path, value, wit):
    """Draws the regions of the staircases along the record of a listed tiling."""
    tiles, sts = stages(value, wit)
    fig, axes = plt.subplots(1, len(sts), figsize=(6.9, 1.4))
    for k, (ax, tiers) in enumerate(zip(axes, sts)):
        draw(ax, tiles[:k])
        strips(ax, tiers, fc="0.86", ec="none", hatch="////", zorder=1)
        for t in tiers:
            ax.add_patch(Rectangle((t.ax, t.ay), 1 - t.ax, t.wall, fc="none", ec="0.55", lw=0, hatch="////", zorder=1))
        ax.set_title(f"$U(S_{k})$" + (r"$ = \emptyset$" if k == len(sts) - 1 else ""), fontsize=6.5, pad=2)
    fig.tight_layout(pad=0.15, w_pad=0.3)
    fig.savefig(path)
    plt.close(fig)


def near_figure(path, value, wit, c, d):
    """Draws, for a point of a listed tiling, the tile that contains the points just above and to its right, and the tile that contains those just below and to its right."""
    tiles, _ = stages(value, wit)
    xs = sorted({round(v, 9) for x, _, w, _ in tiles for v in (x, x + w)})
    ys = sorted({round(v, 9) for _, y, _, h in tiles for v in (y, y + h)})
    eps = 0.45 * (min(v for v in xs if v > c + EPS) - c)
    up = 0.45 * (min(v for v in ys if v > d + EPS) - d)
    down = 0.45 * (d - max(v for v in ys if v < d - EPS))
    fig, axes = plt.subplots(1, 2, figsize=(4.2, 2.2))
    found = []
    for ax, (eta, title) in zip(axes, ((up, "just above and to the right"), (-down, "just below and to the right"))):
        p = (c + eps, d + eta)
        k = next(j for j, (x, y, w, h) in enumerate(tiles) if x < p[0] < x + w and y < p[1] < y + h)
        x, y, w, h = tiles[k]
        assert x <= c + EPS and c < x + w and ((y <= d + EPS and d < y + h) if eta > 0 else (y < d and d <= y + h + EPS))
        coloured(ax, tiles, ["w"] * len(tiles))
        ax.add_patch(Rectangle((x, y), w, h, fc=COLOURS[k], ec="k", lw=0.9, zorder=2))
        ax.add_patch(Rectangle((c, min(d, d + eta)), eps, abs(eta), fc="none", ec="k", lw=0.5, ls=(0, (1, 1)), zorder=5))
        ax.plot([c], [d], marker="o", mfc="k", mec="k", ms=3.2, zorder=6)
        ax.plot([p[0]], [p[1]], marker="x", color="k", ms=3.5, mew=0.7, zorder=6)
        ax.text(c - 0.02, d + (0.02 if eta > 0 else -0.02), "$(c, d)$", fontsize=6.5, ha="right", va="bottom" if eta > 0 else "top", zorder=7)
        frame(ax)
        ax.set_title(title, fontsize=7, pad=3)
        found.append(k)
    fig.tight_layout(pad=0.2, w_pad=0.8)
    fig.savefig(path)
    plt.close(fig)
    return found


def anchor_figure(path, value, wit, k, i):
    """Draws a state of the construction of a listed tiling, with the tile at the anchor of a tier and the parts of the plane next to the anchor that lie outside the region."""
    tiles, sts = stages(value, wit)
    tiers = sts[k]
    t = tiers[i]
    q = next(r for r in tiles[k:] if abs(r[0] - t.ax) < EPS and abs(r[1] - t.ay) < EPS)
    fig, ax = plt.subplots(figsize=(2.9, 2.9))
    draw(ax, tiles[:k])
    strips(ax, tiers, fc="0.93", ec="none", zorder=1)
    outline_rest(ax, tiles[k:])
    ax.add_patch(Rectangle((t.ax, t.ay), 1 - t.ax, t.wall, fc="none", ec="k", lw=1.1, zorder=4))
    w, h = min(q[2], t.floor), min(q[3], t.wall)
    ax.add_patch(Rectangle((t.ax, t.ay), w, h, fc="none", ec="k", lw=0, hatch="////", zorder=3))
    ax.add_patch(Rectangle((q[0], q[1]), q[2], q[3], fc="none", ec="k", lw=0.8, zorder=4))
    reach = 0.09
    ax.add_patch(Rectangle((t.ax - reach, t.ay), reach, t.wall, fc="none", ec="k", lw=0, hatch="xxxx", zorder=3))
    ax.add_patch(Rectangle((t.ax, t.ay - reach), t.floor, reach, fc="none", ec="k", lw=0, hatch="xxxx", zorder=3))
    ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=1.6, solid_capstyle="butt", zorder=5)
    ax.plot([t.ax, t.ax], [t.ay, t.ay + t.wall], color="k", lw=1.6, solid_capstyle="butt", zorder=5)
    mark_anchors(ax, tiers, size=4.6, flags=True)
    ax.text(t.ax + w / 2, t.ay + h / 2, "$T$", fontsize=8, ha="center", va="center", zorder=7, bbox=dict(fc="w", ec="none", pad=1))
    frame(ax)
    fig.tight_layout(pad=0.2)
    fig.savefig(path)
    plt.close(fig)
    return k, i, q


def impossible_figure(path, value, wit, k):
    """Draws, on a state of the construction of a listed tiling, the tile at the chosen anchor made wider than its floor and made higher than its wall, with the tile of the tiling that it would then meet."""
    tiles, sts = stages(value, wit)
    tiers = sts[k]
    i = next(j for j, t in enumerate(tiers) if not extends(tiles, t.ax + t.floor, t.ay))
    assert i == moves_of(wit)[k][0] and 0 < i < len(tiers) - 1
    t = tiers[i]
    q = tiles[k]
    extra = 0.1
    end = (t.ax + t.floor, t.ay)
    below = next(j for j, (x, y, w, h) in enumerate(tiles) if x <= end[0] + EPS and end[0] < x + w - EPS and y < end[1] - EPS and end[1] <= y + h + EPS)
    corner = (t.ax, t.ay + t.wall)
    above = next(j for j, (x, y, w, h) in enumerate(tiles) if abs(y + h - corner[1]) < EPS and x <= corner[0] + EPS and corner[0] < x + w - EPS)
    assert tiles[below][1] + tiles[below][3] > end[1] + EPS and above != k and q[3] < t.wall - EPS
    cases = (
        ((q[0], q[1], t.floor + extra, q[3]), below, end, "wider than the floor"),
        ((q[0], q[1], q[2], t.wall + extra), above, corner, "higher than the wall"),
    )
    fig, axes = plt.subplots(1, 2, figsize=(4.6, 2.4))
    for ax, (ghost, other, point, title) in zip(axes, cases):
        coloured(ax, tiles, ["w"] * len(tiles))
        x, y, w, h = tiles[other]
        ax.add_patch(Rectangle((x, y), w, h, fc=COLOURS[other], ec="k", lw=0.6, zorder=2))
        ax.add_patch(Rectangle(ghost[:2], ghost[2], ghost[3], fc="none", ec="k", lw=1.0, ls=(0, (3, 1.5)), hatch="////", zorder=3))
        for j, u in enumerate(tiers):
            ax.plot([u.ax, u.ax + u.floor], [u.ay, u.ay], color="k", lw=1.5, solid_capstyle="butt", zorder=4)
            if extends(tiles, u.ax + u.floor, u.ay):
                ax.plot([u.ax + u.floor, u.ax + u.floor + 0.09], [u.ay, u.ay], color="k", lw=1.5, ls=(0, (1, 1.2)), zorder=4)
        mark_anchors(ax, tiers, size=4.2, chosen=t, flags=True)
        ax.plot([point[0]], [point[1]], marker="D", mfc="w", mec="k", ms=3.6, zorder=7)
        ax.text(ghost[0] + ghost[2] / 2, ghost[1] + ghost[3] / 2, "$Q$", fontsize=8, ha="center", va="center", zorder=7, bbox=dict(fc="w", ec="none", pad=1))
        frame(ax)
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.8)
    fig.savefig(path)
    plt.close(fig)
    return k, i, below, above


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
    for k, (x, y, w, h) in enumerate(tiles):
        a, b = node[where[("u", k)]], node[where[("l", k)]]
        through(mid, a, b, (x + w / 2, y + h / 2), color=COLOURS[k % len(COLOURS)], lw=2.4 if k == first else 1.2)
    (sx, sy), (tx, ty), reach = node[where[("u", None)]], node[where[root]], 0.85
    curve = MplPath([(sx + 0.03, sy), (sx + reach, sy), (tx + reach, ty), (tx + 0.03, ty)], [MplPath.MOVETO, MplPath.CURVE4, MplPath.CURVE4, MplPath.CURVE4])
    mid.add_patch(FancyArrowPatch(path=curve, arrowstyle="-", color="k", lw=0.7, ls="--"))
    mid.text(sx + 0.75 * reach + 0.03, 0.5, "$e_0$", fontsize=7, va="center", ha="left")
    mid.annotate("", xy=(tx + 0.2, ty - 0.012), xytext=(tx + 0.03, ty), arrowprops=dict(arrowstyle="-|>", color="k", lw=1.6, mutation_scale=6, shrinkA=0, shrinkB=0))
    mid.text(tx + 0.13, ty - 0.035, "$r$", fontsize=7, ha="center", va="top")
    for s, (x, y) in node.items():
        mid.plot([x], [y], marker="o", mfc="w", mec="k", ms=4, zorder=3)
        mid.text(x - 0.06, y, f"${names[s]}$", fontsize=7, va="center", ha="right")
    mid.set_xlim(-0.2, 1.5)
    mid.set_ylim(-0.1, 1.07)
    mid.set_aspect("equal")
    mid.axis("off")
    levels = sorted({s[2] for s in segs})
    for k, (x, y, w, h) in enumerate(tiles):
        bend = -1.3 * (x + w / 2 - 0.5) / max(h, 0.3)
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
    for ax, title in zip((left, mid, right), ("the tiling", "its map, with $e_0$ and the root $r$", "its network of the levels")):
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.3)
    fig.savefig(path)
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
    fig.savefig(path)
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


def same_bag_figure(path, choice):
    """Draws tilings of two classes that have the same bag, the tiles of equal short side having the same colour."""
    fig, axes = plt.subplots(1, 2, figsize=(3.5, 1.85))
    sides = None
    for ax, (value, size, wit) in zip(axes, choice):
        tiles = witness_tiles(value, wit)
        if sides is None:
            sides = sorted({round(min(w, h), 7) for _, _, w, h in tiles})
        coloured(ax, tiles, [COLOURS[sides.index(round(min(w, h), 7))] for _, _, w, h in tiles])
        frame(ax)
        ax.set_title(f"a class of {size} tilings", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.8)
    fig.savefig(path)
    plt.close(fig)
    return sides


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
    fig.savefig(path)
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
    fig.savefig(path)
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
    fig, axes = plt.subplots(1, 4, figsize=(6.6, 1.85))
    draw(axes[0], tiles)
    coloured(axes[1], transposed, [COLOURS[j] for j in ids])
    frame(axes[1])
    corner = next(t for t in tiles if abs(t[0]) < EPS and abs(t[1]) < EPS)
    coloured(axes[2], tiles, ["w"] * len(tiles))
    x, y, w, h = corner
    axes[2].add_patch(Rectangle((x, y), w, h, fc=COLOURS[0], ec="k", lw=0.6, zorder=2))
    axes[2].add_patch(Rectangle((y, x), h, w, fc="none", ec="k", lw=0.9, ls=(0, (3, 1.5)), hatch="////", zorder=3))
    axes[2].plot([0, 1], [0, 1], color="k", lw=0.5, ls=(0, (1, 1.5)), zorder=4)
    frame(axes[2])
    orbit = [turned[0]]
    for _ in range(3):
        x, y, w, h = orbit[-1]
        orbit.append(next(t for t in turned if same(t, (1 - y - h, x, h, w))))
    coloured(axes[3], turned, [COLOURS[1] if any(same(t, g) for g in orbit) else "w" for t in turned])
    axes[3].plot([0.5], [0.5], marker="D", mfc="w", mec="k", ms=3.8, zorder=8)
    frame(axes[3])
    for ax, title in zip(axes, ("a tiling", "its transpose", "a corner tile and its reflection", "fixed by a quarter turn")):
        ax.set_title(title, fontsize=6.5, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
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
    fig.savefig(path)
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
    ctiles, csts = stages(cvalue, cwit)
    t = csts[2][0]
    print("near:", near_figure(OUT / "near.svg", cvalue, cwit, t.ax + t.floor, csts[3][1].ay))
    print("anchor:", anchor_figure(OUT / "anchor.svg", value, wit, 3, 1))
    print("impossible:", impossible_figure(OUT / "impossible.svg", cvalue, cwit, 2))
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
