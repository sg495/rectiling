# SPDX-License-Identifier: LGPL-3.0-or-later
"""Generates the explanatory diagrams of the paper.

Every diagram is drawn from tilings found by the search, read from the listings in the data folder, or from exact solutions of the system of a record; the tiles are drawn by the figure generator and the annotations are added on top.
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import sympy as sp
from matplotlib.patches import Rectangle

from make_figures import COLOURS, Tier, X, draw, place, replay, witness_tiles

OUT = Path(__file__).parent
DATA = OUT.parent / "data"
CODES = {"i": "inside", "h": "full-height", "w": "full-width", "f": "full"}
FIT_NAMES = {"inside": "inside", "full-height": "full height", "full-width": "full width", "full": "full"}
EPS = 1e-9


def listing(n):
    """Returns the proportions listed by the search for n tiles, as pairs of a value and a witness."""
    rows = [line.split("\t") for line in (DATA / f"tilings-{n}.tsv").read_text().splitlines()]
    return [(row[0], row[4]) for row in rows]


def moves_of(witness):
    """Decodes a witness into placements."""
    return [(int(m[0]), CODES[m[1]], m[2] == "T") for m in witness.split()]


def stages(value, witness):
    """Returns the tiles of a listed tiling and, for each number of placements made, the staircase with real lengths."""
    tiles = witness_tiles(value, witness)
    x = float(value)
    tiers = (Tier(sp.Integer(0), sp.Integer(0), sp.Integer(1), sp.Integer(1)),)
    out = []
    for (i, fit, tall), (_, _, w, h) in zip(moves_of(witness), tiles):
        out.append(concrete(tiers, x))
        tiers, _, _ = place(tiers, i, fit, tall, sp.Float(min(w, h)))
    out.append(concrete(tiers, x))
    return tiles, out


def concrete(tiers, x):
    """Evaluates the anchors, floors and walls of a staircase at a proportion."""
    return [Tier(*(float(sp.sympify(c).subs(X, x)) for c in (t.ax, t.ay, t.floor, t.wall)), t.stale, t.started) for t in tiers]


def outline_rest(ax, tiles):
    """Outlines the tiles still to be placed."""
    for x, y, w, h in tiles:
        ax.add_patch(Rectangle((x, y), w, h, fc="none", ec="0.72", lw=0.35, zorder=2))


def mark_anchors(ax, tiers, size=4.0, chosen=None):
    """Circles the anchors of a staircase, in grey for stale tiers and in black for a chosen one."""
    for t in tiers:
        colour = "k" if t is chosen else ("0.7" if t.stale else "w")
        ax.plot([t.ax], [t.ay], marker="o", mfc=colour, mec="k", ms=size, zorder=6)


def excluded(tiers):
    """Lists the placements that the two rules exclude at a staircase, as pairs of a tier index and a reason."""
    out = []
    for i, t in enumerate(tiers):
        if t.stale:
            out.append((i, "stale"))
        elif i > 0 and tiers[i - 1].started:
            out.append((i, "no full height, no full"))
    return out


def base_tiling():
    """Selects the listed tiling used for the staircase, fit and rule diagrams: all four fits occur, no tile is small, and some staircase with at least three tiers has both flags present."""
    best = None
    for n in (7, 6):
        for value, witness in listing(n):
            moves = moves_of(witness)
            if {fit for _, fit, _ in moves} != set(CODES.values()):
                continue
            tiles, sts = stages(value, witness)
            smallest = min(min(w, h) for _, _, w, h in tiles)
            if smallest < 0.07:
                continue
            rich = [k for k, s in enumerate(sts) if len(s) >= 3 and any(t.stale for t in s) and any(t.started for t in s)]
            if not rich:
                continue
            top = max(rich, key=lambda k: (len(sts[k]), -k))
            thin = min(min(t.floor, t.wall) for t in sts[top])
            second = any(reason != "stale" for st in sts for _, reason in excluded(st))
            score = (second, len(sts[top]), min(thin, 0.1), len(rich), smallest)
            rich = [top]
            if best is None or score > best[0]:
                best = (score, value, witness, rich[0])
    return best[1], best[2], best[3]


def staircase_figure(path, value, witness, k):
    """Draws the tiles placed by the first k placements of a listed tiling, with its staircase annotated."""
    tiles, sts = stages(value, witness)
    tiers = sts[k]
    fig, ax = plt.subplots(figsize=(3.9, 3.9))
    draw(ax, tiles[:k])
    outline_rest(ax, tiles[k:])
    ax.set_xlim(-0.16, 1.14)
    ax.set_ylim(-0.12, 1.06)
    for j, t in enumerate(tiers):
        ax.add_patch(Rectangle((t.ax, t.ay), t.floor, t.wall, fc="none", hatch="//", lw=0, ec="lightgray", zorder=1))
        ax.plot([t.ax, 1], [t.ay + t.wall, t.ay + t.wall], color="0.5", lw=0.5, ls=(0, (3, 2)), zorder=3)
        ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=2.2, solid_capstyle="butt", zorder=4)
        ax.plot([t.ax, t.ax], [t.ay, t.ay + t.wall], color="k", lw=2.2, solid_capstyle="butt", zorder=4)
        ax.text(t.ax - 0.018, t.ay - 0.02, f"$(a_{j}, b_{j})$", fontsize=6.3, ha="right", va="top", zorder=7)
        ax.text(t.ax + t.floor / 2, t.ay + 0.016, f"$L_{j}$", fontsize=7.5, ha="center", va="bottom", zorder=7)
        ax.text(t.ax + 0.016, t.ay + t.wall / 2, f"$M_{j}$", fontsize=7.5, ha="left", va="center", zorder=7)
        ax.text(1.03, t.ay + t.wall / 2, f"$T_{j}$", fontsize=9, ha="left", va="center", color="0.3", zorder=7)
    mark_anchors(ax, [Tier(t.ax, t.ay, t.floor, t.wall) for t in tiers], size=5.5)
    fig.tight_layout(pad=0.1)
    fig.savefig(path)
    plt.close(fig)


def fits_figure(path, value, witness):
    """Draws one placement of each fit from the record of a listed tiling, with the floor and the wall of its tier."""
    tiles, sts = stages(value, witness)
    moves = moves_of(witness)
    fig, axes = plt.subplots(1, 4, figsize=(6.6, 2.0))
    chosen = []
    for ax, fit in zip(axes, CODES.values()):
        k = max((k for k, (_, f, _) in enumerate(moves) if f == fit), key=lambda k: min(tiles[k][2], tiles[k][3]))
        i = moves[k][0]
        t = sts[k][i]
        x, y, w, h = tiles[k]
        narrow, low = w < t.floor - EPS, h < t.wall - EPS
        assert abs(x - t.ax) < EPS and abs(y - t.ay) < EPS and w <= t.floor + EPS and h <= t.wall + EPS
        assert (narrow, low) == (fit in ("inside", "full-height"), fit in ("inside", "full-width")), (fit, k)
        draw(ax, tiles[: k + 1])
        outline_rest(ax, tiles[k + 1 :])
        ax.add_patch(Rectangle((t.ax, t.ay), t.floor, t.wall, fc="none", hatch="//", lw=0, ec="0.45", zorder=3))
        ax.add_patch(Rectangle((x, y), w, h, fc="none", ec="k", lw=1.1, zorder=5))
        ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=2.4, solid_capstyle="butt", zorder=4)
        ax.plot([t.ax, t.ax], [t.ay, t.ay + t.wall], color="k", lw=2.4, solid_capstyle="butt", zorder=4)
        mark_anchors(ax, [Tier(u.ax, u.ay, u.floor, u.wall) for u in sts[k + 1]], size=3.6)
        ax.set_title(f"placement {k + 1}: {FIT_NAMES[fit]}", fontsize=7, pad=3)
        chosen.append((fit, k + 1, i, len(sts[k]), len(sts[k + 1])))
    fig.tight_layout(pad=0.2, w_pad=0.5)
    fig.savefig(path)
    plt.close(fig)
    return chosen


def rules_figure(path, value, witness):
    """Draws the staircases of a listed tiling that carry the most flags, marking stale tiers and started floors."""
    tiles, sts = stages(value, witness)
    ranked = sorted(range(1, len(sts) - 1), key=lambda k: (-any(r != "stale" for _, r in excluded(sts[k])), -any(t.stale for t in sts[k]), -len(sts[k]), k))
    picks = sorted(ranked[:3])
    fig, axes = plt.subplots(1, 3, figsize=(6.6, 2.45))
    notes = []
    for ax, k in zip(axes, picks):
        draw(ax, tiles[:k])
        outline_rest(ax, tiles[k:])
        for j, t in enumerate(sts[k]):
            style = dict(color="tab:red", lw=2.6, ls=(0, (2, 1.2))) if t.started else dict(color="k", lw=1.8)
            ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], solid_capstyle="butt", zorder=4, **style)
            ax.text(t.ax + 0.025, t.ay + 0.022, f"$T_{j}$", fontsize=7, ha="left", va="bottom", zorder=7)
        mark_anchors(ax, sts[k], size=4.6)
        ax.set_title(f"after {k} placements", fontsize=7, pad=3)
        notes.append((k, [(j, t.stale, t.started) for j, t in enumerate(sts[k])], excluded(sts[k]), moves_of(witness)[k]))
    fig.tight_layout(pad=0.2, w_pad=0.5)
    fig.savefig(path)
    plt.close(fig)
    return notes


def example_figure(path):
    """Draws the three placements of the worked example at its exact proportion, with the sizes of the tiles."""
    value = str(sp.real_roots(sp.Poly(X**3 - 2 * X**2 + X - 1, X))[-1].evalf(30))
    tiles = witness_tiles(value, "0wW 0hT 0fW")
    labels = [(r"$W$", r"$W/x$"), (r"$h/x$", r"$h = 1 - W/x$"), (r"$W - h/x$", r"$h$")]
    fig, axes = plt.subplots(1, 3, figsize=(6.6, 2.35))
    for k, ax in enumerate(axes):
        draw(ax, tiles[: k + 1])
        ax.set_xlim(-0.2, 1.2)
        ax.set_ylim(-0.2, 1.2)
        x, y, w, h = tiles[k]
        level = y - 0.045 if k == 0 else y + h + 0.045
        ax.annotate("", (x, level), (x + w, level), arrowprops=dict(arrowstyle="<->", lw=0.5))
        ax.text(x + w / 2, level - 0.025 if k == 0 else level + 0.015, labels[k][0], fontsize=7, ha="center", va="top" if k == 0 else "bottom")
        side = x - 0.045 if k < 2 else x + w + 0.045
        ax.annotate("", (side, y), (side, y + h), arrowprops=dict(arrowstyle="<->", lw=0.5))
        ax.text(side - 0.02 if k < 2 else side + 0.02, y + h / 2, labels[k][1], fontsize=7, ha="right" if k < 2 else "left", va="center", rotation=90)
        ax.set_title(("full width, wide", "full height, tall", "full, wide")[k], fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.4)
    fig.savefig(path)
    plt.close(fig)


def extends(tiles, c, d):
    """Whether some tile has its top side at height d over an interval starting at or before c and ending after it."""
    return any(abs(y + h - d) < EPS and x <= c + EPS and c < x + w - EPS for x, y, w, h in tiles)


def construction_choice():
    """Selects the listed tiling with six tiles whose construction shows the most extending floors, amongst those without small tiles.

    Tilings in which four tiles meet at a point are passed over: they arise from two records, and the one listed need not be the one that the construction yields.
    """
    best = None
    for value, witness in listing(6):
        tiles, sts = stages(value, witness)
        if min(min(w, h) for _, _, w, h in tiles) < 0.12:
            continue
        moves = moves_of(witness)
        if any(next(j for j, t in enumerate(sts[k]) if not extends(tiles, t.ax + t.floor, t.ay)) != moves[k][0] for k in range(len(tiles))):
            continue
        score = sum(sum(extends(tiles, t.ax + t.floor, t.ay) for t in s) for s in sts) + sum(len(s) >= 3 for s in sts)
        if best is None or score > best[0]:
            best = (score, value, witness)
    return best[1], best[2]


def construction_figure(path, value, witness):
    """Draws the stages of the construction of the record of a listed tiling, marking the floors that extend."""
    tiles, sts = stages(value, witness)
    moves = moves_of(witness)
    fig, axes = plt.subplots(1, len(tiles), figsize=(6.8, 1.55))
    for k, ax in enumerate(axes):
        draw(ax, tiles[:k])
        outline_rest(ax, tiles[k:])
        first = None
        for j, t in enumerate(sts[k]):
            ext = extends(tiles, t.ax + t.floor, t.ay)
            ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="tab:red" if ext else "k", lw=1.8, ls=(0, (2, 1.2)) if ext else "-", solid_capstyle="butt", zorder=4)
            if not ext and first is None:
                first = j
        assert first == moves[k][0], (k, first, moves[k])
        mark_anchors(ax, sts[k], size=3.6, chosen=sts[k][first])
        ax.set_title(f"before placement {k + 1}", fontsize=6, pad=2)
    fig.tight_layout(pad=0.15, w_pad=0.3)
    fig.savefig(path)
    plt.close(fig)


def corner_order(tiles):
    """Describes, for each vertical segment with corners on both sides, the order of those corners from the bottom."""
    out = []
    for c in sorted({round(x + w, 9) for x, _, w, _ in tiles if x + w < 1 - EPS}):
        left = sorted({round(y + h, 9) for x, y, w, h in tiles if abs(x + w - c) < EPS})
        right = sorted({round(y + h, 9) for x, y, w, h in tiles if abs(x - c) < EPS})
        marks = sorted({(v, "l") for v in left if v not in right} | {(v, "r") for v in right if v not in left})
        word = "".join(side for _, side in marks)
        if "l" in word and "r" in word:
            out.append(word)
    return out


def mosaic_choice():
    """Selects listed tilings with the same placements, up to orientations, in which the corners along a vertical segment alternate differently."""
    groups = {}
    for n in (5, 6):
        for value, witness in listing(n):
            key = " ".join(m[:2] for m in witness.split())
            groups.setdefault(key, []).append((value, witness))
    best = None
    for key, members in groups.items():
        seen = {}
        for value, witness in members:
            tiles = witness_tiles(value, witness)
            if min(min(w, h) for _, _, w, h in tiles) < 0.1:
                continue
            order = tuple(corner_order(tiles))
            if order:
                seen.setdefault(order, (value, witness))
        if len(seen) >= 2 and (best is None or len(seen) > len(best)):
            best = seen
    return list(best.items())[:3]


def mosaic_figure(path, choice):
    """Draws listed tilings that share their placements but not the order of corners along a vertical segment."""
    fig, axes = plt.subplots(1, len(choice), figsize=(1.75 * len(choice), 1.95))
    for ax, (order, (value, witness)) in zip(axes, choice):
        draw(ax, witness_tiles(value, witness))
        ax.set_title(f"$x = {float(value):.4f}$", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def symmetry_figure(path, value, witness):
    """Draws a listed tiling, its transpose, and the tiling obtained by cutting one tile into four."""
    tiles = witness_tiles(value, witness)
    fig, axes = plt.subplots(1, 3, figsize=(4.8, 1.75))
    draw(axes[0], tiles)
    draw(axes[1], [(y, x, h, w) for x, y, w, h in tiles])
    k = max(range(len(tiles)), key=lambda j: tiles[j][2] * tiles[j][3])
    x, y, w, h = tiles[k]
    quarters = [(x, y, w / 2, h / 2), (x + w / 2, y, w / 2, h / 2), (x, y + h / 2, w / 2, h / 2), (x + w / 2, y + h / 2, w / 2, h / 2)]
    draw(axes[2], tiles[:k] + tiles[k + 1 :] + quarters)
    for ax, title in zip(axes, ("a tiling", "its transpose", "three more tiles")):
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def pinwheel_figure(path):
    """Draws the exact solutions of the system of the pinwheel record of five tiles, with the width of the main rectangle free, for three proportions."""
    moves = [(0, "inside", False), (0, "full-height", False), (0, "full-width", False), (1, "full", True), (0, "full", False)]
    width_symbol = sp.Symbol("W", positive=True)
    tiers = (Tier(sp.Integer(0), sp.Integer(0), width_symbol, sp.Integer(1)),)
    tiles, equations, sides = [], [], []
    for i, fit, tall in moves:
        side = None
        if fit == "inside":
            side = sp.Symbol(f"s{len(sides)}")
            sides.append(side)
        tiers, tile, equation = place(tiers, i, fit, tall, side)
        tiles.append(tile)
        if equation is not None:
            equations.append(equation)
    solution = sp.solve(equations, [width_symbol] + sides, dict=True)[0]
    width = sp.simplify(solution[width_symbol])
    centre = sp.factor(sp.simplify(sp.sympify(tiles[2][3]).subs(solution)))
    xs = (sp.Rational(11, 5), sp.Rational(3, 2), sp.Integer(1))
    fig, axes = plt.subplots(1, 3, figsize=(6.6, 2.1), gridspec_kw=dict(width_ratios=[float(width.subs(X, x)) for x in xs]))
    for ax, x in zip(axes, xs):
        concrete_tiles = [tuple(float(sp.sympify(c).subs(solution).subs(X, x)) for c in t) for t in tiles]
        w = float(width.subs(X, x))
        draw(ax, concrete_tiles, width=w, height=1.0)
        ax.set_title(f"$x = {float(x):.1f}$, width ${w:.3f}$", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)
    return width, centre


def two_tiles_figure(path):
    """Draws the two placements of the tiling of the square by two tiles."""
    value, witness = listing(2)[0]
    tiles, sts = stages(value, witness)
    fig, axes = plt.subplots(1, 2, figsize=(3.2, 1.75))
    for k, ax in enumerate(axes):
        draw(ax, tiles[: k + 1])
        mark_anchors(ax, sts[k + 1], size=4)
        ax.set_title(f"after placement {k + 1}", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)
    return value, witness


def main():
    """Generates all diagrams and prints the facts on which their captions rely."""
    value, witness, k = base_tiling()
    print("base tiling:", value, witness, "staircase after", k, "placements")
    staircase_figure(OUT / "staircase.svg", value, witness, k)
    print("fits:", fits_figure(OUT / "fits.svg", value, witness))
    for note in rules_figure(OUT / "rules.svg", value, witness):
        print("rules:", note)
    example_figure(OUT / "example-steps.svg")
    value, witness = construction_choice()
    print("construction:", value, witness)
    construction_figure(OUT / "construction.svg", value, witness)
    choice = mosaic_choice()
    print("mosaic:", choice)
    mosaic_figure(OUT / "mosaic.svg", choice)
    value, witness = next((v, w) for v, w in listing(5) if "i" in w and "T" in w)
    print("symmetry:", value, witness)
    symmetry_figure(OUT / "symmetry.svg", value, witness)
    print("pinwheel:", pinwheel_figure(OUT / "pinwheel.svg"))
    print("two tiles:", two_tiles_figure(OUT / "two-tiles.svg"))


if __name__ == "__main__":
    main()
