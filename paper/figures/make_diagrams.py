# SPDX-License-Identifier: LGPL-3.0-or-later
"""Generates the explanatory diagrams of the paper: staircases, placements, rules and constructions."""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import sympy as sp
from matplotlib.patches import Rectangle

from make_figures import COLOURS, FITS, Tier, X, place, witness_tiles

OUT = Path(__file__).parent
W = sp.Symbol("W", positive=True)
FIT_NAMES = {"inside": "inside", "full-height": "full height", "full-width": "full width", "full": "full"}
STAIRCASE_MOVES = [(0, "inside", False), (0, "inside", True), (2, "inside", False)]
STAIRCASE_VALUES = {X: 1.5, sp.Symbol("s0"): 0.36, sp.Symbol("s1"): 0.22, sp.Symbol("s2"): 0.16}


def run(moves, width=1, height=1):
    """Replays placements symbolically, returning the tiers, the tiles, the equations and the free sides."""
    tiers = (Tier(sp.Integer(0), sp.Integer(0), sp.sympify(width), sp.sympify(height)),)
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
    return tiers, tiles, equations, sides


def number(expr, values):
    """Evaluates an expression at the given values."""
    return float(sp.sympify(expr).subs(values))


def numbers(tile, values):
    """Evaluates the four coordinates of a tile or tier."""
    return tuple(number(c, values) for c in tile)


def tier_numbers(tier, values):
    """Evaluates the anchor, floor and wall of a tier."""
    return numbers((tier.ax, tier.ay, tier.floor, tier.wall), values)


def frame(ax, width=1.0, height=1.0, margin=0.06):
    """Sets up the axes around a main rectangle and draws its outline."""
    ax.add_patch(Rectangle((0, 0), width, height, fc="none", ec="k", lw=0.7, zorder=5))
    ax.set_xlim(-margin * width, (1 + margin) * width)
    ax.set_ylim(-margin * height, (1 + margin) * height)
    ax.set_aspect("equal")
    ax.axis("off")


def fill(ax, tiles, start=0, alpha=1.0):
    """Draws tiles in the colours of the default cycle, in placement order."""
    for k, (x, y, w, h) in enumerate(tiles):
        ax.add_patch(Rectangle((x, y), w, h, fc=COLOURS[(start + k) % len(COLOURS)], ec="k", lw=0, alpha=alpha))


def anchors(ax, tiers, values, size=5):
    """Circles the anchors of the tiers."""
    for t in tiers:
        x, y, _, _ = tier_numbers(t, values)
        ax.plot([x], [y], marker="o", mfc="none", mec="k", ms=size, zorder=6)


def staircase_figure(path):
    """Draws a partial tiling with its staircase, labelling anchors, floors, walls and tiers."""
    tiers, tiles, _, _ = run(STAIRCASE_MOVES)
    fig, ax = plt.subplots(figsize=(3.6, 3.6))
    fill(ax, [numbers(t, STAIRCASE_VALUES) for t in tiles])
    frame(ax, margin=0.13)
    for k, t in enumerate(tiers):
        x, y, floor, wall = tier_numbers(t, STAIRCASE_VALUES)
        ax.add_patch(Rectangle((x, y), floor, wall, fc="none", hatch="//", lw=0, ec="lightgray", zorder=1))
        ax.add_patch(Rectangle((x, y), 1 - x, wall, fc="none", ec="0.55", lw=0.5, ls=(0, (3, 2)), zorder=3))
        ax.plot([x, x + floor], [y, y], color="k", lw=2.2, solid_capstyle="butt", zorder=4)
        ax.plot([x, x], [y, y + wall], color="k", lw=2.2, solid_capstyle="butt", zorder=4)
        ax.plot([x], [y], marker="o", mfc="w", mec="k", ms=5.5, zorder=6)
        ax.text(x - 0.02, y - 0.022, f"$(a_{k}, b_{k})$", fontsize=6.5, ha="right", va="top", zorder=7)
        ax.text(x + floor / 2, y + 0.02, f"$L_{k}$", fontsize=7.5, ha="center", va="bottom", zorder=7)
        ax.text(x + 0.02, y + wall / 2, f"$M_{k}$", fontsize=7.5, ha="left", va="center", zorder=7)
        ax.text(1.03, y + wall / 2, f"$T_{k}$", fontsize=9, ha="left", va="center", color="0.3", zorder=7)
    fig.tight_layout(pad=0.1)
    fig.savefig(path)
    plt.close(fig)


def fits_figure(path):
    """Draws the four fits of a tile placed at the last tier of the staircase of the first figure."""
    tiers, tiles, _, _ = run(STAIRCASE_MOVES)
    placed = [numbers(t, STAIRCASE_VALUES) for t in tiles]
    fig, axes = plt.subplots(1, 4, figsize=(6.6, 1.9))
    values = dict(STAIRCASE_VALUES)
    values[sp.Symbol("s")] = 0.12
    for ax, fit in zip(axes, FITS):
        new_tiers, tile, _ = place(tiers, 3, fit, fit in ("inside", "full-width"), sp.Symbol("s"))
        fill(ax, placed, alpha=0.35)
        x, y, w, h = numbers(tile, values)
        ax.add_patch(Rectangle((x, y), w, h, fc=COLOURS[3], ec="k", lw=0.6, zorder=4))
        frame(ax)
        anchors(ax, new_tiers, values, size=3.5)
        ax.set_title(f"{FIT_NAMES[fit]}: {len(new_tiers)} tiers", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def rules_figure(path):
    """Draws the flags of the staircase of the first figure and the two placements that the rules forbid at its third tier."""
    tiers, tiles, _, _ = run(STAIRCASE_MOVES)
    placed = [numbers(t, STAIRCASE_VALUES) for t in tiles]
    fig, axes = plt.subplots(1, 3, figsize=(6.6, 2.4))
    ax = axes[0]
    fill(ax, placed, alpha=0.35)
    frame(ax)
    for k, t in enumerate(tiers):
        x, y, floor, wall = tier_numbers(t, STAIRCASE_VALUES)
        style = dict(color="tab:red", lw=2.4, ls=(0, (2, 1.2))) if t.started else dict(color="k", lw=1.6)
        ax.plot([x, x + floor], [y, y], solid_capstyle="butt", zorder=4, **style)
        ax.plot([x], [y], marker="o", mfc="0.75" if t.stale else "w", mec="k", ms=5, zorder=6)
        ax.text(x + 0.03, y + 0.03, f"$T_{k}$" + (" stale" if t.stale else ""), fontsize=6.5, ha="left", va="bottom", zorder=7)
    ax.set_title("flags after three placements", fontsize=7, pad=3)
    values = dict(STAIRCASE_VALUES)
    for ax, fit in zip(axes[1:], ("full-height", "full")):
        _, tile, _ = place(tiers, 2, fit, False, None)
        fill(ax, placed, alpha=0.35)
        x, y, w, h = numbers(tile, values)
        ax.add_patch(Rectangle((x, y), w, h, fc="none", ec="tab:red", lw=1.0, hatch="xx", zorder=4))
        t1 = tier_numbers(tiers[1], values)
        ax.plot([t1[0], t1[0] + t1[2]], [t1[1], t1[1]], color="tab:red", lw=2.4, ls=(0, (2, 1.2)), solid_capstyle="butt", zorder=5)
        frame(ax)
        ax.set_title(f"{FIT_NAMES[fit]} at $T_2$: not admissible", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def example_figure(path):
    """Draws the three placements of the worked example, with the sizes of the tiles."""
    moves = [(0, "full-width", False), (0, "full-height", True), (0, "full", False)]
    root = sp.real_roots(sp.Poly(X**3 - 2 * X**2 + X - 1, X))[-1]
    values = {X: float(root)}
    _, tiles, _, _ = run(moves)
    concrete = [numbers(t, values) for t in tiles]
    labels = [(r"$W$", r"$W/x$"), (r"$h/x$", r"$h = 1 - W/x$"), (r"$W - h/x$", r"$h$")]
    fig, axes = plt.subplots(1, 3, figsize=(6.6, 2.35))
    for k, ax in enumerate(axes):
        fill(ax, concrete[: k + 1])
        frame(ax, margin=0.16)
        x, y, w, h = concrete[k]
        ax.annotate("", (x, y - 0.045 if k == 0 else y + h + 0.045), (x + w, y - 0.045 if k == 0 else y + h + 0.045), arrowprops=dict(arrowstyle="<->", lw=0.5))
        ax.text(x + w / 2, y - 0.07 if k == 0 else y + h + 0.06, labels[k][0], fontsize=7, ha="center", va="top" if k == 0 else "bottom")
        side = x - 0.045 if k < 2 else x + w + 0.045
        ax.annotate("", (side, y), (side, y + h), arrowprops=dict(arrowstyle="<->", lw=0.5))
        ax.text(side - 0.02 if k < 2 else side + 0.02, y + h / 2, labels[k][1], fontsize=7, ha="right" if k < 2 else "left", va="center", rotation=90)
        ax.set_title(("full width, wide", "full height, tall", "full, wide")[k], fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.4)
    fig.savefig(path)
    plt.close(fig)


def doomed_figure(path):
    """Draws a placement whose tile is positive but wider than its floor, and the non-positive floor that it leaves."""
    moves = [(0, "inside", False), (1, "inside", False)]
    values = {X: 1.6, sp.Symbol("s0"): 0.34, sp.Symbol("s1"): 0.2}
    tiers, tiles, _, _ = run(moves)
    fig, axes = plt.subplots(1, 2, figsize=(4.6, 2.2))
    for ax, s1 in zip(axes, (0.2, 0.36)):
        values[sp.Symbol("s1")] = s1
        concrete = [numbers(t, values) for t in tiles]
        fill(ax, concrete)
        frame(ax, margin=0.2)
        x, y, floor, _ = tier_numbers(tiers[2], values)
        colour = "k" if floor > 0 else "tab:red"
        ax.annotate("", (x, y - 0.06), (x + floor, y - 0.06), arrowprops=dict(arrowstyle="<->", lw=0.9, color=colour))
        ax.text(x + floor / 2, y - 0.09, f"floor {floor:+.2f}", fontsize=7, ha="center", va="top", color=colour)
        ax.set_title("the tile fits" if floor > 0 else "a positive tile, a negative floor", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def extends(tiles, c, d):
    """Whether some tile has its top side at height d over an interval starting at or before c and ending after it."""
    return any(abs(y + h - d) < 1e-9 and x <= c + 1e-9 and c < x + w - 1e-9 for x, y, w, h in tiles)


def construction_figure(path, value, witness):
    """Draws the stages of the construction of the record of a tiling, marking the floors that extend."""
    codes = {"i": "inside", "h": "full-height", "w": "full-width", "f": "full"}
    moves = [(int(m[0]), codes[m[1]], m[2] == "T") for m in witness.split()]
    tiles = witness_tiles(value, witness)
    n = len(tiles)
    fig, axes = plt.subplots(1, n, figsize=(6.8, 1.55))
    for k, ax in enumerate(axes):
        tiers = (Tier(0.0, 0.0, 1.0, 1.0),)
        for j, (i, fit, tall) in enumerate(moves[:k]):
            _, _, w, h = tiles[j]
            tiers, _, _ = place(tiers, i, fit, tall, min(w, h))
        tiers = [Tier(*(number(c, {X: float(value)}) for c in (t.ax, t.ay, t.floor, t.wall)), t.stale, t.started) for t in tiers]
        fill(ax, tiles[:k])
        for x, y, w, h in tiles[k:]:
            ax.add_patch(Rectangle((x, y), w, h, fc="none", ec="0.6", lw=0.4, zorder=2))
        frame(ax)
        chosen = None
        for idx, t in enumerate(tiers):
            ext = extends(tiles, t.ax + t.floor, t.ay) and t.ax + t.floor < 1 - 1e-9
            ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="tab:red" if ext else "k", lw=1.8, ls=(0, (2, 1.2)) if ext else "-", solid_capstyle="butt", zorder=4)
            if not ext and chosen is None:
                chosen = t
        for t in tiers:
            ax.plot([t.ax], [t.ay], marker="o", mfc="k" if t is chosen else "w", mec="k", ms=3.6, zorder=6)
        ax.set_title(f"before placement {k + 1}", fontsize=6, pad=2)
    fig.tight_layout(pad=0.15, w_pad=0.3)
    fig.savefig(path)
    plt.close(fig)


def mosaic_figure(path):
    """Draws three tilings by four rectangles with the same segments, in which the corners along the vertical segment alternate differently."""
    fig, axes = plt.subplots(1, 3, figsize=(4.8, 1.75))
    for ax, (a, b) in zip(axes, ((0.38, 0.62), (0.5, 0.5), (0.62, 0.38))):
        fill(ax, [(0, 0, 0.45, a), (0, a, 0.45, 1 - a), (0.45, 0, 0.55, b), (0.45, b, 0.55, 1 - b)])
        frame(ax)
    for ax, title in zip(axes, ("left corner below", "four tiles at a point", "left corner above")):
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def symmetry_figure(path, value, witness):
    """Draws a tiling, its transpose, and the tiling obtained by cutting one tile into four."""
    tiles = witness_tiles(value, witness)
    fig, axes = plt.subplots(1, 3, figsize=(4.8, 1.75))
    fill(axes[0], tiles)
    fill(axes[1], [(y, x, h, w) for x, y, w, h in tiles])
    fill(axes[2], tiles)
    x, y, w, h = max(tiles, key=lambda t: t[2] * t[3])
    axes[2].plot([x + w / 2, x + w / 2], [y, y + h], color="w", lw=1.0, zorder=4)
    axes[2].plot([x, x + w], [y + h / 2, y + h / 2], color="w", lw=1.0, zorder=4)
    for ax, title in zip(axes, ("a tiling", "its transpose", "three more tiles")):
        frame(ax)
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def pinwheel_figure(path):
    """Draws the pinwheel arrangement of five tiles for three proportions, the last being the one for which the main rectangle is a square."""
    moves = [(0, "inside", False), (0, "full-height", False), (0, "full-width", False), (1, "full", True), (0, "full", False)]
    _, tiles, equations, sides = run(moves, width=W)
    solution = sp.solve(equations, [W] + sides, dict=True)[0]
    width = sp.simplify(solution[W])
    fig, axes = plt.subplots(1, 3, figsize=(6.6, 2.1), gridspec_kw=dict(width_ratios=[float(width.subs(X, x)) for x in (2.2, 1.5, 1.0)]))
    for ax, x in zip(axes, (2.2, 1.5, 1.0)):
        values = {X: x}
        concrete = [tuple(float(sp.sympify(c).subs(solution).subs(values)) for c in t) for t in tiles]
        w = float(width.subs(values))
        fill(ax, concrete)
        frame(ax, width=w, height=1.0)
        ax.set_title(f"$x = {x:.1f}$, width ${w:.3f}$", fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)
    return width


def two_tiles_figure(path):
    """Draws the staircases after each admissible first placement for two tiles, and the tiling found."""
    fig, axes = plt.subplots(1, 3, figsize=(4.8, 1.75))
    fill(axes[0], [(0, 0, 1, 1 / 1.6)])
    axes[0].plot([0], [1 / 1.6], marker="o", mfc="w", mec="k", ms=4, zorder=6)
    axes[0].set_title("full width, wide", fontsize=7, pad=3)
    fill(axes[1], [(0, 0, 1.6, 1)])
    axes[1].plot([1.6], [0], marker="o", mfc="w", mec="k", ms=4, zorder=6)
    axes[1].set_title("full height, wide: floor $1 - x$", fontsize=7, pad=3)
    fill(axes[2], [(0, 0, 1, 0.5), (0, 0.5, 1, 0.5)])
    axes[2].set_title("the tiling, $x = 2$", fontsize=7, pad=3)
    for ax in axes:
        frame(ax, margin=0.06)
    axes[1].set_xlim(-0.06, 1.7)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path)
    plt.close(fig)


def best_construction(n):
    """Returns the listed tiling with n tiles whose construction shows the most extending floors, amongst those without small tiles."""
    codes = {"i": "inside", "h": "full-height", "w": "full-width", "f": "full"}
    best = None
    for line in (OUT.parent / "data" / f"tilings-{n}.tsv").read_text().splitlines():
        value, _, _, _, witness = line.split("\t")
        tiles = witness_tiles(value, witness)
        if min(min(w, h) for _, _, w, h in tiles) < 0.14:
            continue
        moves = [(int(m[0]), codes[m[1]], m[2] == "T") for m in witness.split()]
        score = 0
        tiers = (Tier(0.0, 0.0, 1.0, 1.0),)
        for j, (i, fit, tall) in enumerate(moves):
            concrete = [Tier(*(number(c, {X: float(value)}) for c in (t.ax, t.ay, t.floor, t.wall))) for t in tiers]
            score += sum(extends(tiles, t.ax + t.floor, t.ay) and t.ax + t.floor < 1 - 1e-9 for t in concrete) + (len(concrete) >= 3)
            _, _, w, h = tiles[j]
            tiers, _, _ = place(tiers, i, fit, tall, min(w, h))
        if best is None or score > best[0]:
            best = (score, value, witness)
    return best[1], best[2]


def pick(n, condition):
    """Returns the first listed proportion with n tiles whose witness satisfies the condition."""
    for line in (OUT.parent / "data" / f"tilings-{n}.tsv").read_text().splitlines():
        value, _, _, _, witness = line.split("\t")
        if condition(witness):
            return value, witness
    raise LookupError("no witness satisfies the condition")


def main():
    """Generates all diagrams."""
    staircase_figure(OUT / "staircase.svg")
    fits_figure(OUT / "fits.svg")
    rules_figure(OUT / "rules.svg")
    example_figure(OUT / "example-steps.svg")
    doomed_figure(OUT / "doomed.svg")
    value, witness = best_construction(6)
    print("construction:", value, witness)
    construction_figure(OUT / "construction.svg", value, witness)
    mosaic_figure(OUT / "mosaic.svg")
    value, witness = pick(5, lambda w: w.count("i") >= 1 and "T" in w)
    symmetry_figure(OUT / "symmetry.svg", value, witness)
    print("pinwheel:", pinwheel_figure(OUT / "pinwheel.svg"))
    two_tiles_figure(OUT / "two-tiles.svg")


if __name__ == "__main__":
    main()
