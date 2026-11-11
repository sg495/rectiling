# SPDX-License-Identifier: LGPL-3.0-or-later
"""Generates the figures of the paper from staircase placement sequences."""

from dataclasses import dataclass
from itertools import product
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.colors as mcolors
import matplotlib.pyplot as plt
import sympy as sp
from matplotlib.patches import Rectangle

COLOURS = tuple(mcolors.TABLEAU_COLORS)
FITS = ("inside", "full-height", "full-width", "full")
X = sp.Symbol("x", positive=True)
OUT = Path(__file__).parent


@dataclass(frozen=True, slots=True)
class Tier:
    """Tier of the staircase: anchor, floor, wall and flags."""

    ax: sp.Expr
    ay: sp.Expr
    floor: sp.Expr
    wall: sp.Expr
    stale: bool = False
    started: bool = False


def admits(tiers: tuple[Tier, ...], i: int, fit: str, remaining: int) -> bool:
    """Whether a placement is possible with the given number of tiles still to place."""
    if tiers[i].stale:
        return False
    if fit in ("full-height", "full") and i > 0 and tiers[i - 1].started:
        return False
    after = len(tiers) + (fit == "inside") - (fit == "full")
    left = remaining - 1
    return left >= after and (after > 0 or left == 0)


def place(tiers, i, fit, tall, side):
    """Places a tile, returning the new tiers, the tile rectangle and the equation it imposes, if any."""
    t = tiers[i]
    equation = None
    if fit == "inside":
        w, h = (side, X * side) if tall else (X * side, side)
    elif fit == "full-height":
        h = t.wall
        w = h / X if tall else X * h
    elif fit == "full-width":
        w = t.floor
        h = X * w if tall else w / X
    else:
        w, h = t.floor, t.wall
        equation = (h - X * w) if tall else (w - X * h)
    tile = (t.ax, t.ay, w, h)
    low = fit in ("inside", "full-width")
    narrow = fit in ("inside", "full-height")
    new = [Tier(u.ax, u.ay, u.floor, u.wall, True, u.started) for u in tiers[:i]]
    if not low and i > 0:
        p = new[i - 1]
        new[i - 1] = Tier(p.ax, p.ay, p.floor + w, p.wall, False, p.started)
    if fit == "inside":
        new.append(Tier(t.ax, t.ay + h, w, t.wall - h))
        new.append(Tier(t.ax + w, t.ay, t.floor - w, h, False, True))
    elif fit == "full-height":
        new.append(Tier(t.ax + w, t.ay, t.floor - w, t.wall, False, True))
    elif fit == "full-width":
        new.append(Tier(t.ax, t.ay + h, t.floor, t.wall - h))
    rest = list(tiers[i + 1 :])
    if not narrow and rest:
        b = rest[0]
        rest[0] = Tier(b.ax, b.ay, b.floor, b.wall + h, b.stale, b.started)
    return tuple(new + rest), tile, equation


def replay(moves, width=1, height=1):
    """Replays a placement sequence symbolically, returning tiers, tiles, equations and the free sides."""
    tiers = (Tier(sp.Integer(0), sp.Integer(0), sp.Integer(width), sp.Integer(height)),)
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


def solve(moves, width=1, height=1):
    """Returns the tilings realised by a complete placement sequence, as pairs of a proportion and concrete tiles."""
    _, tiles, equations, sides = replay(moves, width, height)
    if sides:
        solution = sp.solve(equations[: len(sides)], sides, dict=True)
        if not solution:
            return []
        solution = solution[0]
        if len(solution) < len(sides):
            return []
    else:
        solution = {}
    residual = sp.together(equations[-1].subs(solution))
    numerator = sp.Poly(sp.numer(residual), X)
    out = []
    for root in sp.real_roots(numerator):
        value = float(root)
        if value < 1 - 1e-12:
            continue
        concrete = [tuple(float(sp.sympify(c).subs(solution).subs(X, root)) for c in tile) for tile in tiles]
        if all(w > 1e-9 and h > 1e-9 for _, _, w, h in concrete):
            out.append((value, concrete))
    return out


def sequences(n, square=True):
    """Enumerates the complete placement sequences with orientations for n tiles."""

    def rec(tiers, remaining, moves):
        if not tiers:
            yield tuple(moves)
            return
        for i, fit, tall in product(range(len(tiers)), FITS, (False, True)):
            if tall and not moves and square:
                continue
            if not admits(tiers, i, fit, remaining):
                continue
            new, _, _ = place(tiers, i, fit, tall, sp.Symbol("s"))
            yield from rec(new, remaining - 1, moves + [(i, fit, tall)])

    yield from rec((Tier(0, 0, 1, 1),), n, [])


def tilings(n):
    """Returns the tilings of the unit square by n similar rectangles, sorted by proportion."""
    found = []
    for moves in sequences(n):
        for value, tiles in solve(moves):
            found.append((value, tiles, moves))
    found.sort(key=lambda item: item[0])
    return found


def draw(ax, tiles, width=1.0, height=1.0, outline=True):
    """Draws tiles in the colours of the default Matplotlib cycle, in placement order."""
    for k, (x, y, w, h) in enumerate(tiles):
        ax.add_patch(Rectangle((x, y), w, h, fc=COLOURS[k % len(COLOURS)], ec="k", lw=0))
    if outline:
        ax.add_patch(Rectangle((0, 0), width, height, fc="none", ec="k", lw=0.6))
    ax.set_xlim(-0.05 * width, 1.05 * width)
    ax.set_ylim(-0.05 * height, 1.05 * height)
    ax.set_aspect("equal")
    ax.axis("off")


def grid(items, columns, path, labels=None):
    """Saves a grid of tilings."""
    rows = -(-len(items) // columns)
    fig, axes = plt.subplots(rows, columns, figsize=(1.25 * columns, 1.4 * rows), squeeze=False)
    for ax in axes.flat:
        ax.axis("off")
    for k, tiles in enumerate(items):
        ax = axes.flat[k]
        draw(ax, tiles)
        if labels is not None:
            ax.set_title(labels[k], fontsize=7, pad=2)
    fig.tight_layout(pad=0.3)
    fig.savefig(path)
    plt.close(fig)


def distinct(found):
    """Keeps the first tiling found for each proportion."""
    out = []
    for value, tiles, moves in found:
        if not out or abs(out[-1][0] - value) > 1e-9:
            out.append((value, tiles, moves))
    return out


def witness_tiles(value, witness):
    """Computes the tiles of the tiling described by a proportion and a witness sequence from the search tool."""
    codes = {"i": "inside", "h": "full-height", "w": "full-width", "f": "full"}
    moves = [(int(m[0]), codes[m[1]], m[2] == "T") for m in witness.split()]
    _, tiles, equations, sides = replay(moves)
    x = sp.Float(value, 30)
    solution = {}
    if sides:
        solution = sp.solve([e.subs(X, x) for e in equations[: len(sides)]], sides, dict=True)[0]
    return [tuple(float(sp.sympify(c).subs(X, x).subs(solution)) for c in tile) for tile in tiles]


def catalogue(n, columns, path, size, labels=True):
    """Draws one tiling for each proportion listed by the search tool for n tiles."""
    rows = [line.split("\t") for line in (OUT.parent / "data" / f"tilings-{n}.tsv").read_text().splitlines()]
    count = -(-len(rows) // columns)
    fig, axes = plt.subplots(count, columns, figsize=(size * columns, size * (1.18 if labels else 1.0) * count), squeeze=False)
    for ax in axes.flat:
        ax.axis("off")
    for ax, (value, _, _, _, witness) in zip(axes.flat, rows):
        draw(ax, witness_tiles(value, witness))
        if labels:
            ax.set_title(f"{float(value):.4f}", fontsize=5.5, pad=1.5)
    fig.tight_layout(pad=0.15, h_pad=0.25, w_pad=0.1)
    fig.savefig(path)
    plt.close(fig)


def staircase_figure(path):
    """Draws a partial tiling with the tiers of its staircase, their anchors and the regions available to the next tile."""
    moves = [(0, "inside", False), (0, "inside", True), (2, "inside", True)]
    values = {X: 1.6, sp.Symbol("s0"): 0.3, sp.Symbol("s1"): 0.22, sp.Symbol("s2"): 0.14}
    tiers, tiles, _, _ = replay(moves)
    concrete = [tuple(float(sp.sympify(c).subs(values)) for c in tile) for tile in tiles]
    fig, ax = plt.subplots(figsize=(2.6, 2.6))
    for t in tiers:
        ax_, ay, floor, wall = (float(sp.sympify(c).subs(values)) for c in (t.ax, t.ay, t.floor, t.wall))
        ax.add_patch(Rectangle((ax_, ay), floor, wall, fc="none", hatch="//", lw=0, ec="lightgray"))
    draw(ax, concrete)
    for k, t in enumerate(tiers):
        ax_, ay, floor, wall = (float(sp.sympify(c).subs(values)) for c in (t.ax, t.ay, t.floor, t.wall))
        ax.add_patch(Rectangle((ax_, ay), 1 - ax_, wall, fc="none", ec="k", lw=0.4))
        ax.plot([ax_], [ay], marker="o", mfc="none", mec="k", ms=5)
        ax.text(ax_ + 0.02, ay + 0.02, f"$T_{k}$", fontsize=7, va="bottom", ha="left")
    fig.tight_layout(pad=0.2)
    fig.savefig(path)
    plt.close(fig)


def main():
    """Generates all figures."""
    three = tilings(3)
    four = tilings(4)
    assert len(distinct(three)) == 3 and len(distinct(four)) == 11
    grid([t for _, t, _ in three], 7, OUT / "three-tiles.svg", [f"{v:.4f}" for v, _, _ in three])
    picks = distinct(four)
    grid([t for _, t, _ in picks], 6, OUT / "four-tiles.svg", [f"{v:.4f}" for v, _, _ in picks])
    cubic = [(v, t, m) for v, t, m in four if abs(v - 1.5436890127) < 1e-6]
    grid([t for _, t, _ in cubic], len(cubic), OUT / "shared-cubic.svg")
    staircase_figure(OUT / "staircase.svg")
    catalogue(5, 9, OUT / "five-tiles.svg", 0.72)
    catalogue(6, 14, OUT / "six-tiles.svg", 0.47)
    print("three tiles:", [(round(v, 6), m) for v, _, m in three])
    print("tilings with four tiles:", len(four), "sharing the cubic:", len(cubic))


if __name__ == "__main__":
    main()
