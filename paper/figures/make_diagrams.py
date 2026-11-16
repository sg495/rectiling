# SPDX-License-Identifier: LGPL-3.0-or-later
"""Generates the explanatory diagrams of the paper.

Every diagram is drawn from tilings found by the search, read from the listings in the data folder, or from exact solutions of the system of a record; the tiles are drawn by the figure generator and the annotations are added on top.
"""

import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import sympy as sp
from matplotlib.patches import FancyArrowPatch, Rectangle
from matplotlib.path import Path as MplPath
from matplotlib.transforms import offset_copy

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


def continue_floor(ax, x, y, width=1.1):
    """Continues a floor beyond its right end by two dots as thick as the floor."""
    for k in (1, 2):
        shift = offset_copy(ax.transData, fig=ax.figure, x=2.2 * width * k, y=0, units="points")
        ax.plot([x], [y], marker="s", ms=width, mfc="k", mec="k", mew=0, transform=shift, zorder=4, clip_on=False)


def mark_anchors(ax, tiers, size=4.0, chosen=None, flags=False, open_floors=True):
    """Marks the anchors of a staircase, in black for a chosen one; with flags, the floors are drawn thick, a red cross is drawn on the anchor of a stale tier and, unless disabled, the floor of a tier that is neither started nor last is continued by two dots."""
    for j, t in enumerate(tiers):
        ax.plot([t.ax], [t.ay], marker="o", mfc="k" if t is chosen else "w", mec="k", ms=size, zorder=6)
        if flags:
            ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
        if flags and t.stale:
            ax.plot([t.ax], [t.ay], marker="x", color="red", ms=1.2 * size, mew=0.9, zorder=7)
        if flags and open_floors and not t.started and j < len(tiers) - 1:
            continue_floor(ax, t.ax + t.floor, t.ay)


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
    ax.set_xlim(-0.16, 1.14)
    ax.set_ylim(-0.12, 1.06)
    for j, t in enumerate(tiers):
        ax.add_patch(Rectangle((t.ax, t.ay), t.floor, t.wall, fc="none", hatch="//", lw=0, ec="lightgray", zorder=1))
        ax.plot([t.ax, 1], [t.ay + t.wall, t.ay + t.wall], color="0.5", lw=0.5, ls=(0, (3, 2)), zorder=3)
        ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
        ax.plot([t.ax, t.ax], [t.ay, t.ay + t.wall], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
        ax.text(t.ax - 0.018, t.ay - 0.02, f"$(a_{j}, b_{j})$", fontsize=6.3, ha="right", va="top", zorder=7)
        ax.text(t.ax + t.floor / 2, t.ay + 0.016, f"$L_{j}$", fontsize=7.5, ha="center", va="bottom", zorder=7)
        ax.text(t.ax + 0.016, t.ay + t.wall / 2, f"$M_{j}$", fontsize=7.5, ha="left", va="center", zorder=7)
        ax.text(1.03, t.ay + t.wall / 2, f"$T_{j}$", fontsize=9, ha="left", va="center", color="0.3", zorder=7)
    mark_anchors(ax, [Tier(t.ax, t.ay, t.floor, t.wall) for t in tiers], size=5.5)
    fig.tight_layout(pad=0.1)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def fits_figure(path, value, witness):
    """Draws one placement of each fit from the record of a listed tiling, with the floor and the wall of its tier."""
    tiles, sts = stages(value, witness)
    moves = moves_of(witness)
    fig, axes = plt.subplots(1, 4, figsize=(6.6, 2.0))
    chosen = []
    picks = sorted((max((k for k, (_, f, _) in enumerate(moves) if f == fit), key=lambda k: min(tiles[k][2], tiles[k][3])), fit) for fit in CODES.values())
    for ax, (k, fit) in zip(axes, picks):
        i = moves[k][0]
        t = sts[k][i]
        x, y, w, h = tiles[k]
        narrow, low = w < t.floor - EPS, h < t.wall - EPS
        assert abs(x - t.ax) < EPS and abs(y - t.ay) < EPS and w <= t.floor + EPS and h <= t.wall + EPS
        assert (narrow, low) == (fit in ("inside", "full-height"), fit in ("inside", "full-width")), (fit, k)
        draw(ax, tiles[: k + 1])
        for u in sts[k]:
            ax.plot([u.ax, 1], [u.ay + u.wall, u.ay + u.wall], color="0.4", lw=0.5, ls=(0, (3, 2)), zorder=4)
        ax.add_patch(Rectangle((t.ax, t.ay), t.floor, t.wall, fc="none", hatch="//", lw=0, ec="0.45", zorder=3))
        ax.add_patch(Rectangle((x, y), w, h, fc="none", ec="k", lw=0.6, zorder=5))
        ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
        ax.plot([t.ax, t.ax], [t.ay, t.ay + t.wall], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
        mark_anchors(ax, [Tier(u.ax, u.ay, u.floor, u.wall) for u in sts[k + 1]], size=3.6)
        ax.set_title(f"placement {k + 1}: {FIT_NAMES[fit]}", fontsize=7, pad=3)
        chosen.append((fit, k + 1, i, len(sts[k]), len(sts[k + 1])))
    fig.tight_layout(pad=0.2, w_pad=0.5)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return chosen


def rules_figure(path, value, witness):
    """Draws the staircases of a listed tiling that carry the most flags, marking stale tiers and started floors."""
    tiles, sts = stages(value, witness)
    ranked = sorted(range(1, len(sts) - 1), key=lambda k: (-any(r != "stale" for _, r in excluded(sts[k])), -any(t.stale for t in sts[k]), -len(sts[k]), k))
    picks = sorted(set(ranked[:3]) | {5})
    fig, axes = plt.subplots(1, len(picks), figsize=(6.8, 1.95))
    notes = []
    for ax, k in zip(axes, picks):
        draw(ax, tiles[:k])
        outline_rest(ax, tiles[k:])
        for j, t in enumerate(sts[k]):
            ax.text(t.ax + 0.025, t.ay + 0.022, f"$T_{j}$", fontsize=7, ha="left", va="bottom", zorder=7)
        mark_anchors(ax, sts[k], size=4.6, flags=True)
        ax.set_title(f"after {k} placement{'' if k == 1 else 's'}", fontsize=7, pad=3)
        notes.append((k, [(j, t.stale, t.started) for j, t in enumerate(sts[k])], excluded(sts[k]), moves_of(witness)[k]))
    fig.tight_layout(pad=0.2, w_pad=0.5)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
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
    fig.tight_layout(pad=0.6, w_pad=0.4)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
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
            ax.plot([t.ax, t.ax + t.floor], [t.ay, t.ay], color="k", lw=1.1, solid_capstyle="butt", zorder=4)
            if ext:
                continue_floor(ax, t.ax + t.floor, t.ay)
            if not ext and first is None:
                first = j
        assert first == moves[k][0], (k, first, moves[k])
        mark_anchors(ax, sts[k], size=3.6, chosen=sts[k][first], flags=True, open_floors=False)
        ax.set_title("no placement" if k == 0 else f"after {k} placement{'' if k == 1 else 's'}", fontsize=6, pad=2)
    fig.tight_layout(pad=0.15, w_pad=0.3)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
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


def record_of(tiles):
    """Returns the witness of a tiling of the unit square given by the coordinates of its tiles, by placing at each stage the tile at the anchor of the first tier whose floor does not extend."""
    tiers = (Tier(0.0, 0.0, 1.0, 1.0),)
    codes = {v: k for k, v in CODES.items()}
    words = []
    left = list(tiles)
    while tiers:
        i = next(j for j, t in enumerate(tiers) if not extends(tiles, t.ax + t.floor, t.ay))
        t = tiers[i]
        tile = next(r for r in left if abs(r[0] - t.ax) < EPS and abs(r[1] - t.ay) < EPS)
        left.remove(tile)
        _, _, w, h = tile
        narrow, low = w < t.floor - EPS, h < t.wall - EPS
        fit = "inside" if narrow and low else "full-height" if narrow else "full-width" if low else "full"
        words.append(f"{i}{codes[fit]}{'T' if h > w else 'W'}")
        new = [Tier(u.ax, u.ay, u.floor, u.wall, True, u.started) for u in tiers[:i]]
        if not low and i > 0:
            new[i - 1] = Tier(new[i - 1].ax, new[i - 1].ay, new[i - 1].floor + w, new[i - 1].wall, False, new[i - 1].started)
        if fit == "inside":
            new += [Tier(t.ax, t.ay + h, w, t.wall - h), Tier(t.ax + w, t.ay, t.floor - w, h, False, True)]
        elif fit == "full-height":
            new.append(Tier(t.ax + w, t.ay, t.floor - w, t.wall, False, True))
        elif fit == "full-width":
            new.append(Tier(t.ax, t.ay + h, t.floor, t.wall - h))
        rest = list(tiers[i + 1 :])
        if not narrow and rest:
            rest[0] = Tier(rest[0].ax, rest[0].ay, rest[0].floor, rest[0].wall + h, rest[0].stale, rest[0].started)
        tiers = tuple(new + rest)
    assert not left
    return " ".join(words)


def regenerated(coordinates, side, proportion):
    """Returns the tiles that the figure generator computes from the record of a tiling given by integer coordinates, checking that they are the given ones."""
    given = [tuple(sp.Rational(c, side) for c in tile) for tile in coordinates]
    witness = record_of([tuple(float(c) for c in tile) for tile in given])
    tiles = witness_tiles(str(sp.Rational(proportion).evalf(30)), witness)
    assert all(abs(a - float(b)) < 1e-9 for t, g in zip(sorted(tiles), sorted(tuple(float(c) for c in g) for g in given)) for a, b in zip(t, g))
    return tiles, witness


SPORADIC_SIX = ([(0, 0, 75, 45), (75, 0, 30, 50), (72, 50, 33, 55), (0, 45, 36, 60), (36, 45, 36, 60), (72, 45, 3, 5)], 105, sp.Rational(5, 3))
SPORADIC_NINE = (
    [(0, 0, 2560, 800), (2560, 0, 480, 1536), (2100, 1536, 470, 1504), (2570, 1536, 470, 1504)]
    + [(700 * k, 800, 700, 2240) for k in range(3)]
    + [(2100, 800, 230, 736), (2330, 800, 230, 736)],
    3040,
    sp.Rational(16, 5),
)


def sporadic_figure(path):
    """Draws the two sporadic tilings of proportions 5/3 with six tiles and 16/5 with nine, from their records."""
    fig, axes = plt.subplots(1, 2, figsize=(3.6, 1.95))
    out = []
    for ax, (coordinates, side, proportion), label in zip(axes, (SPORADIC_SIX, SPORADIC_NINE), ("$5/3$", "$16/5$")):
        tiles, witness = regenerated(coordinates, side, proportion)
        draw(ax, tiles)
        ax.set_title(label, fontsize=7, pad=2)
        out.append(witness)
    fig.tight_layout(pad=0.3)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return out


def classes(n):
    """Reads the classes of tilings under symmetry listed by the search for n tiles, as triples of a proportion, the size of the class and a witness."""
    fits = {"inside": "i", "full height": "h", "full width": "w", "full": "f"}
    values = [v for v, _ in listing(n)]
    out = []
    for block in re.split(r"(?m)^class \d+: ", (DATA / f"classes-{n}.txt").read_text())[1:]:
        lines = block.splitlines()
        lines = [lines[0]] + [line for line in lines[1:] if line.startswith("  ")]
        approx = float(lines[0].split("proportion ")[1].split(",")[0])
        value = min(values, key=lambda v: abs(float(v) - approx))
        size = int(lines[1].split("=")[1].split(",")[0])
        words = []
        for line in lines:
            if "(tier" in line:
                orientation = line.split(",")[4].split("(")[0].strip()
                tier, fit = line.split("(tier ")[1].rstrip(")").split(", ")
                words.append(f"{tier}{fits[fit]}{'T' if orientation == 'tall' else 'W'}")
        out.append((value, size, " ".join(words)))
    return out


def classes_figure(path, n, columns, size):
    """Draws one tiling for each class of tilings under the symmetries of the square, from the records listed by the search."""
    items = classes(n)
    rows = -(-len(items) // columns)
    fig, axes = plt.subplots(rows, columns, figsize=(size * columns, size * 1.2 * rows), squeeze=False)
    for ax in axes.flat:
        ax.axis("off")
    total = 0
    for ax, (value, count, witness) in zip(axes.flat, items):
        tiles = witness_tiles(value, witness)
        assert abs(sum(w * h for _, _, w, h in tiles) - 1) < 1e-9
        draw(ax, tiles)
        ax.set_title(f"{float(value):.4f} ({count})", fontsize=5.2 if size < 0.7 else 6.5, pad=1.5)
        total += count
    fig.tight_layout(pad=0.15, h_pad=0.3, w_pad=0.1)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return len(items), total


def components_of(tiles):
    """Returns the connected components of the union of the horizontal sides of the tiles, as triples of the two ends and the height."""
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


def network_figure(path, tiles):
    """Draws a tiling with the components of its horizontal sides, and the network of the tiling with the edge joining its poles."""
    comps = components_of(tiles)
    names = {c: f"v_{k}" for k, c in enumerate(c for c in comps if 0 < c[2] < 1 - EPS)}
    names.update({c: "t" for c in comps if c[2] < EPS})
    names.update({c: "s" for c in comps if c[2] > 1 - EPS})
    nodes = {c: ((c[0] + c[1]) / 2, c[2]) for c in comps}
    fig, (left, right) = plt.subplots(1, 2, figsize=(4.6, 2.3))
    draw(left, tiles)
    for x, y, w, h in tiles:
        left.plot([x + w / 2, x + w / 2], [y, y + h], color="k", lw=0.4)
    for c in comps:
        left.plot([c[0], c[1]], [c[2], c[2]], color="k", lw=1.1, solid_capstyle="butt")
        left.text(c[1] + 0.03 if c[1] > 1 - EPS else c[0] - 0.03, c[2], f"${names[c]}$", fontsize=7, va="center", ha="left" if c[1] > 1 - EPS else "right")
    left.set_xlim(-0.14, 1.14)
    for k, (x, y, w, h) in enumerate(tiles):
        top = next(c for c in comps if abs(c[2] - y - h) < EPS and c[0] - EPS <= x and x + w <= c[1] + EPS)
        bottom = next(c for c in comps if abs(c[2] - y) < EPS and c[0] - EPS <= x and x + w <= c[1] + EPS)
        bend = -1.6 * (x + w / 2 - (nodes[top][0] + nodes[bottom][0]) / 2) / max(h, 0.35)
        right.annotate("", xy=nodes[bottom], xytext=nodes[top], arrowprops=dict(arrowstyle="-|>", color=COLOURS[k % len(COLOURS)], lw=1.2, shrinkA=3, shrinkB=3, mutation_scale=7, connectionstyle=f"arc3,rad={bend:.3f}"))
    top, bottom = next(c for c in comps if c[2] > 1 - EPS), next(c for c in comps if c[2] < EPS)
    (sx, sy), (tx, ty), reach = nodes[top], nodes[bottom], 0.95
    curve = MplPath([(tx + 0.03, ty), (tx + reach, ty), (sx + reach, sy), (sx + 0.03, sy)], [MplPath.MOVETO, MplPath.CURVE4, MplPath.CURVE4, MplPath.CURVE4])
    right.add_patch(FancyArrowPatch(path=curve, arrowstyle="-|>", color="k", lw=0.6, ls="--", mutation_scale=7))
    right.text(sx + 0.75 * reach + 0.03, 0.5, "$e_0$", fontsize=7, va="center", ha="left")
    for c, (x, y) in nodes.items():
        right.plot([x], [y], marker="o", mfc="w", mec="k", ms=4, zorder=3)
        right.text(x - 0.06, y, f"${names[c]}$", fontsize=7, va="center", ha="right")
    right.set_xlim(-0.14, 1.52)
    right.set_ylim(-0.07, 1.07)
    right.set_aspect("equal")
    right.axis("off")
    fig.tight_layout(pad=0.3)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return len(comps)


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
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def persistence_figure(path, value, witness):
    """Draws a listed tiling and the tilings with three, four, five and seven more tiles obtained by cutting a tile into four, by the pinwheel and by cutting a tile into six and into eight, each from its record, the tiles of the listed tiling keeping their colours and the new tiles being grey."""
    tiles = witness_tiles(value, witness)
    k = max(range(len(tiles)), key=lambda j: tiles[j][2] * tiles[j][3])
    a, b, w, h = tiles[k]
    kept = {j: t for j, t in enumerate(tiles) if j != k}
    four = [(a + w * u / 2, b + h * v / 2, w / 2, h / 2) for u in range(2) for v in range(2)]
    six = [(a, b, 2 * w / 3, 2 * h / 3)] + [(a + w * u / 3, b + h * v / 3, w / 3, h / 3) for u, v in ((2, 0), (2, 1), (2, 2), (1, 2), (0, 2))]
    eight = [(a, b, 3 * w / 4, 3 * h / 4)] + [(a + w * u / 4, b + h * v / 4, w / 4, h / 4) for u, v in ((3, 0), (3, 1), (3, 2), (3, 3), (2, 3), (1, 3), (0, 3))]
    x = float(value)
    p = x / (x + 1)
    scale = (x - 1) / (x + 1)
    pinwheel = [(0, 0, p, 1 - p), (p, 0, 1 - p, p), (1 - p, p, p, 1 - p), (0, 1 - p, 1 - p, p)]
    copy = {j: (1 - p + scale * u, 1 - p + scale * v, scale * c, scale * d) for j, (u, v, c, d) in enumerate(tiles)}
    cases = ((dict(enumerate(tiles)), []), (kept, four), (copy, pinwheel), (kept, six), (kept, eight))
    records = []
    fig, axes = plt.subplots(1, 5, figsize=(7.2, 1.62))
    for ax, (old, new) in zip(axes, cases):
        built = list(old.values()) + new
        record = record_of(built)
        drawn = witness_tiles(value, record)
        assert len(drawn) == len(built) and all(any(max(abs(c - d) for c, d in zip(t, g)) < 1e-8 for g in built) for t in drawn)
        for t in drawn:
            index = next((j for j, g in old.items() if max(abs(c - d) for c, d in zip(t, g)) < 1e-8), None)
            ax.add_patch(Rectangle(t[:2], t[2], t[3], fc="#d9d9d9" if index is None else COLOURS[index], ec="k", lw=0.35))
        ax.add_patch(Rectangle((0, 0), 1, 1, fc="none", ec="k", lw=0.6))
        ax.set_xlim(-0.05, 1.05)
        ax.set_ylim(-0.05, 1.05)
        ax.set_aspect("equal")
        ax.axis("off")
        records.append(record)
    for ax, title in zip(axes, ("a tiling", "three more tiles", "four more tiles (square)", "five more tiles", "seven more tiles")):
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.6)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)
    return records


def steps_figure(path):
    """Draws three tilings found by the search whose proportions do not recur with one or two more tiles in the square, or with four more in the other two main rectangles."""
    cases = (("2.0", "0wW 0fW", 1, 1, "$2 \\in P_2(1)$"), ("1.5", "0fW", 3, 2, "$3/2 \\in P_1(3/2)$"), ("4.0", "0wW 0fW", 2, 1, "$4 \\in P_2(2)$"))
    fig, axes = plt.subplots(1, 3, figsize=(4.6, 1.3), gridspec_kw={"width_ratios": [width / height for _, _, width, height, _ in cases]})
    for ax, (value, witness, width, height, title) in zip(axes, cases):
        tiles = [tuple(c / height for c in tile) for tile in witness_tiles(value, witness, width, height)]
        draw(ax, tiles, width / height, 1.0)
        ax.set_ylim(-0.05, 1.05)
        ax.set_title(title, fontsize=7, pad=3)
    fig.tight_layout(pad=0.2, w_pad=0.8)
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
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
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
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
    fig.savefig(path, bbox_inches="tight", pad_inches=0.04)
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
    value, witness = next((v, w) for v, w in listing(5) if w == "0iW 0wW 1wT 1fT 0fW")
    print("persistence:", value, witness, persistence_figure(OUT / "persistence.svg", value, witness))
    steps_figure(OUT / "steps.svg")
    print("pinwheel:", pinwheel_figure(OUT / "pinwheel.svg"))
    print("two tiles:", two_tiles_figure(OUT / "two-tiles.svg"))
    print("sporadic:", sporadic_figure(OUT / "sporadic.svg"))
    print("classes:", classes_figure(OUT / "classes-4.svg", 4, 8, 0.8), classes_figure(OUT / "classes-5.svg", 5, 11, 0.6))
    tiles, witness = regenerated(*SPORADIC_SIX)
    print("network:", witness, network_figure(OUT / "network.svg", tiles), "components")


if __name__ == "__main__":
    main()
