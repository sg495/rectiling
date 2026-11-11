# Staircase enumeration

The search enumerates tilings by placing tiles one at a time, from the bottom-left corner of the main rectangle towards the top-right, so that the region still to be filled always has the shape of a staircase.

## The staircase

After any number of placements, the unfilled region is a union of *tiers*, numbered from the top-left to the bottom-right.
Each tier has an *anchor*, the concave corner of the filled region at its bottom-left; a *floor*, the horizontal segment running right from the anchor to the next anchor or to the right side of the main rectangle; and a *wall*, the vertical segment running up from the anchor to the floor of the previous tier or to the top side.
Initially there is a single tier, whose floor is the bottom side and whose wall is the left side.

Every tiling can be built in this way: say that a tile precedes another when it lies to its left or below it along a shared segment, and place the tiles in any order compatible with this relation.
The next tile always has its bottom-left corner at an anchor, is at most as wide as the floor there and at most as high as the wall.

## The four fits

A tile placed at the anchor of tier i, with floor of length L and wall of height M, is of one of four kinds.

- **Inside**: narrower than L and lower than M. The tier is replaced by two tiers, one above the tile and one to its right.
- **Full height**: narrower than L and of height M. The anchor moves right, and the floor of tier i − 1 grows by the width of the tile.
- **Full width**: of width L and lower than M. The anchor moves up, and the wall of tier i + 1 grows by the height of the tile.
- **Full**: of width L and height M. The tier disappears; the floor of tier i − 1 grows by L and the wall of tier i + 1 grows by M.

The number of tiers grows by one with an inside placement and shrinks by one with a full placement, so a complete tiling has exactly one more full placement than inside placements, and a partial tiling can be abandoned when fewer tiles remain than there are tiers.

## The two placement rules

Each tiling admits many compatible orders, and tilings that differ only in how the corners of tiles alternate along a segment lead to the same linear system (see [solving.md](solving.md) and [theory.md](theory.md)).
The search restricts the placement sequences by two rules, each recorded by a flag on the tiers.

- **Stale tiers.** When a tile is placed at tier i, every tier j < i becomes *stale*. A stale tier ceases to be stale when its floor grows, which happens when a tile of full height is placed at the next tier, and the flag is cleared when a tile is placed at the tier, since the anchor then moves. No tile may be placed at a stale tier.
- **Started floors.** The floor of a tier is *started* when the tier lies to the right of a tile that stands on the same segment: the tier created to the right of an inside tile, and the tier whose anchor has been moved right by a full-height tile. A tile of full height, or a full tile, may not be placed at a tier when the floor of the previous tier is started, since it would lengthen a floor on which tiles already stand.

A sequence of placements that obeys both rules is *admissible*.

## Why the rules lose nothing

Say that the floor of a tier *extends*, in a given tiling, when the horizontal segment carrying the floor continues to the right beyond the end of the floor: the tile lying below that segment just to the right of the end of the floor has its top side at the level of the floor.
Every tiling is produced by the admissible sequence that places, at every step, the tile at the anchor of the first tier whose floor does not extend.
Such a tier exists, because the floor of the last tier ends at the right side of the main rectangle, and the tile at its anchor fits the tier.
Along this sequence a stale tier always has a floor that extends, and a started floor never does, so both rules are obeyed.
In effect, the tiles standing on a horizontal segment are placed only after all the tiles hanging below it.

This order is not the one that places the tile at the first tier whose tile fits: with the rule on started floors, that order can break the rules.

## Why the rules are needed

The constraints attached to a sequence say only that every tile has positive size; none says that a tile placed inside is narrower than its floor or lower than its wall.
For an admissible sequence these facts follow: a floor that has become non-positive and is started or last, or a wall that has become non-positive behind stale tiers, stays so under every further admissible placement with positive tiles, so the staircase could never be emptied.
The two rules are therefore part of what makes every solution a genuine tiling, and not only a device to avoid repetitions.

Both statements, that every solution of an admissible complete sequence is a tiling and that every tiling arises from one, are proved formally in the Lean development.

## One sequence per mosaic class

The staircase construction never distinguishes the order of corners along a vertical segment, and the rule on started floors fixes it along horizontal segments.
The numbers of complete admissible sequences of n placements, for n = 1 to 13, are the Baxter numbers 1, 2, 6, 22, 92, 422, 2074, 10754, 58202, 326240, 1882960, 11140560, 67329992 ([OEIS A001181](https://oeis.org/A001181)), which count the mosaic classes of tilings.
This agreement has been observed by computation; that each mosaic class has exactly one admissible sequence has not been proved here.
A repeated sequence would in any case affect only the amount of work, and not the set of proportions found.

The bound on the number of tiles still to place, by which a partial sequence is abandoned when fewer tiles remain than there are tiers, only prunes sequences that cannot be completed.

## Orientations and symmetry

Each tile is either wide or tall, so a sequence of n placements is examined with 2ⁿ orientation vectors.
Transposition of the plane maps tilings of a main rectangle of aspect ratio w to tilings of one of aspect ratio 1/w, exchanging wide and tall tiles and preserving the proportion.
For a square, it is therefore enough to consider tilings whose bottom-left tile is wide, which leaves 2ⁿ⁻¹ orientation vectors per sequence.
