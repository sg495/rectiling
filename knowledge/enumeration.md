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

## Canonical order

Each tiling admits many compatible orders, and the search must visit it once.
The canonical order places, at every step, the tile at the lowest-numbered tier whose tile is *ready*, meaning that it fits on the floor and against the wall as they currently stand.

This rule is enforced locally.
Placing a tile at tier i asserts that no tile at a tier j < i was ready, so every such tier becomes *stale*: no tile can be placed on it until its floor grows, which happens when a tile of full height is placed at the next tier.
Staleness is cleared when the floor grows, and when a tile is placed at the tier, since the anchor then moves.

## One sequence per mosaic class

The linear system that determines the sizes of the tiles (see [solving.md](solving.md)) depends only on which tiles border each maximal segment of the tiling, and not on the order in which the junctions on the two sides of a segment alternate; see [theory.md](theory.md).
Tilings that agree in this respect form a *mosaic class*, and it is enough to visit one placement sequence per class.

The staircase construction never distinguishes the order of junctions along a vertical segment, but it does along a horizontal one: a tile standing on a segment can be placed before or after the tiles hanging below the segment are complete.
The search keeps the second alternative only.
A floor is *started* once a tile narrower than it stands on it, and a tile of full height may not be placed at a tier when the floor of the previous tier is started, since that would extend a segment on which tiles already stand.
With this rule every mosaic class has exactly one placement sequence.

The numbers of placement sequences for n = 1 to 12 are accordingly the Baxter numbers 1, 2, 6, 22, 92, 422, 2074, 10754, 58202, 326240, 1882960, 11140560 ([OEIS A001181](https://oeis.org/A001181)), which count mosaic classes.
A tiling in which four tiles meet at a point belongs to the closure of two classes and is found through either.

## Orientations and symmetry

Each tile is either wide or tall, so a sequence of n placements is examined with 2ⁿ orientation vectors.
Transposition of the plane maps tilings of a main rectangle of aspect ratio w to tilings of one of aspect ratio 1/w, exchanging wide and tall tiles and preserving the proportion.
For a square, it is therefore enough to consider tilings whose bottom-left tile is wide, which leaves 2ⁿ⁻¹ orientation vectors per sequence.
