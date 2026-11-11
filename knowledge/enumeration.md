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

This rule is enforced locally by locks.
Placing a tile at tier i asserts that no tile at a tier j < i was ready, so every such tier is locked at the current length of its floor: the tile eventually placed there must be strictly wider than that length.
A locked tier is *stale* until its floor grows, which happens when a tile of full height is placed at the next tier, and no tile can be placed on a stale tier.
Once the floor has grown, the tile placed there is either of full width, or narrower but strictly wider than the length recorded by the lock.
A lock is cleared when a tile is placed at the tier, since the anchor then moves.

The wall of a locked tier cannot grow before its tile is placed: that would require a full-width tile at the previous tier, which is itself locked and can only become ready after a full-height tile at the locked tier.
Hence the width condition captures readiness exactly, and each concrete tiling corresponds to exactly one placement sequence.

## What a placement sequence determines

A placement sequence fixes which tiles touch along each segment, and the order of the junctions on the two sides of each horizontal segment, but not the order of junctions on the two sides of a vertical segment.
A tiling in which four tiles meet at a point belongs to the sequence in which the vertical segment through that point is unbroken.
The sequences are therefore coarser than generic rectangulations (1, 2, 6, 24, 116, 642, … for n tiles) and finer than diagonal rectangulations (1, 2, 6, 22, 92, 422, …): their numbers are 1, 2, 6, 23, 104, 530, 2958, 17734, 112657 for n = 1 to 9.

## Orientations and symmetry

Each tile is either wide or tall, so a sequence of n placements is examined with 2ⁿ orientation vectors.
Transposition of the plane maps tilings of a main rectangle of aspect ratio w to tilings of one of aspect ratio 1/w, exchanging wide and tall tiles and preserving the proportion.
For a square, it is therefore enough to consider tilings whose bottom-left tile is wide.
