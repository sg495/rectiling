# Counting the tilings

The search of [enumeration.md](enumeration.md) and [solving.md](solving.md) was built to count proportions.
This note describes how it is made to count the tilings themselves, in three ways, records the values obtained, the checks they passed, and what was found when studying them.
Statements are labelled as in [analysis.md](analysis.md): *Proved* (the proof is given here, but nothing is formalised or reviewed), *Argued* (an argument is sketched and the data agree), *Conjecture* (agrees with all available data, range stated) or *Heuristic* (loose numerical observation).

## Definitions

- A *tiling* is a set of n rectangles with pairwise disjoint interiors whose union is the unit square, all of the same proportion x ≥ 1, each in either orientation. Two tilings are equal when they are the same set of rectangles.
- t(n) is the number of tilings with exactly n tiles.
- b(n) is the number of tilings up to the eight symmetries of the square. This is the sequence that the comments of [OEIS A359146](https://oeis.org/A359146) ask for, with b(1) = 1, b(2) = 1, b(3) = 3 and b(4) > 11 on record.
- The *bag* of a tiling is its proportion together with the multiset of the short sides of its tiles; two tilings have the same bag when the tiles of one can be rearranged, and turned individually, into the other. c(n) is the number of distinct bags.
- a(n) is the number of proportions, so that a(n) ≤ c(n) ≤ b(n) ≤ t(n) ≤ 8·b(n).
- s(n) is the number of tilings by squares, the tilings of proportion one.
- A *crossing* is a point at which four tiles meet.
- A *record* is what the search reports: an admissible placement sequence, an orientation for every tile and a proportion at which all tiles have positive size. T(n) is the number of records for the square whose first tile is wide, the column *tilings* of the table of work in [results.md](results.md).

## Values

| n  | a(n)     | c(n)    | b(n)       | t(n)       |
| -- | -------- | ------- | ---------- | ---------- |
| 1  | 1        | 1       | 1          | 1          |
| 2  | 1        | 1       | 1          | 2          |
| 3  | 3        | 3       | 3          | 14         |
| 4  | 11       | 11      | 16         | 89         |
| 5  | 51       | 51      | 121        | 830        |
| 6  | 245      | 250     | 976        | 7278       |
| 7  | 1372     | 1419    | 9051       | 70410      |
| 8  | 8522     | 8877    | 88982      | 703606     |
| 9  | 58347    | 61147   | 914261     | 7280599    |
| 10 | 433926   | 456652  | 9666313    | 77188146   |
| 11 | 3446981  | 3636350 | 104584332  | 836069812  |
| 12 | 28799493 |         | 1152003122 | 9213388789 |

The values of a(n) are those of [results.md](results.md).
All the other values were computed here on 11 November 2026, on the machine described there, and none of them was on record before, apart from b(1), b(2) and b(3).
How each was checked is described under *Validation*; in short, everything up to n = 8 was confirmed by an independent program, everything up to n = 10 by a second method inside the search, and the values for n = 11 and 12 rest on the search alone.
The bags were not counted for n = 12.

## From records to tilings

A record is not a tiling, and four things separate the two.
Each is handled exactly.

### One sequence represents each tiling

Call the floor of a tier *extending*, in a given tiling, when the tile lying just to the right of the end of the floor and just below its level has its top side at that level.
The *representative sequence* of a tiling places, at every step, the tile at the anchor of the first tier whose floor does not extend.
It is admissible ([enumeration.md](enumeration.md)), it is determined by the tiling, and the tiling is the unique solution of its linear system at the proportion, provided the system is not singular.
The search therefore counts the records whose sequence is the representative sequence of the tiling they describe: these correspond one to one to the tilings with the given orientations.

For each record the search builds the tiling, constructs its representative sequence from the exact order of the coordinates, and compares it with the sequence of the record.
This does not assume that each mosaic class has exactly one admissible sequence; that statement is in fact proved below, and the search checks the criterion that follows from it on every record.

### Crossings

A tiling with crossings is the solution of several systems, one for each way of regarding the two segments through a crossing: the horizontal one passes and the vertical one is broken, or conversely.
In a record, the lower right tile at a crossing is placed either before or after the upper left tile.
A record is representative exactly when the lower right tile comes first at every crossing (proved below), so the other records of the same tiling are discarded.
The search finds the crossings of every record and tallies records and tilings by their number; a tiling with k crossings turns out to have exactly 2^k records for each orientation vector, which is also argued below.

### Squares

For x = 1 every tile is both wide and tall, and a tiling has a record for every orientation vector.
Only the records with all tiles marked wide are examined at x = 1; the others are counted and set aside.
The number of records set aside must be 2ⁿ⁻¹ − 1 times the number examined, which is checked.

### Transposition

For a square the search examines only records whose first tile is wide.
The first tile is the tile at the bottom left corner, and transposition of the plane fixes that corner and exchanges wide and tall tiles.
For x > 1 it is therefore a bijection between the tilings whose corner tile is wide and those whose corner tile is tall, with no fixed point, and the tilings of the first kind are counted twice.
For x = 1 nothing is doubled.
With E the number of representative records at x > 1 and Q the number at x = 1 with all tiles wide, t(n) = 2E + Q.
For a main rectangle that is not a square the search examines both orientations of the first tile, and t = E + Q.

### Classes under symmetry, in two ways

Each symmetry g of the square maps a tiling to a tiling of the same proportion, with orientations exchanged when g exchanges the axes and x > 1.
The search computes, for every tiling T it examines and every g, the representative sequence of g(T), as a string of bytes that includes the orientations.

- *By representatives.* T is counted when its own string is the smallest of the eight. A string that begins with a tall tile is larger than any that begins with a wide tile, so the smallest string of every class belongs to a tiling that the search examines, and b(n) is the number of tilings counted.
- *By fixed points.* Independently of the strings, T is fixed by g when the set of its rectangles, with orientations, is mapped to itself. The numbers of tilings fixed by each g are accumulated and b(n) is their sum divided by eight (the lemma of Burnside). Tilings whose corner tile is tall are accounted for by conjugation with the transposition, which exchanges the two reflections in the axes and the two quarter turns.

The two counts must agree, and for every tiling and every g the two tests (equal strings, invariant set of rectangles) must give the same answer; disagreements are counted in `inconsistent`.
The search also records the group of symmetries of every tiling.

### Bags

One tiling from each class under symmetry is entered in a table of bags, since symmetric tilings have the same bag.
The key of the table is the proportion with the multiset of the residues of the short sides modulo a prime, and every tiling whose key is already present is compared exactly with the tilings stored under that key.
The count is the number of entries of the table.

## Exact identification

All decisions are exact; floating point serves only to avoid exact work when it certifies a strict inequality.

**Coordinates as elements of the number field.**
For a record with proportion α, every length of the tiling is N(α)/D(α), where D is the determinant of the linear system and N a polynomial with integer coefficients, both produced by the fraction-free elimination of the reference method.
Two lengths of the same record are equal exactly when the minimal polynomial of α divides the difference of their numerators, and otherwise the sign of the difference is determined by the registry of algebraic numbers, which knows which root is meant (interval evaluation, refined until the sign is decided).
Lengths of different records, P/D and P′/D′, are equal exactly when the minimal polynomial divides P·D′ − P′·D.
No canonical form in ℚ[x]/(f) is ever computed, so there are no inverses and no rational coefficients.

**The order of the coordinates.**
Every side of a tile lies on a *line*: a side of the square, or the line through the right or top side of the tile that created it.
Sides that the placement sequence puts on the same line are equal by construction.
The search needs the order of the coordinates of the vertical lines and of the horizontal lines, with equalities.
It first computes enclosures of all coordinates from the interval arithmetic that the default method already performs; if they are pairwise disjoint the order is certified.
Otherwise the record is solved by exact elimination and every pair of coordinates that the enclosures do not separate is compared exactly.
About 6.6% of the records need this for n = 11; with the option `--exact` every comparison is exact.

**Everything else is combinatorial.**
The order of the coordinates turns the tiling into a set of rectangles with small integer corners.
Crossings, the representative sequence, the images under the symmetries and the invariance of the set of rectangles are computed on these integers.
This suffices because a tiling is determined by its proportion, its orientations and its representative sequence, the linear system being non-singular: two tilings with the same integer picture, orientations and proportion are equal.
As a check that does not rely on this, whenever the integer picture of a tiling is invariant under a symmetry the search verifies by exact arithmetic that the coordinates themselves are mapped to one another (xᵢ + x′ᵢ = 1 and the like); failures are counted in `asymmetric`.

**Bags.**
For each proportion a prime p and a root r of the minimal polynomial modulo p are fixed, the same for all threads; evaluating at r is a ring homomorphism, so equal short sides have equal residues N(r)/D(r).
Tilings with different keys therefore have different bags, with certainty.
Tilings with the same key are compared exactly: the short sides are matched greedily, a pair being accepted when P·D′ − P′·D is a multiple of the minimal polynomial, computed in 128-bit integers with a fallback to arbitrary precision.
Residues only limit the pairs that are tried, so a coincidence of residues cannot merge two bags; such coincidences are counted in `collisions` and none has occurred.
A tiling for which the residues cannot be formed is counted in `unresolved`.

**Certification.**
The counts are certified when the counters `singular`, `constant` and `overflows` of the search and `inconsistent`, `asymmetric` and `unresolved` of the census are all zero.
They were zero in every run reported here.

## Further counts

The number of tilings fixed by each symmetry; the two reflections in the axes fix equally many tilings, as do the two reflections in the diagonals and the two quarter turns.

| n  | identity   | each reflection in an axis | half turn | each reflection in a diagonal | each quarter turn | sum / 8    |
| -- | ---------- | -------------------------- | --------- | ----------------------------- | ----------------- | ---------- |
| 1  | 1          | 1                          | 1         | 1                             | 1                 | 1          |
| 2  | 2          | 2                          | 2         | 0                             | 0                 | 1          |
| 3  | 14         | 4                          | 2         | 0                             | 0                 | 3          |
| 4  | 89         | 15                         | 5         | 1                             | 1                 | 16         |
| 5  | 830        | 62                         | 14        | 0                             | 0                 | 121        |
| 6  | 7278       | 234                        | 58        | 2                             | 0                 | 976        |
| 7  | 70410      | 928                        | 138       | 2                             | 0                 | 9051       |
| 8  | 703606     | 3862                       | 510       | 6                             | 2                 | 88982      |
| 9  | 7280599    | 16081                      | 1307      | 9                             | 1                 | 914261     |
| 10 | 77188146   | 68614                      | 5078      | 26                            | 0                 | 9666313    |
| 11 | 836069812  | 295464                     | 13828     | 44                            | 0                 | 104584332  |
| 12 | 9213388789 | 1290691                    | 54517     | 123                           | 21                | 1152003122 |

The number of tilings by their group of symmetries; *one axis* and *one diagonal* add the two conjugate groups.

| n  | none       | one axis | half turn | one diagonal | both axes | both diagonals | quarter turns | all | any symmetry |
| -- | ---------- | -------- | --------- | ------------ | --------- | -------------- | ------------- | --- | ------------ |
| 1  | 0          | 0        | 0         | 0            | 0         | 0              | 0             | 1   | 1            |
| 2  | 0          | 0        | 0         | 0            | 2         | 0              | 0             | 0   | 2            |
| 3  | 8          | 4        | 0         | 0            | 2         | 0              | 0             | 0   | 6            |
| 4  | 64         | 20       | 0         | 0            | 4         | 0              | 0             | 1   | 25           |
| 5  | 712        | 104      | 4         | 0            | 10        | 0              | 0             | 0   | 118          |
| 6  | 6792       | 424      | 36        | 4            | 22        | 0              | 0             | 0   | 486          |
| 7  | 68520      | 1748     | 84        | 4            | 54        | 0              | 0             | 0   | 1890         |
| 8  | 695600     | 7484     | 388       | 12           | 120       | 0              | 2             | 0   | 8006         |
| 9  | 7247672    | 31604    | 1028      | 16           | 278       | 0              | 0             | 1   | 32927        |
| 10 | 77047056   | 135964   | 4444      | 48           | 632       | 2              | 0             | 0   | 141090       |
| 11 | 835468072  | 587824   | 12276     | 88           | 1552      | 0              | 0             | 0   | 601740       |
| 12 | 9210759440 | 2574588  | 51100     | 244          | 3396      | 0              | 20            | 1   | 2629349      |

The number of tilings by squares, of their classes, and of all tilings by the number of crossings.

| n  | by squares | classes | 0          | 1         | 2       | 3      | 4     | 5   | 6  | share with such a point |
| -- | ---------- | ------- | ---------- | --------- | ------- | ------ | ----- | --- | -- | ----------------------- |
| 1  | 1          | 1       | 1          | 0         | 0       | 0      | 0     | 0   | 0  | 0.0000                  |
| 2  | 0          | 0       | 2          | 0         | 0       | 0      | 0     | 0   | 0  | 0.0000                  |
| 3  | 0          | 0       | 14         | 0         | 0       | 0      | 0     | 0   | 0  | 0.0000                  |
| 4  | 1          | 1       | 88         | 1         | 0       | 0      | 0     | 0   | 0  | 0.0112                  |
| 5  | 0          | 0       | 818        | 12        | 0       | 0      | 0     | 0   | 0  | 0.0145                  |
| 6  | 4          | 1       | 7110       | 162       | 6       | 0      | 0     | 0   | 0  | 0.0231                  |
| 7  | 8          | 2       | 69010      | 1356      | 44      | 0      | 0     | 0   | 0  | 0.0199                  |
| 8  | 36         | 6       | 687410     | 15606     | 584     | 6      | 0     | 0   | 0  | 0.0230                  |
| 9  | 105        | 16      | 7115198    | 159036    | 6154    | 204    | 7     | 0   | 0  | 0.0227                  |
| 10 | 384        | 56      | 75338906   | 1783632   | 63918   | 1644   | 46    | 0   | 0  | 0.0240                  |
| 11 | 1340       | 183     | 815392000  | 19947620  | 708926  | 20412  | 854   | 0   | 0  | 0.0247                  |
| 12 | 4975       | 657     | 8975326238 | 229805276 | 8010560 | 235652 | 10782 | 267 | 14 | 0.0258                  |

How the records of the search decompose: T(n), the tilings with first tile wide and x > 1, the further records of the same tilings at crossings, and the records at x = 1 for all orientation vectors; the last column is the number of records whose coordinates needed exact comparison.

| n  | records    | tilings with first tile wide | repeats at four-tile points | records by squares | compared exactly |
| -- | ---------- | ---------------------------- | --------------------------- | ------------------ | ---------------- |
| 1  | 1          | 0                            | 0                           | 1                  | 0                |
| 2  | 1          | 1                            | 0                           | 0                  | 0                |
| 3  | 7          | 7                            | 0                           | 0                  | 0                |
| 4  | 60         | 44                           | 0                           | 16                 | 2                |
| 5  | 421        | 415                          | 6                           | 0                  | 15               |
| 6  | 3981       | 3637                         | 88                          | 256                | 211              |
| 7  | 37219      | 35201                        | 738                         | 1280               | 1909             |
| 8  | 368663     | 351785                       | 8686                        | 8192               | 21974            |
| 9  | 3793179    | 3640247                      | 89444                       | 63488              | 228938           |
| 10 | 40013433   | 38593881                     | 993568                      | 425984             | 2562206          |
| 11 | 432396494  | 418034236                    | 11114130                    | 3248128            | 28685992         |
| 12 | 4758270004 | 4606691907                   | 127825393                   | 23752704           | 329447932        |

Ratios, and the mean number of crossings per tiling with its lower bound.

| n  | t(n)/t(n-1) | t(n)/(2^n M(n)) | 8 b(n)/t(n) | symmetric share | four-tile points per tiling | lower bound | c(n)/a(n) |
| -- | ----------- | --------------- | ----------- | --------------- | --------------------------- | ----------- | --------- |
| 1  |             | 0.5000          | 8.00000     | 1.00000         | 0.00000                     | 0.00000     | 1.0000    |
| 2  | 2.000       | 0.2500          | 4.00000     | 1.00000         | 0.00000                     | 0.00000     | 1.0000    |
| 3  | 7.000       | 0.2917          | 1.71429     | 0.42857         | 0.00000                     | 0.00000     | 1.0000    |
| 4  | 6.357       | 0.2528          | 1.43820     | 0.28090         | 0.01124                     | 0.01124     | 1.0000    |
| 5  | 9.326       | 0.2850          | 1.16627     | 0.14217         | 0.01446                     | 0.00482     | 1.0000    |
| 6  | 8.769       | 0.2787          | 1.07282     | 0.06678         | 0.02391                     | 0.00577     | 1.0204    |
| 7  | 9.674       | 0.2838          | 1.02838     | 0.02684         | 0.02051                     | 0.00506     | 1.0343    |
| 8  | 9.993       | 0.2859          | 1.01173     | 0.01138         | 0.02387                     | 0.00590     | 1.0417    |
| 9  | 10.348      | 0.2882          | 1.00460     | 0.00452         | 0.02362                     | 0.00600     | 1.0480    |
| 10 | 10.602      | 0.2898          | 1.00184     | 0.00183         | 0.02483                     | 0.00639     | 1.0524    |
| 11 | 10.832      | 0.2911          | 1.00072     | 0.00072         | 0.02563                     | 0.00673     | 1.0549    |
| 12 | 11.020      | 0.2920          | 1.00029     | 0.00029         | 0.02676                     | 0.00711     |           |

Here M(n) = 2·(3n)!/((2n+1)!·(n+1)!) as in [analysis.md](analysis.md), and the lower bound is that of the statement on crossings below.

## Validation

- **Published values.** b(1), b(2), b(3) = 1, 1, 3, and b(4) = 16 > 11.
- **Squares.** The numbers of tilings by squares agree with [OEIS A221842](https://oeis.org/A221842) (1, 0, 0, 1, 0, 4, 8, 36, 105, 384, 1340, 4975) and their classes with [OEIS A221841](https://oeis.org/A221841) (1, 0, 0, 1, 0, 1, 2, 6, 16, 56, 183, 657), for all n ≤ 12, and for n ≤ 14 in the search restricted to one orientation (17676 and 69052 tilings, 2277 and 8813 classes for n = 13 and 14). These were found by other authors with other methods, and exercise the treatment of squares, of crossings and of symmetry, since tilings by squares are rich in both.
- **Two counts of the classes.** The count by representatives and the count by fixed points agree for every n ≤ 12, and for the rectangles 2 × 1, 3 × 2 and 5 × 3 with n ≤ 6.
- **Independent implementation.** `tools/reference.py` is a separate program in Python, written from the definitions without knowledge of the Rust code. It solves each system by Gauss–Jordan elimination over ℚ[x]/(f) with canonical elements, enumerates all 2ⁿ orientation vectors without the restriction on the first tile, represents a tiling as a set of rectangles with exact coordinates, removes repetitions by hashing these sets, applies the eight symmetries to the coordinates, and counts orbits both directly and by fixed points. It agrees with the search on t(n), b(n), c(n), the number of tilings fixed by each symmetry, the numbers of tilings by crossings and by squares and on the numbers of tilings, classes and bags of every single proportion, for all n ≤ 8.
- **Without the placement rules.** The same program, run without the rules on stale tiers and started floors (all n! orders of placement, each solution verified to be a genuine tiling by exact tests of containment and disjointness), finds exactly the same sets of tilings for n ≤ 7. This confirms for those n that the rules lose no tiling.
- **Exact comparison throughout.** With `--exact` every record is solved by the reference method and every comparison of coordinates is exact; t(n), b(n), c(n) and all the tables above are unchanged for n ≤ 10.
- **Records.** For every n ≤ 12, T(n) equals the sum over the tilings with first tile wide of 2^k, plus 2ⁿ⁻¹ times the same sum over the tilings by squares, where k is the number of crossings; T(n) itself agrees with [results.md](results.md).
- **Criteria.** On every record, the comparison with the representative sequence and the criterion on crossings agreed, and so did the two tests of symmetry (`inconsistent` = 0); every combinatorial symmetry was confirmed on the coordinates (`asymmetric` = 0).
- **Transposed rectangles.** A w × h and an h × w rectangle have the same numbers of tilings, classes and bags, with the reflections exchanged, for the three rectangles above.

The values for n = 11 and n = 12 come from the Rust search alone, with its default method; t(11), b(11), t(12) and b(12) were each obtained in two runs with identical results, the second with a later version of the program, and c(11) was computed once.

## The sixteen classes for four tiles

Each class is given by one tiling, with widths and heights rounded to four places; *wide* and *tall* refer to the long side.
The number of tilings in the class follows, and the sizes add up to 89.

1. x = 1. Four squares of side 1/2. One tiling, with all eight symmetries; the centre is a crossing.
2. x = 4/3. Three wide tiles 1/3 × 1/4 in a row along the bottom, and a wide tile 1 × 3/4 above them. Four tilings.
3. x = 1.3982, root of 2x³ − 3x² + x − 1. A row of height 0.2848 along the bottom, made of two wide tiles of width 0.3982 followed by a tall tile of width 0.2037, and a wide tile 1 × 0.7152 above. Eight tilings.
4. The same proportion and tiles, with the tall tile between the two wide ones. Four tilings.
5. x = 1.5437, root of x³ − 2x² + 2x − 2. A column of width 0.3522 on the left, made from the bottom of two wide tiles of height 0.2282 and a tall tile of height 0.5437, and a tall tile 0.6478 × 1 on the right. Eight tilings.
6. The same proportion and tiles, with the tall tile of the column between the two wide ones. Four tilings.
7. x = 5/3. Two wide tiles 1/3 × 1/5 stacked in the bottom left corner, a wide tile 2/3 × 2/5 beside them, and a wide tile 1 × 3/5 above. Eight tilings.
8. x = 1.8105, root of x³ − 2x² + 2x − 3. A band of height 0.4477 along the bottom, made of a wide tile 0.8105 × 0.4477 and, to its right, a wide tile 0.1895 × 0.1046 below a tall tile 0.1895 × 0.3430; a wide tile 1 × 0.5523 above. Eight tilings.
9. The same proportion. A block of width 0.4477 on the left, made of a wide tile 0.3430 × 0.1895 and a tall tile 0.1046 × 0.1895 side by side, below a tall tile 0.4477 × 0.8105; a tall tile 0.5523 × 1 on the right. Eight tilings.
10. x = 1.8756, root of 2x³ − 4x² + x − 1. A block of width 0.4668 on the left, made of two wide tiles 0.2334 × 0.1245 side by side below a tall tile 0.4668 × 0.8756; a tall tile 0.5332 × 1 on the right. Eight tilings.
11. x = 5/2. Two wide tiles 1/2 × 1/5 side by side along the bottom, and two wide tiles 1 × 2/5 above them. Four tilings.
12. x = 5/2. The same tiles, with the pair of small tiles between the two large ones. Two tilings, symmetric in both axes.
13. x = 2.5214, root of x³ − 3x² + 2x − 2. A band of height 0.6034 along the bottom, made of two wide tiles 0.7607 × 0.3017 stacked and a tall tile 0.2393 × 0.6034 to their right; a wide tile 1 × 0.3966 above. Eight tilings.
14. x = 2.8933, root of x³ − 3x² + x − 2. A column of width 0.3087 on the left, made of a wide tile of height 0.1067 below a tall tile of height 0.8933, followed by two tall tiles 0.3456 × 1. Eight tilings.
15. The same proportion and tiles. Wide tiles 1 × 0.3456 along the bottom and the top, and between them a wide tile 0.8933 × 0.3087 beside a tall tile 0.1067 × 0.3087. Four tilings.
16. x = 4. Four wide tiles 1 × 1/4 stacked. Two tilings, symmetric in both axes.

The proportions 1.3982, 1.5437, 1.8105, 5/2 and 2.8933 have two classes each and the other six have one, which gives 16 classes for the eleven proportions.
The classes of sizes four and two are symmetric in one axis and in both axes respectively; the classes of size eight have no symmetry.
In every case the two classes of a proportion use the same tiles, so that c(4) = 11.
The command `rectiling --classes 4` prints the list with coordinates.

## Proved and argued statements

**Representative sequences** (*Proved*, given that the tiles of an admissible record fit their tiers strictly, as stated in [enumeration.md](enumeration.md)).
In a record of a tiling, let a step place a tile at tier i.

1. Every tier j < i has an extending floor. Otherwise tier j becomes stale, and it can only cease to be stale when its floor grows, that is, when a tile is placed just beyond the end of the floor with its top at the level of the floor; this says that the floor extends. A stale tier can never be removed, so the sequence could not be completed.
2. If the floor of tier i extends, let Q be its right end and U the tile below the level of the floor with its top left corner at Q. If the tile placed is narrower than the floor, the remainder of the floor is started, and stays so until a tile W covers it up to Q; if the tile is as wide as the floor it is itself such a tile W. While the floor is started U cannot be placed, since it would lengthen the floor. So W is placed before U, and Q is a crossing with W at its upper left and U at its lower right.

Hence a record in which the lower right tile comes first at every crossing places every tile at the first tier whose floor does not extend: it is the representative record.
Conversely the representative sequence places the tiles standing on a horizontal segment after all the tiles hanging below it, so the lower right tile comes first at every crossing.
In particular a tiling without crossings has exactly one record for each orientation vector.
This is one half of what the Baxter numbers of [enumeration.md](enumeration.md) would require; the other half, that every complete admissible sequence is that of a tiling by rectangles without crossings and that two such tilings have the same sequence exactly when they are mosaic equivalent, is not proved.

**Multiplicity of records** (*Proved*; checked by enumeration on all dissections of the 4×4 grid and on samples of larger grids, and by the search for n ≤ 12).
A tiling with k crossings has exactly 2^k records for each orientation vector: for every set X of crossings there is exactly one record in which the upper left tile comes first exactly at the crossings in X.
Say that a floor X-extends if it extends and its end is not a crossing in X.

1. *Uniqueness.* Such a record places every tile at the first tier whose floor does not X-extend. A tier j before the tier of the placement has an extending floor, by the argument above, and no tile is placed at it before the tile U whose top left corner is the end of that floor; the tile standing on the floor at its end is placed at tier j or at a tier that replaces it, hence after U, so the end is not in X. If the floor of the tier of the placement extends, its end is a crossing where the upper left tile comes first, hence in X.
2. *Existence.* The construction of the representative sequence, with "extends" replaced by "X-extends", obeys the rules. The tile at the anchor is not wider than the floor: otherwise the floor extends and ends inside the bottom side of that tile, which is not a crossing. Stale floors X-extend and started floors do not, the started remainder ending where the floor did.
3. *The record has the set X.* If the lower right tile U of a crossing Q is placed first, it is as high as its wall, the floor of the previous tier ends at Q and X-extends, so Q is not in X. If the upper left tile is placed first, it is as wide as its floor, which ends at Q and extends; as it does not X-extend, Q is in X.

The search itself checks only that, for each k, the records of the tilings with k crossings are 2^k times as many as these tilings.
Consequently T(n) = Σ 2^k over the tilings with first tile wide and x > 1, plus 2ⁿ⁻¹ · Σ 2^k over the tilings by squares.

**Parity** (*Proved*). t(n) ≡ s(n) modulo 2, since transposition is an involution without fixed points on the tilings with x > 1.
With [OEIS A221842](https://oeis.org/A221842) this gives the parity of t(n): odd for n = 1, 4, 9 and 12 in the range computed.

**Diagonal symmetry** (*Proved*). A tiling fixed by a reflection in a diagonal consists of squares.
The reflection fixes two corners of the square, hence the tile at such a corner, and a rectangle fixed by a reflection in a diagonal through its corner is a square.
So the column of the diagonal reflections in the table of fixed tilings counts tilings by squares only.

**Quarter turns** (*Proved*). A tiling with x > 1 fixed by a quarter turn has a crossing at the centre of the square and a number of tiles divisible by four; a tiling by squares fixed by a quarter turn has n ≡ 0 or 1 modulo 4.
The centre cannot lie inside a tile when x > 1, since the tile would be mapped to itself, nor inside an edge of a tile, since the edge would be mapped to a perpendicular segment through the centre, which enters the interior of a tile; no tile is then fixed by the half turn, so the tiles fall into orbits of four.
For squares the only other possibility is a tile centred at the centre.
The table agrees: the quarter turns fix a tiling only for n = 1, 4, 8, 9 and 12.

**Fixed points** (*Proved*). The reflections in the two axes are conjugate, as are those in the two diagonals and the two quarter turns, so 8·b(n) = t(n) + 2·F_axis + F_half + 2·F_diagonal + 2·F_quarter, with the columns of the table.

**Crossings are not rare** (*Proved*, the second part given an exponential bound on t(n)).
Let K(n) be the total number of crossings over all tilings with n tiles.
Cutting a tile into four by its mid-lines maps a tiling with n tiles and one of its tiles to a tiling with n + 3 tiles and one of its crossings, injectively, so n·t(n) ≤ K(n + 3).
If the mean number of crossings K(n)/t(n) were bounded by B, then t(n + 3) ≥ n·t(n)/B and t would grow faster than any exponential, which would contradict t(n) ≤ n·2ⁿ·M(n).
That bound is not proved: it needs that a tiling is determined by its plane network, its orientations and its proportion, and the bound on T(n) argued in [analysis.md](analysis.md) does not give it, since a tiling with crossings has several records and one network.
So the mean number of crossings per tiling is unbounded.
In the range computed it is still small, near 0.025, against a lower bound near 0.007.

**Bags and quartering** (*Proved*). If a tiling with n − 3 tiles and proportion x has tiles of m different sizes, then x has at least m bags for n tiles: cutting a tile of short side s into four replaces s by four copies of s/2 in the bag, and the results differ for different s.
Since tilings with tiles of two sizes exist for every number of tiles from three onwards, c(n) > a(n) for all n ≥ 6.
For n = 6 this accounts for three of the five extra bags, at the proportions 3/2 and 1.7549 of the tilings with three tiles.

**Inequalities** (*Proved*). a(n) ≤ c(n) ≤ b(n) ≤ t(n) ≤ 8·b(n) and t(n) ≤ 2·T(n), with equality exactly when no tiling has a crossing or consists of squares, that is, for n = 2 and n = 3.

## Conjectures and heuristics

*Conjecture:* t(n)/(2ⁿ·M(n)) converges to a positive constant, so that t(n) and b(n) grow as (27/2)ⁿ up to a power of n.
The values for n = 5 to 12 are 0.2850, 0.2787, 0.2838, 0.2859, 0.2882, 0.2898, 0.2911 and 0.2920.
This is the companion of the conjecture on T(n) in [analysis.md](analysis.md), and the same caution applies: the ratio still creeps upward, and the safer statement is t(n)^(1/n) → 27/2.

*Heuristic:* two-point fits of t(n)/t(n − 1) = μ·(1 − α/n) give μ = 13.1 and α = 1.9 from n = 10, 11, 12, against 27/2 and 5/2 for 2ⁿ·M(n); the same kind of fit is some 5% low on the Baxter numbers ([analysis.md](analysis.md)), so this is compatible with the conjecture and does not test it sharply.

*Conjecture:* t(n + 1)/t(n) is increasing for n ≥ 5, and 8·b(n)/t(n) decreases to 1.
The second part would follow from any exponential separation between the tilings with a symmetry and all tilings.

*Heuristic:* the number of tilings with a symmetry grows by a factor near 4.3 per tile (118, 486, 1890, 8006, 32927, 141090, 601740 and 2629349 for n = 5 to 12), against 10.8 for all tilings, and nearly all of them have exactly one reflection in an axis.
A tiling symmetric in an axis is determined by one half, but the tiles that straddle the axis count once, so the factor exceeds the square root of that of t(n).

*Heuristic:* the share of tilings with a crossing rises slowly, from 2.0% at n = 7 to 2.6% at n = 12; by the statement above it cannot stay bounded away from one for ever unless the mean is carried by few tilings.

*Heuristic:* c(n)/a(n) = 1.020, 1.034, 1.042, 1.048, 1.052 and 1.055 for n = 6 to 11: nearly every proportion has a single bag.
For n ≤ 5 every proportion has one bag, so c(n) = a(n).
For n = 6 the four proportions with more than one bag (3/2, 2, and the roots of 2x³ − 3x² + 2x − 2 and x³ − 2x² + x − 1) all occur with fewer tiles, and the extra bags come from applying the constructions of the persistence statement of [analysis.md](analysis.md) to different tiles.
From n = 7 onwards proportions that are new at n can also have several bags (16, 148, 1368, 12410 and 108156 of them for n = 7 to 11), so no law in terms of the complexity of the proportion holds.
The largest number of bags at one proportion is at x = 2 for n = 8 to 11 (14, 53, 178 and 746).

*Heuristic:* between 9% and 10% of the proportions are realised by a single class of tilings (9.8, 9.3, 9.6, 9.5 and 9.1 per cent for n = 7 to 11), and the numbers of classes per proportion favour 1, 2, 4, 6, 8 and 12, the numbers of arrangements of a few blocks.
The mean number of classes per proportion is 6.6, 10.4, 15.7, 22.3 and 30.3 for n = 7 to 11, while the median stays at 6 or 8, and the largest is at x = 2 (52, 292, 1826, 10397 and 64115 classes).

*Conjecture (weak):* for n ≥ 7 the proportion with the most tilings is 2. Tested for n = 7 to 11.

## What did not work, and limits

- No match in the OEIS for t(n), b(n), c(n), the number of tilings with a symmetry, the number fixed by a reflection in an axis, or the corresponding counts for tilings with all tiles in one orientation (1, 2, 6, 21, 86, 374, 1758, 8626, 43827, 229160, 1229300, 6710767, 37261110, 209776944 tilings and 1, 1, 2, 6, 17, 63, 259, 1183, 5746, 29386, 155644, 844416, 4672999, 26265965 classes for n = 1 to 14, computed once with `--minority 0`). Only the counts for squares are known sequences.
- No law relating the number of bags of a proportion to the least number of tiles with which it occurs; see above.
- No recurrence was sought for t(n) or b(n): with twelve terms the tests of [analysis.md](analysis.md) could detect only very small recurrences, and the Baxter-like growth of T(n) already failed them.
- **Limits.** Counting t(n) and b(n) costs about twice the plain search: 12 seconds for n = 10, 128 seconds and 1.8 GB for n = 11, and 29 minutes and 7.2 GB for n = 12 (6.6 hours of processor time), so n = 13 would take some six hours and was not attempted. What limits it is the search itself, and beyond it the exact comparison of coordinates, which about 7% of the records need.
- Counting bags is limited by the exact comparison of each class representative with the stored tiling of the same key: two eliminations and n tests of divisibility, about 50 microseconds of processor time, for nearly every class, since c(n) is so much smaller than b(n). The run for n = 11 took 16 minutes and 3.5 GB while other jobs were running (two hours of processor time), and n = 12 would take about an hour and a half; it was not attempted. A cheaper exact comparison, reusing the eliminations of the default method in place of fresh ones, would be needed to go further.
- The reference program is limited by memory, since it keeps every tiling as a set of exact rectangles: eight tiles take eight minutes and 5.4 GB, and nine would need some ten times as much.

## Reproducing

```console
$ cargo build --release
$ ./target/release/rectiling --tilings 11
$ ./target/release/rectiling --tilings 12
$ ./target/release/rectiling --bags 10
$ ./target/release/rectiling --classes 4
$ ./target/release/rectiling --list --bags 9
$ ./target/release/rectiling --exact --bags 9
$ ./target/release/rectiling --tilings --minority 0 9
$ ./target/release/rectiling --tilings 6 3 2
$ python3 tools/reference.py 1 2 3 4 5 6 7 --mode A
$ python3 tools/reference.py 1 2 3 4 5 6 7 --mode B
$ cargo test --release
```

The option `--tilings` prints t(n), b(n) by both methods, the tilings fixed by each symmetry and by each group, the tilings by squares and by crossings, the decomposition of the records and the certification counters; `--bags` adds c(n); `--classes` lists one tiling from each class; `--list` adds, for each proportion, its numbers of records, tilings, classes and bags.
The reference program needs Python 3.14 and sympy; mode A uses the placement rules and mode B does not.
The tests in `tests/tilings.rs` pin t(n), b(n) and c(n) for n ≤ 8, the agreement of the two counts of classes, the decomposition of the records and the agreement with exact comparison.
