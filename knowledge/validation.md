# Validation data

External results against which the implementation is checked.
Proportions are quoted here as x ≥ 1; sources that use the reciprocal convention give the reciprocal polynomials, which have the same degrees.

## Counts for the square

The values a(1), …, a(10) = 1, 1, 3, 11, 51, 245, 1372, 8522, 58347, 433926 are listed with their provenance in [problem.md](problem.md).

## Proportions for four tiles

| x          | minimal polynomial    |
| ---------- | --------------------- |
| 1          | x − 1                 |
| 1.33333333 | 3x − 4                |
| 1.39816095 | 2x³ − 3x² + x − 1     |
| 1.54368901 | x³ − 2x² + 2x − 2     |
| 1.66666667 | 3x − 5                |
| 1.81053571 | x³ − 2x² + 2x − 3     |
| 1.87555035 | 2x³ − 4x² + x − 1     |
| 2.5        | 2x − 5                |
| 2.52137971 | x³ − 3x² + 2x − 2     |
| 2.89328920 | x³ − 3x² + x − 2      |
| 4          | x − 4                 |

## Degree distributions

The number of proportions of each algebraic degree, as derived from the published lists.

| n | degree 1 | 2  | 3   | 4  | 5   | 6  | 7  |
| - | -------- | -- | --- | -- | --- | -- | -- |
| 3 | 2        | 0  | 1   |    |     |    |    |
| 4 | 5        | 0  | 6   | 0  |     |    |    |
| 5 | 11       | 2  | 32  | 2  | 4   |    |    |
| 7 | 76       | 16 | 560 | 92 | 546 | 38 | 44 |

The row for n = 7 comes from Henderson's data file, which lists all 1372 proportions with exact minimal polynomials.

## Sources

- Henderson's data file for n = 7, preserved at `http://web.archive.org/web/20251009101129id_/http://ianhenderson.org/similar-rectangles/out.json`.
- Gerbet's tables for n = 3 to 7, at `http://math.ucr.edu/home/baez/mathematical/gerbet_partitioning_square_into_rectangles/`; the file `rect7_detailed.pdf` includes polynomials.
- Narain's 51 polynomials for n = 5, printed in Baez's post of 22 December 2022.
- Einstein's notebook, whose saved output lists the counts up to n = 10.

## Internal consistency checks

- The number of placement sequences of the staircase enumeration, disregarding orientations, equals the Baxter number; see [enumeration.md](enumeration.md).
- The default and reference methods must agree on every proportion and on the number of tilings realising it.
- Counts for a main rectangle of aspect ratio w and 1/w must agree, since transposition maps tilings of one to tilings of the other.
- The search reports the number of tilings whose linear system is singular, or whose main aspect ratio does not depend on x; both must be zero for the result to be certified.
