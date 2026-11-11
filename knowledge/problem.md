# The problem

## Statement

A rectangle is *tiled by similar rectangles* when it is cut into finitely many rectangles that all have the same aspect ratio, where each tile may be placed in either orientation and tiles may differ in size.
We write x ≥ 1 for the *proportion* of the tiles, the ratio of the long side to the short side, and w for the aspect ratio (width over height) of the main rectangle.
Much of the literature uses the reciprocal convention, with proportion at most one; the two are equivalent.

For the unit square, a(n) is the number of distinct proportions x for which a tiling with exactly n tiles exists.
This is [OEIS A359146](https://oeis.org/A359146).
The count concerns proportions only: different arrangements with the same proportion are counted once.
The same question for a main rectangle of rational aspect ratio w gives a two-parameter family of counts.

## Small cases

- n = 1: the square itself, x = 1.
- n = 2: two halves, x = 2.
- n = 3: three proportions, 3/2, 3 and the real root 1.7548… of x³ − 2x² + x − 1, the square of the plastic ratio.
- n = 4: eleven proportions, five rational and six cubic.
- n = 5: fifty-one proportions, of degrees one to five.

## Known values

| n    | 1 | 2 | 3 | 4  | 5  | 6   | 7    | 8    | 9     | 10     |
| ---- | - | - | - | -- | -- | --- | ---- | ---- | ----- | ------ |
| a(n) | 1 | 1 | 3 | 11 | 51 | 245 | 1372 | 8522 | 58347 | 433926 |

- The OEIS entry lists the values up to n = 7, and mentions a(8) = 8522 as apparent.
- The values up to n = 7 were obtained independently by Ian Henderson and Daniel Gerbet in early 2023; a(7) was first reported as 1371 and then corrected.
- The value a(8) = 8522 is due to Henderson, and was reproduced by David Einstein with a different method.
- The values a(9) and a(10) were reported by Einstein alone, in a blog comment of 15 March 2023, and were never submitted to the OEIS.
- No formula, recurrence, generating function or asymptotic estimate for a(n) is known.

## History

- Dehn (1903) showed that a rectangle can be tiled by squares only if its aspect ratio is rational.
- Brooks, Smith, Stone and Tutte (1940) related tilings of rectangles to planar electrical networks.
- Freiling and Rinne (1994), and independently Laczkovich and Szekeres (1995), showed that a square can be tiled by rectangles of proportion x, for some number of tiles, exactly when x is algebraic and all its conjugates have positive real part.
- Freiling, Laczkovich and Rinne (1997) extended this characterisation to a rectangular main rectangle.
- In December 2022 John Baez asked on Mathstodon for the ways of dividing a square into n similar rectangles, which led to a collaborative effort: Rahul Narain enumerated guillotine tilings for n = 5, Ian Henderson wrote an exhaustive search over grid arrangements, Lisanne Taams proved that x has algebraic degree at most n, Daniel Gerbet produced tables for n ≤ 7, and David Einstein recast the search in terms of electrical networks.
- The sequence was added to the OEIS by N. J. A. Sloane in February 2023, on the day of a New York Times article by Siobhan Roberts.

## Open questions

- Independent confirmation of a(9) and a(10), and further terms.
- A formula, recurrence or asymptotic estimate for a(n).
- The number of tilings up to symmetry, as opposed to the number of proportions.
- The distribution of the algebraic degrees of the proportions; degree n is attained for n = 3, 5 and 7 but not for n = 4.
- The share of proportions that require a tiling which is not guillotine.
- Whether a proportion achievable with n tiles is always achievable with n + 1 tiles; it is always achievable with n + 3, by cutting one tile into four.
- The corresponding counts for a main rectangle of aspect ratio other than one.

## References

- J. C. Baez, *Dividing a Square into Similar Rectangles*, The n-Category Café, 22 December 2022, <https://golem.ph.utexas.edu/category/2022/12/dividing_a_square_into_similar.html>.
- J. C. Baez, *Dividing a Square into 7 Similar Rectangles*, Azimuth, 6 March 2023, <https://johncarlosbaez.wordpress.com/2023/03/06/dividing-a-square-into-7-similar-rectangles/>; the comments include Einstein's values for n = 9 and 10.
- D. Einstein, SageMath notebook, <https://github.com/deinst/mathcode/blob/master/Triconnected_Planar.ipynb>.
- I. Henderson, *Cutting squares into similar rectangles using a computer program*, February 2023, formerly at `http://ianhenderson.org/similar-rectangles/` and preserved by the Internet Archive.
- L. Taams, proof of the degree bound, Mathstodon, 5 January 2023, <https://mathstodon.xyz/@Lisanne/109636809198760215>.
- G. Spahn, *Tiling a Square with Similar Rectangles*, Rutgers Experimental Mathematics Seminar, 30 March 2023, <https://sites.math.rutgers.edu/~zeilberg/expmath/spahn23.pdf>.
- S. Roberts, *The Quest to Find Rectangles in a Square*, The New York Times, 7 February 2023.
- M. Dehn, Über die Zerlegung von Rechtecken in Rechtecke, *Math. Ann.* 57 (1903), 314–332.
- R. L. Brooks, C. A. B. Smith, A. H. Stone, W. T. Tutte, The dissection of rectangles into squares, *Duke Math. J.* 7 (1940), 312–340.
- C. Freiling, D. Rinne, Tiling a square with similar rectangles, *Math. Res. Lett.* 1 (1994), 547–558.
- M. Laczkovich, G. Szekeres, Tilings of the square with similar rectangles, *Discrete Comput. Geom.* 13 (1995), 569–572.
- C. Freiling, M. Laczkovich, D. Rinne, Rectangling a rectangle, *Discrete Comput. Geom.* 17 (1997), 217–225.
- S. Dorichenko, M. Skopenkov, A square from similar rectangles, arXiv:1305.2598.
- M. Prasolov, M. Skopenkov, Tiling by rectangles and alternating current, *J. Combin. Theory Ser. A* 118 (2011), 920–937.
