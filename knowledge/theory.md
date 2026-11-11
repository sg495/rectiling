# Theory

## Tilings as electrical networks

Brooks, Smith, Stone and Tutte (1940) associate a planar electrical network with every tiling of a rectangle by rectangles.
Each maximal horizontal segment of the tiling, including the top and bottom sides, is a node; each tile is a wire joining the segment that carries its top side to the segment that carries its bottom side.
A tile of width a and height b carries current a under a potential difference b, so it is a resistor of resistance b/a.
Kirchhoff's current law at a node says that the tiles hanging below a segment are together as wide as the tiles standing on it, and the voltage law around a face says that the tiles on the two sides of a vertical segment are together equally high.
The main rectangle is the whole network seen from its two poles: its height over its width is the effective resistance.

In a tiling by similar rectangles of proportion x, every resistance is x or 1/x, according to the orientation of the tile.
For positive resistances the currents in a network are uniquely determined by the potential difference between the poles, so for a fixed arrangement and fixed orientations the sizes of all tiles are determined by x, and the aspect ratio of the main rectangle is a rational function of x.
By the matrix-tree theorem this function is a ratio of two polynomials in the resistances with positive coefficients, one summing over the spanning trees of the network and the other over the spanning trees of the network with its poles identified.

The system depends only on which tiles border each maximal segment, that is, on the mosaic class of the tiling.
The order in which the junctions on the two sides of a segment alternate does not enter it.
Conversely, a solution of the system in which every tile has positive width and height is a tiling of that class, whatever order of junctions it exhibits.
A solution in which some tile has zero size is a tiling with fewer tiles, as happens for the pinwheel arrangement of five tiles, whose central tile degenerates to a point.

A tiling in which four tiles meet at a point lies in the closure of two classes, and arises in each as the solution at a value of x for which two junctions coincide.

## The degree bound

Taams (2023) showed that the proportion of a tiling of a square by n similar rectangles is algebraic of degree at most n.
Write one equation for each maximal segment, in the n tile sizes and the side of the square: these are n + 1 homogeneous linear equations in n + 1 unknowns, with coefficients 0, ±1 or ±x, and the column of the side of the square contains no x.
A tiling requires a non-zero solution, so the determinant vanishes, and the determinant has degree at most n in x.

The bound concerns the determinant and not the minimal polynomial: for n = 4 the proportions have degree one or three.

## Which proportions occur

Freiling and Rinne (1994) and Laczkovich and Szekeres (1995) proved that a square can be tiled by rectangles of proportion x, for some number of tiles, exactly when x is algebraic and every conjugate of x has positive real part.
Freiling, Laczkovich and Rinne (1997) proved that a rectangle of aspect ratio v can be tiled by rectangles of proportion u exactly when v is the value at u of an odd rational function with rational coefficients, all of whose preimages of v have positive real part.

For guillotine tilings the aspect ratio is built from x and 1/x by sums, which join rectangles side by side, and by the harmonic sums that stack them; these are the series and parallel compositions of resistors.

## Consequences for the search

- For fixed arrangement and orientations, the linear system has a unique solution for every x > 0, so a search can solve it symbolically in x and need only examine the roots of a single polynomial.
- The search does not rely on this: it detects singular systems and reports their number, which has been zero in every run.
- One system per mosaic class and orientation vector suffices, with positivity of the tile sizes as the only test.
- The conjugate condition of Freiling and Rinne cannot serve as a filter: the aspect ratio is an odd rational function of the kind that arises as the impedance of a network of inductors and capacitors, and every root of the resulting equation already has positive real part.
- Distinct arrangements often share the same rational function, so caching the roots by polynomial removes most of the algebraic work.
