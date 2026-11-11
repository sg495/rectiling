# From placement sequences to proportions

Each placement sequence with orientations determines a linear system for the sizes of the tiles, whose coefficients are polynomials in the proportion x.
Solving it exactly yields the proportions for which the sequence describes a genuine tiling.

## Unknowns and linear forms

The height of the main rectangle is fixed to one and its width W is an unknown.
A wide tile with short side s has width x·s and height s; a tall tile has width s and height x·s.
The short side of each tile placed inside its tier is a new unknown.
The sides of every other tile are determined by the floor or wall it spans:

- a full-height tile has the height of the wall, and its width is that height multiplied or divided by x;
- a full-width tile has the width of the floor, and its height is that width divided or multiplied by x;
- a full tile has both, which gives one linear *equation* between the floor and the wall.

All lengths are thus linear forms in W and the inside unknowns, with coefficients in ℤ[x] up to a common power of x in the denominator.
A sequence with k inside tiles has k + 1 full tiles, so there are k + 1 equations in the k + 1 unknowns.

The sequence describes a genuine tiling exactly when the system has a solution in which every tile has positive size; no further inequality is needed, because the system does not depend on the order of junctions along a segment.

## Reference method

The reference method treats one complete sequence at a time.
Fraction-free Gaussian elimination over ℤ[x] reduces the system to triangular form, with the width W in the last column.
The last row reads D(x)·W = N(x), so the main rectangle has aspect ratio W = N(x)/D(x), and back-substitution expresses every unknown as a polynomial numerator over the same denominator D.
For a main rectangle of aspect ratio a/b, the proportion must be a root of b·N(x) − a·D(x).

1. Eliminate, and form the polynomial b·N − a·D.
2. Discard the case if the polynomial has no root in [1, ∞); a sufficient test is that its expansion in x − 1 has coefficients of one sign.
3. Otherwise find its distinct roots in [1, ∞) as canonical algebraic numbers.
4. Back-substitute, and express the size of each tile as a polynomial numerator over D.
5. For each root, determine the sign of D and of every numerator; the root is a proportion if no sign is zero and all agree.

If D vanishes at a root, or the elimination meets a column without pivot, the system is singular and uniqueness of the solution fails; if b·N − a·D is identically zero, the aspect ratio does not depend on x.
Neither is expected to occur, by the theory in [theory.md](theory.md), and the search counts both so that their absence is verified and not assumed.

## Default method

The default method shares work between sequences with a common beginning, and replaces most exact sign computations by certified numerical ones.

**Eager elimination.**
The main rectangle is given sides a·t and b·t, for integers a and b and an unknown scale t, so that the system is homogeneous.
Whenever a full tile contributes an equation, one unknown is eliminated at once from every floor and wall of the staircase, by a step of Bareiss's fraction-free elimination: a form F becomes (E_m·F − F_m·E)/π, where E is the equation, m the eliminated unknown and π the previous pivot, and the division is exact.
A staircase with t tiers thus involves only t − 1 unknowns besides the scale, and the cost of a step shrinks towards the leaves of the search tree, where most of the work lies.
At the last placement nothing but the scale is left, and the final equation is the polynomial in x itself.

**Candidate roots.**
The polynomial is discarded if its expansion in x − 1 has non-negative coefficients and positive constant term.
Otherwise its roots in [1, ∞) are looked up in a cache shared by all threads, keyed by the coefficients; a polynomial is factorised only the first time it is met.
For eight tiles, 1.4 million cases lead to some 12 thousand distinct polynomials.

**Numerical check.**
For each root, the eliminations along the path are undone in reverse order in interval arithmetic, which yields enclosures for the free sides, and the placements are then replayed on intervals to obtain enclosures for the size of every tile.
The root is accepted if every size is certainly positive, and rejected if some size is certainly not.
If the enclosure of some size contains zero, the size is tested for being exactly zero: its linear form is carried through the remaining eliminations of the path, which leaves a polynomial multiple of the scale, and the size vanishes at the root exactly when the minimal polynomial of the root divides that polynomial.
A tile of size zero rejects the root, and this settles nearly all doubtful cases, which arise when a tile degenerates to a segment.
Only if no doubtful size is exactly zero, or a pivot cannot be separated from zero, is the case passed to the reference method; for ten tiles this happens for about one case in ten thousand.

The default method falls back to the reference method also when a coefficient exceeds the range of machine integers or an elimination finds no pivot, so its results are exact.

## Exact arithmetic

- **Coefficients.** Both methods run on machine integers with every operation checked; a case in which an operation overflows is recomputed with arbitrary-precision integers.
- **Canonical form.** A proportion is identified by its minimal polynomial, primitive with positive leading coefficient, and its position amongst the roots of that polynomial in [1, ∞).
- **Factorisation.** A polynomial that is irreducible modulo the prime 2³¹ − 1 is irreducible, and this is tried first. Otherwise the polynomial is split into square-free layers by repeated greatest common divisors with the derivative, unless it is already square-free modulo that prime; each layer is factorised modulo a single large prime exceeding twice the Landau–Mignotte bound on the coefficients of any factor, by Berlekamp's method, and the modular factors are recombined by trial division over ℤ. The large prime is 2⁶¹ − 1 whenever the bound allows, so that no lifting is needed.
- **Root isolation.** Real roots above one of an irreducible polynomial are isolated by Descartes' rule of signs with bisection, on dyadic intervals.
- **Signs.** The sign of a polynomial q at a root α of an irreducible polynomial f is zero exactly when f divides q; otherwise it is found by interval evaluation, first in floating point with outward rounding and, when that is inconclusive, in exact dyadic arithmetic with the isolating interval refined until the sign is determined.
- **Caching.** Irreducible factors and their isolated roots are shared between all cases through a registry, which assigns each algebraic number a stable identifier. The registry and the cache of polynomials store coefficients as variable-length bytes in arenas indexed by hash tables, which keeps the memory per proportion below a hundred bytes or so.
