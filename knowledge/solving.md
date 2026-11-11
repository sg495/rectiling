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

Each placement also contributes strict inequalities: a narrow tile is narrower than its floor and, on a locked tier, wider than the recorded length; a low tile is lower than its wall; an inside unknown is positive.
These are exactly the conditions under which the sequence is the canonical one for an actual tiling.

## Solving

Fraction-free Gaussian elimination over ℤ[x] reduces the system to triangular form, with the width W in the last column.
The last row reads D(x)·W = N(x), so the main rectangle has aspect ratio W = N(x)/D(x), and back-substitution expresses every unknown as a polynomial numerator over the same denominator D.
For a main rectangle of aspect ratio a/b, the proportion must be a root of b·N(x) − a·D(x).

The procedure for one sequence and orientation vector is as follows.

1. Eliminate, and form the polynomial b·N − a·D.
2. Discard the case if the polynomial has no root in [1, ∞); a sufficient test is that its expansion in x − 1 has coefficients of one sign.
3. Otherwise find its distinct roots in [1, ∞) as canonical algebraic numbers.
4. Back-substitute, and express each inequality as a polynomial numerator over D.
5. For each root, determine the sign of D and of every numerator; the root is a proportion if no sign is zero and all agree.

If D vanishes at a root, or the elimination meets a column without pivot, the system is singular and uniqueness of the solution fails; if b·N − a·D is identically zero, the aspect ratio does not depend on x.
Neither is expected to occur, by the theory in [theory.md](theory.md), and the search counts both so that their absence is verified and not assumed.

## Exact arithmetic

- **Coefficients.** The search runs on machine integers with every operation checked; a subtree in which any operation overflows is recomputed with arbitrary-precision integers.
- **Canonical form.** A proportion is identified by its minimal polynomial, primitive with positive leading coefficient, and its position amongst the roots of that polynomial in [1, ∞).
- **Factorisation.** A polynomial is split into square-free layers by repeated greatest common divisors with the derivative; each layer is factorised modulo a single large prime exceeding twice the Landau–Mignotte bound on the coefficients of any factor, by distinct-degree and equal-degree splitting, and the modular factors are recombined by trial division over ℤ.
- **Root isolation.** Real roots above one of an irreducible polynomial are isolated by Descartes' rule of signs with bisection, on dyadic intervals.
- **Signs.** The sign of a polynomial q at a root α of an irreducible polynomial f is zero exactly when f divides q; otherwise it is found by interval evaluation, first in floating point with outward rounding and, when that is inconclusive, in exact dyadic arithmetic with the isolating interval refined until the sign is determined.
- **Caching.** Factorisations and isolated roots are shared between all cases through a registry, so that each distinct polynomial is factorised once.
