# Lean formalisation of the reference method

A Lean 4 development, on top of Mathlib, proving that the staircase enumeration of `rectiling` is sound and complete for tilings of a rectangle by similar rectangles, and that the reference ("exact") method reports exactly the proportions of such tilings, given specifications of its exact-arithmetic primitives.

## Building

The toolchain is pinned in `lean-toolchain` and Mathlib in `lake-manifest.json`.

```
lake exe cache get
lake build
```

The build prints the axioms of each main theorem (module `Rectiling.Audit`); all of them depend on `propext`, `Classical.choice` and `Quot.sound` only.
The development contains no `sorry`, no `admit` and no `axiom`.

## Modules

The modules fall into three groups, which a treatment of the default method can reuse separately.

Geometry:

- `Rectiling/Geometry.lean` — rectangles `Rect`, tilings `IsTiling`, tilings by rectangles of proportion `x ≥ 1` `IsSimilarTiling`, transposition.
- `Rectiling/Scaling.lean` — homotheties of tilings.

Staircase:

- `Rectiling/Staircase.lean` — the model of `src/staircase.rs`: `Fit`, `Placement`, `Tier`, the arithmetic of lengths `Algebra`, `place`, the emitted `positives` and `equations`, the rules `Allows` and `Admits`, complete admissible sequences `Complete`, the square rule `FirstWide`, and the constraints over the reals `Satisfies`.
- `Rectiling/Layout.lean` — the anchors of a staircase with real lengths (`geom`), the region still to be filled (`region`), the rectangles of the placed tiles (`tiles`), and the effect of a placement on the anchors (`geom_place`).
- `Rectiling/Region.lean` — the effect of a placement on the region (`step_region`).
- `Rectiling/Soundness.lean` — the theorem `soundness`.
- `Rectiling/Extension.lean` — one step of the construction of a placement sequence from a tiling, in terms of the anchors (`GInv.step`).
- `Rectiling/Completeness.lean` — the theorems `completeness` and `completeness_square`.
- `Rectiling/Check.lean` — an executable count of the admissible sequences of the model, compared with the Baxter numbers 1, 2, 6, 22, 92, 422, 2074 that the library reports.

Solver:

- `Rectiling/Forms.lean` — the model of `src/form.rs`: linear forms `Form` with coefficients in ℤ[x] over a power of x, the symbolic system `symEquations` and `symPositives`, and its agreement with the system over the reals (`satisfies_iff_forms`).
- `Rectiling/Solver.lean` — the assumed primitives `Primitives`, the model `solve` of `solve_in` in `src/exact.rs`, and the theorems `solve_sound`, `solve_complete` and `solve_spec`.
- `Rectiling/Main.lean` — the theorems `reported_sound`, `reported_complete` and `reported_iff`, which combine the three groups.

## Main theorems

- `soundness`. For a complete admissible placement sequence for n tiles, a proportion x ≥ 1 and free sides that satisfy the emitted equations and positivity constraints, the tiles of the sequence form a tiling of the W × H rectangle by n rectangles of proportion x.
- `completeness`. For W, H > 0, every tiling of the W × H rectangle by rectangles of proportion x ≥ 1 is, up to the order of the tiles, the list of tiles of a complete admissible placement sequence, for free sides that satisfy the emitted constraints; a placement is wide exactly when the width of its tile is x times its height.
- `completeness_square`. For a square, the tiling or its transpose is obtained in this way from a sequence whose first tile is wide.
- `solve_sound`. Every proportion reported by the reference method for a complete admissible sequence is a real number x ≥ 1 at which the emitted system, for a main rectangle of width a/b and height one, has a solution satisfying every constraint.
- `solve_complete`. Conversely, every such x is reported, provided that the method counts no singular situation for the sequence and does not find the aspect ratio independent of the proportion.
- `solve_spec`. The equivalence of the two, under the same proviso.
- `reported_iff`. For positive integers a and b, if no enumerated sequence for n tiles is singular or has a constant aspect ratio, the proportions reported are exactly the proportions of the tilings of the a × b rectangle by n rectangles; the direction `reported_sound` needs no proviso.

## How the proofs go

Soundness does not follow from the emitted constraints alone, since these never state that a tile placed inside its tier is narrower than the floor or lower than the wall.
The missing inequalities come from the admissibility rules.
A floor that is not positive and is started, or is the last one, can never become positive, because only a tile of full height at the next tier would lengthen it, and the rule on started floors forbids that.
A wall that is not positive, behind stale tiers, can never become positive, because only a tile of full width at the previous tier would raise it, and that tier is stale until a tile of full height is placed against the wall in question.
Either situation prevents the staircase from being emptied, so in a complete sequence every floor and wall is positive at every step, and each placement removes a rectangle from the region still to be filled.

Completeness builds the sequence one tile at a time.
The floor of a tier *extends* when the tile of the tiling lying below and to the right of the right end of the floor has its top side at the level of the floor.
The next tile is the one at the anchor of the first tier whose floor does not extend.
A stale tier always has a floor that extends and a started floor never does, so the placement obeys both rules.
The bound on the number of remaining tiles in `Staircase::admits` holds of itself for any sequence that obeys the two rules and empties the staircase (`Allowed.completeFrom`).

## Assumed primitives

The Rust code is not verified.
The structure `Primitives` states what the exact-arithmetic primitives are assumed to compute, and every theorem on the reference method is quantified over it.

- **Fraction-free elimination** (`eliminate`, `eliminate_some`). On success, the elimination and back-substitution return a denominator D and numerators such that D is the determinant of the system and the numerators are those of Cramer's rule, up to a common factor; Bareiss's elimination with row exchanges gives the factor ±1. Nothing is assumed when the elimination fails, since the method then counts a singular situation.
- **Real-root isolation** (`roots`, `mem_roots`). The roots reported for a non-zero polynomial are exactly its real roots not smaller than one. This covers factorisation, the square-free decomposition, Descartes' rule, the cache, and the passage to the primitive part.
- **Sign determination** (`sign`, `sign_eq`). The sign reported for a polynomial at a reported root is the sign of its value there.

The specifications are consistent: `Primitives.ideal` meets them.
The test that discards a polynomial whose expansion in x − 1 has coefficients of one sign and non-zero constant term is modelled (`NoRootTest`) and proved sufficient (`NoRootTest.ne_zero`), on the assumption that the Taylor shift computes that expansion.

## Differences between the model and the Rust code

- Lengths are real numbers in the geometric part, and forms have exact coefficients in ℤ[x]; the fallback from machine integers to arbitrary precision is not modelled.
- The staircase is a list, with no bound on the number of tiers or tiles; a placement at a tier that does not exist is not admissible in the model, where the Rust code would fail.
- The free side of the j-th inside placement is `fresh j`, for a function `fresh` given once; the Rust code draws the unknowns from a counter.
- The positions of the tiles, which the Rust code never computes, are defined from the floors and walls (`tileAt`).
- A form stores a coefficient for every index of unknown, zero beyond those in use; the Rust code stores a vector.
- A reported proportion is a real number; the registry of algebraic numbers, their identifiers, and the counting of sequences per proportion are not modelled.
- The fields `candidate` and `overflow` of the outcome are omitted.
- The parallel driver is modelled by the predicate `Reported`, an existential over the complete admissible sequences, with the first tile wide when the sides of the main rectangle are equal.

## Not proved

- That each tiling without a point where four tiles meet has exactly one placement sequence.
- Anything about the default method of `src/fast.rs`.
- That the singular and constant cases never occur.
