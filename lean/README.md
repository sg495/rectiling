# Lean formalisation of the two methods

A Lean 4 development, on top of Mathlib, proving that the staircase enumeration of `rectiling` is sound and complete for tilings of a rectangle by similar rectangles, that the reference ("exact") method reports exactly the proportions of such tilings, and that the default ("fast") method does too, given specifications of the arithmetic primitives of each.

## Building

The toolchain is pinned in `lean-toolchain` and Mathlib in `lake-manifest.json`.

```
lake exe cache get
lake build
```

The build prints the axioms of each main theorem (module `Rectiling.Audit`); all of them depend on `propext`, `Classical.choice` and `Quot.sound` only.
The development contains no `sorry`, no `admit` and no `axiom`.

## Modules

The modules fall into four groups.

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
- `Rectiling/Enumeration.lean` — the enumerations of `src/search.rs` and `src/fast.rs`: the placements tried at a staircase (`moves`), the complete sequences below a staircase (`completions`), the prefixes of bounded length (`prefixes`), and the theorems `mem_completions` and `mem_completions_iff_prefix`.

Reference method:

- `Rectiling/Forms.lean` — the model of `src/form.rs`: linear forms `Form` with coefficients in ℤ[x] over a power of x, the symbolic system `symEquations` and `symPositives`, and its agreement with the system over the reals (`satisfies_iff_forms`).
- `Rectiling/Solver.lean` — the assumed primitives `Primitives`, the model `solve` of `solve_in` in `src/exact.rs`, and the theorems `solve_sound`, `solve_complete` and `solve_spec`.
- `Rectiling/Main.lean` — the theorems `reported_sound`, `reported_complete` and `reported_iff`, which combine the three groups.

Default method (namespace `Rectiling.Fast`):

- `Rectiling/Elimination.lean` — the eager elimination over any commutative ring with a distinguished unit: forms `Vec` indexed by unknown, stages `Stage`, records `Step` and `Elim`, the exact update `elimForm`, a successful symbolic pass `Run`, the same eliminations over a field (`carry`), and the relation of the records to the system that has not been reduced (`Elims`, `Trace`, `Run.trace`).
- `Rectiling/BackSubstitution.lean` — what the relation gives over a field in which no pivot vanishes: a carried form takes on a solution the value of the original multiplied by the pivot (`Elims.dot_carry`), the recorded and the original equations have the same solutions (`Elims.true_of_stage`, `Elims.stage_of_true`), back-substitution solves them (`back_solves`) and is the only solution (`back_unique`).
- `Rectiling/Determinant.lean` — the last pivot is the determinant of the system, up to sign (`Elims.det_eq`).
- `Rectiling/Reduced.lean` — the homogeneous system of a path (`homEquations`, `homPositives`), its agreement with the system over the reals (`satisfies_iff_hom`), and the theorems `Run.final_eq_det`, `Run.final_vanishes` and `Run.solution`.
- `Rectiling/Certified.lean` — the coefficient ring ℤ[x, x⁻¹] (`Coeff`), the assumed numerical primitives `Numerics`, the model of `Engine::check` and `Engine::degenerate` (`backIv`, `check`, `degenerate`), and the theorems `check_accept`, `check_reject` and `dvd_iff_evalAt_eq_zero`.
- `Rectiling/Fast.lean` — the unmodelled machine limits `Limits`, the model of `Engine::step` (`advance`), of the symbolic pass along a path (`run`), of `Engine::leaf` and `Engine::finish` (`leaf`), the proportions reported for a path (`fastSolve`), and the theorems `leaf_spec`, `fastSolve_sound`, `fastSolve_complete`, `fastSolve_eq_solve`, `fast_sound`, `fast_complete`, `fast_iff` and `fast_iff_reported`.
- `Rectiling/Search.lean` — the model of `Engine::explore`, `Engine::delegate` and the splitting by prefixes of `Search::run` (`explore`, `exploreForced`, `Searched`), and the theorem `searched_iff`.
- `Rectiling/Exact.lean` — exactness of the divisions: `Elims.pivot_eq_det`, `Elims.divisible` and `division_exact`.
- `Rectiling/Target.lean` — the relation between the proportion polynomials of the two methods (`Run.final_eq_target`).

## Main theorems

Staircase and reference method:

- `soundness`. For a complete admissible placement sequence for n tiles, a proportion x ≥ 1 and free sides that satisfy the emitted equations and positivity constraints, the tiles of the sequence form a tiling of the W × H rectangle by n rectangles of proportion x.
- `completeness`. For W, H > 0, every tiling of the W × H rectangle by rectangles of proportion x ≥ 1 is, up to the order of the tiles, the list of tiles of a complete admissible placement sequence, for free sides that satisfy the emitted constraints; a placement is wide exactly when the width of its tile is x times its height.
- `completeness_square`. For a square, the tiling or its transpose is obtained in this way from a sequence whose first tile is wide.
- `solve_sound`. Every proportion reported by the reference method for a complete admissible sequence is a real number x ≥ 1 at which the emitted system, for a main rectangle of width a/b and height one, has a solution satisfying every constraint.
- `solve_complete`. Conversely, every such x is reported, provided that the method counts no singular situation for the sequence and does not find the aspect ratio independent of the proportion.
- `solve_spec`. The equivalence of the two, under the same proviso.
- `reported_iff`. For positive integers a and b, if no enumerated sequence for n tiles is singular or has a constant aspect ratio, the proportions reported are exactly the proportions of the tilings of the a × b rectangle by n rectangles; the direction `reported_sound` needs no proviso.

Default method:

- `Run.trace`. Along a successful symbolic pass, over any field into which the coefficients map without a pivot vanishing, every form of a stage is the corresponding form of the system that has not been reduced, carried through the eliminations made so far; the form carried is the original multiplied by the current pivot, modulo the equations seen so far (`Elims.carry_eq`).
- `Run.final_eq_det`. On a complete path, the scale coefficient c of the final equation is, up to sign, the determinant of the homogeneous system in the scale and the free sides.
- `Run.final_vanishes`. Hence c vanishes at every real x at which the system has a solution of scale one, whether or not a pivot vanishes there.
- `Run.solution`. At a real x where no pivot vanishes, back-substitution gives an assignment of scale one that solves the system exactly when c vanishes at x, every solution of scale one coincides with it, and the size recorded for a tile, carried through the later eliminations, has the value of the positivity constraint of the tile multiplied by the last pivot.
- `Run.final_eq_target`. If the elimination of the reference method succeeds with common factor ε, then ε · c = ± x^e · (b N − a D) for some integer e.
- `division_exact`. At every stage that the symbolic pass reaches, the elimination of any unknown with a non-zero coefficient divides every floor and wall exactly by the current pivot.
- `check_accept`, `check_reject`. A root of c that the numerical check accepts satisfies every constraint; a root that it rejects satisfies them for no choice of the free sides, whether the rejection comes from an enclosure that is certainly not positive or from a tile certified to have size zero.
- `dvd_iff_evalAt_eq_zero`. A primitive integer polynomial, irreducible over ℚ, that vanishes at a real number divides exactly the integer polynomials that vanish there; the certificate of a degenerate tile is therefore complete as well as correct when the stored polynomial is the minimal one.
- `leaf_spec`, `direct_spec`. A complete admissible path that is not passed to the reference method reports exactly the real numbers x ≥ 1 at which the emitted system, for a main rectangle of width a/b and height one, has a solution satisfying every constraint.
- `fastSolve_sound`, `fastSolve_complete`. The proportions reported for a path are such numbers; conversely every such number is reported, provided that, if the path is passed to the reference method, that method counts no singular situation on it and does not find the aspect ratio independent of the proportion.
- `solve_subset_fastSolve`, `fastSolve_eq_solve`. The default method reports for a path everything that the reference method reports, and exactly the same when the reference method counts no singular situation and no constant aspect ratio on the path.
- `mem_completions`, `mem_completions_iff_prefix`. The sequences enumerated below a staircase are those whose placements are admissible and which empty it, with the first tile wide for a square; a sequence is enumerated exactly when it consists of one of the prefixes of the driver followed by a sequence enumerated below the staircase that the prefix reaches.
- `searched_iff`. The depth-first search, with forced prefixes of any length and with the subtree below a failure of the symbolic pass passed to the reference method, finds the proportions reported for the complete admissible sequences one at a time.
- `fast_sound`. Every proportion reported by the default method is the proportion of a tiling of the a × b rectangle by n rectangles; no proviso is needed.
- `fast_complete`, `fast_iff`. If no sequence that the default method passes to the reference method is singular or has a constant aspect ratio, the proportions reported by the default method are exactly the proportions of the tilings of the a × b rectangle by n rectangles.
- `fast_iff_reported`. If the search by the reference method is certified, the two methods report the same proportions; `reported_imp_fast` needs no proviso.

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

The default method is treated through one relation between its forms and those of the homogeneous system that has not been reduced.
Over a field in which the pivots do not vanish, the update (E_m F − F_m E)/π is a linear map on forms, so the forms of a stage are the images of the original forms under the composite of these maps, and the staircase arithmetic commutes with it.
Two fields are used.
Over the field of fractions of the coefficient ring no pivot vanishes, which gives the algebraic identities: each recorded equation is its original multiplied by the previous pivot plus a combination of the earlier originals, so the recorded equations are a lower triangular matrix times the system, and they are upper triangular in the eliminated unknowns; comparing determinants identifies the last pivot, and the same argument with a form appended as a fictitious last equation shows that every quotient lies in the ring.
Over the reals, at a root where the numerical check has separated every pivot from zero, the same relation shows that the recorded equations and the original ones have the same solutions, which back-substitution computes.
The check then decides a leaf correctly because the candidate is the only solution of scale one, and the proportion polynomial vanishes at every solution because it is the determinant.

## Assumed primitives

The Rust code is not verified.
The structures `Primitives` and `Numerics` state what the primitives are assumed to compute, and every theorem on the two methods is quantified over them.
Both sets of specifications are consistent: `Primitives.ideal` and `Numerics.ideal` meet them.

For the reference method (`Primitives`):

- **Fraction-free elimination** (`eliminate`, `eliminate_some`). On success, the elimination and back-substitution return a denominator D and numerators such that D is the determinant of the system and the numerators are those of Cramer's rule, up to a common factor; Bareiss's elimination with row exchanges gives the factor ±1. Nothing is assumed when the elimination fails, since the method then counts a singular situation.
- **Real-root isolation** (`roots`, `mem_roots`). The roots reported for a non-zero polynomial are exactly its real roots not smaller than one. This covers factorisation, the square-free decomposition, Descartes' rule, the caches, and the passage to the primitive part. The default method uses the same primitive.
- **Sign determination** (`sign`, `sign_eq`). The sign reported for a polynomial at a reported root is the sign of its value there.

The test that discards a polynomial whose expansion in x − 1 has coefficients of one sign and non-zero constant term is modelled (`NoRootTest`, and `FastNoRoot` for the one-sided form of the default method) and proved sufficient (`NoRootTest.ne_zero`), on the assumption that the Taylor shift computes that expansion.

For the default method (`Numerics`):

- **Interval arithmetic** (`mem_ofInt`, `mem_add`, `mem_sub`, `mem_mul`, `mem_neg`, `mem_div`). The interval of an integer encloses it, and the sum, difference, product and negation of intervals enclose the results on the enclosed numbers, as does the quotient when the divisor is certainly away from zero.
- **Decisions on intervals** (`ne_zero`, `nonpos_le`, `pos_lt`). An interval that is certainly away from zero, certainly not positive, or certainly positive, encloses only numbers that are so.
- **Polynomial enclosure** (`mem_eval`). When it succeeds, the enclosure of a Laurent polynomial over an interval that is certainly away from zero encloses the value at every positive number of the interval.
- **Root references** (`mem_rootIv`). The interval stored with a root not smaller than one of a non-zero integer polynomial encloses the root and is certainly away from zero.
- **Minimal polynomials and divisibility** (`minPoly_root`, `divides_dvd`). A stored minimal polynomial vanishes at its root, and a positive test of divisibility is correct. Nothing is assumed of a negative test, nor that the stored polynomial is irreducible.
- **Coefficients** (`key_spec`, `coeffs_spec`). The coefficient list of a Laurent polynomial is that of the polynomial up to a power of x, and the normalised key up to a sign as well.

Nothing is assumed on `Limits`, which stands for the failures of machine arithmetic and for the choice of the unknown to eliminate.

## Differences between the model and the Rust code

Common to both methods:

- Lengths are real numbers in the geometric part, and forms have exact coefficients; the fallback from machine integers to arbitrary precision is not modelled.
- The staircase is a list, with no bound on the number of tiers or tiles; a placement at a tier that does not exist is not admissible in the model, where the Rust code would fail.
- The free side of the j-th inside placement is `fresh j`, for a function `fresh` given once; the Rust code draws the unknowns from a counter.
- The positions of the tiles, which the Rust code never computes, are defined from the floors and walls (`tileAt`).
- A form stores a coefficient for every index of unknown, zero beyond those in use; the Rust code stores a vector.
- A reported proportion is a real number; the registry of algebraic numbers, their identifiers, and the counting of sequences per proportion are not modelled.
- The parallel driver is modelled by an existential over the complete admissible sequences (`Reported`, `FastReported`), with the first tile wide when the sides of the main rectangle are equal; for the default method the depth-first search itself is also modelled (`Searched`).

Reference method:

- The fields `candidate` and `overflow` of the outcome are omitted.

Default method:

- **Unknowns for slots.** The Rust code keeps eight slots and reuses the slot of an eliminated unknown; the model gives every inside placement its own index and never reuses one. The two differ by a renaming of the live slots at each stage, which the model does not state. Exhaustion of the slots is a failure covered by `Limits.overflow`.
- **Failures.** A failure of machine arithmetic at a placement (a coefficient beyond the limit, a polynomial too long, no free slot, a quotient beyond the limit) is an arbitrary function `Limits.overflow` of the sequence of placements made, on which nothing is assumed. A division that is not exact is modelled as such; `division_exact` shows that it does not occur.
- **Choice of the pivot.** The unknown to eliminate is an arbitrary function `Limits.pick` of the sequence of placements and the equation; the model proceeds only if the unknown chosen is the side of an inside placement already made and has a non-zero coefficient, and otherwise fails. The Rust code takes the live slot whose coefficient has fewest terms.
- **Delegation.** Every failure, an identically zero or malformed final equation, and every unsettled root pass the path to the reference method (`fastSolve`); in the search, a failure passes the whole subtree below the placement, as `Engine::delegate` does.
- **The last tile.** `Engine::last` forms the final equation of both orientations of the last tile directly; the model treats the last placement as any other, which gives the same equation.
- **Intervals.** Intervals, floats and their rounding are an abstract type with assumed properties; that the code meets them, in particular in the presence of infinite or undefined endpoints, is not examined.
- **Order of summation.** The model sums the terms of an equation in the order of the unknowns and the Rust code in the order of the slots; only the enclosure matters.
- **Free sides in the replay.** The model reads the free side of the j-th inside placement from the value of unknown j + 1 after back-substitution; the Rust code collects the values slot by slot during back-substitution, which is the same value under the renaming of slots.
- **Caches.** The caches of polynomials and of minimal polynomials are transparent in the model.
- **Unchecked arithmetic.** The expansion in x − 1 in `Engine::finish` is computed in 128-bit integers without a check for overflow, and the model computes it exactly.

## Findings

- **The two methods can differ only where the reference method is singular.** A leaf that the default method settles itself reports every proportion at which the system has a positive solution, including one at which the determinant D of the reference method vanishes; the reference method counts a singular situation there and reports nothing. The default method is therefore sound without proviso and reports at least what the reference method reports (`reported_imp_fast`), and the two agree when the reference search is certified (`fast_iff_reported`). No example of a disagreement is known.
- **Completeness of the default method needs less than that of the reference method.** Only the paths passed to the reference method need to be free of singular situations and constant aspect ratios (`FastCertified`), which is what the counters `singular` and `constant` of a run of the default method record.
- **The pivots need not be assumed non-zero at a solution.** The proportion polynomial is the determinant of the system, so every solution is amongst its roots; the pivots matter only for the roots, where the numerical check separates them from zero or the path is passed to the reference method.
- **A failure on a forced placement would be counted more than once.** `Engine::step` passes the whole subtree below a failing placement to `Engine::delegate`, also when the placement is one of the forced placements of a prefix that is not yet exhausted; every prefix through that placement would then enumerate the same subtree, and the counts of sequences per proportion and the statistics would include it once per prefix. The set of proportions is not affected (`searched_iff`). The first elimination divides by one and cannot fail, and no failure within the first three placements has been exhibited, so this is a latent defect of the counts and not an observed one.

## Not proved

- That each tiling without a point where four tiles meet has exactly one placement sequence.
- That the singular and constant cases never occur.
- That the renaming of slots relates the Rust code to the model of the default method, and that the floating-point code meets the specifications of `Numerics`.
- That the exact divisions made when the size of a tile is carried through the later eliminations (`carryExact`) succeed; the model treats a failure there as an unsettled root.
- Anything about the counts of sequences per proportion or the statistics of a search.
