# Fair Dice from Curvature: Alexandrov's Theorem, Machine-Checked (Lean 4 + Mathlib)

Author: DICTO.

## The theorems

Let `n 0, …, n (N-1)` be distinct unit vectors in 3-space, not all in one closed hemisphere. A polytope with corners
on these rays has its corners at `r i • n i` with `r i > 0`; its curvature at a corner is the area of the outer unit
normals there, defined in Lean as three times the volume of the normal cone inside the unit ball (the solid angle of a
face is likewise three times the volume of the cone through it inside the unit ball). A die with these face normals is `{x | ⟪n j, x⟫ ≤ d j for all j}` with `d j > 0`; it is fair about the
origin when every face is seen from the origin under the solid angle `4π / N`.

- **Alexandrov's theorem, polytope case** (`alexandrov_iff`): for positive curvatures `κ j`, a polytope with
  corners on the rays and curvature `κ j` at corner `j` exists if and only if `Σ κ j = 4π` and Alexandrov's condition
  holds: for every nonempty proper set `I` of rays, `Σ_{i ∈ I} κ i` is less than the area of the directions within
  π/2 of some ray in `I`. The condition is stated over sets of rays; its equivalence with the textbook form over
  spherically convex sets is not formalized.
- **Uniqueness** (`alexandrov_unique`): two such polytopes are equal up to scaling about the origin.
- **#112 Lemma 1, the polar identity** (`solidAngle_eq_curvature`): the solid angle of face `k` of the die equals
  the curvature of the polar polytope (corners `n j / d j`) at its corner `n k / d k`.
- **#112 Theorem A (a)** (`fair_die_iff`, `fair_die_unique`): a fair die with face normals `n` exists if and only if
  Alexandrov's condition holds for the equal curvatures `4π / N`, and it is then unique up to scale.

The theorem is Alexandrov's (1942); the polytope case was proved by Oliker (2007) and Bertrand (2016). Existence here
follows Oliker's variational route; uniqueness is by the maximum principle.

- `Challenge.lean`: the definitions and the five statements, with every proof `sorry`. It imports only Mathlib.
- `Solution.lean`: the proofs, from the library.
- `Alexandrov/`: the library (namespace `Alexandrov`).

Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib `v4.35.0-rc2`. The theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. `Challenge.lean` contains `sorry` by design (the statements only);
`Solution.lean` and the library contain no `sorry`, and `native_decide` is not used. Every Lean file uses the module
system.

## How to check

```
lake exe cache get
lake build
```

## Files

| file | content |
|---|---|
| `Alexandrov/Basic.lean` | normal cone, curvature, the polytope with corners on rays; the normal cone at a corner is its cell |
| `Alexandrov/Comparison.lean` | the comparison lemma (maximum principle) |
| `Alexandrov/Uniqueness.lean` | uniqueness up to scaling |
| `Alexandrov/Total.lean` | the curvatures add up to 4π |
| `Alexandrov/Continuity.lean` | the curvature at a corner is continuous in the radii |
| `Alexandrov/Monotone.lean` | moving one corner outward enlarges its cell and shrinks the others |
| `Alexandrov/Necessity.lean`, `Alexandrov/Hemisphere.lean` | necessity of Alexandrov's condition (also for spherically convex sets) |
| `Alexandrov/Variational.lean` | at a maximizer of Oliker's functional every corner has the prescribed curvature |
| `Alexandrov/Functional.lean`, `Alexandrov/PhiContinuity.lean` | Oliker's functional: integrability, scaling, continuity |
| `Alexandrov/Margin.lean`, `Alexandrov/Coercive.lean` | a uniform margin in Alexandrov's condition; coercivity |
| `Alexandrov/Existence.lean` | existence of a maximizer, hence of the polytope |
| `Alexandrov/Main.lean` | Alexandrov's theorem, polytope case: `alexandrov_iff`, `alexandrov_unique` |
| `Alexandrov/Dice.lean` | fair dice: the polar identity and Theorem A (a) |

## Earlier work

The theorem is Alexandrov's: A. D. Alexandrov, Doklady Acad. Sci. URSS 35 (1942) 131–134. The polytope case and the
variational functional are from V. Oliker, Adv. Math. 213 (2007) 600–620 (Theorems 4 and 6), and the statement of
Alexandrov's condition and its necessity from J. Bertrand, Geom. Dedicata 183 (2016) 81–99 (Theorem 1.2). The
companion problem for face areas is Minkowski's theorem (H. Minkowski, Nachr. Ges. Wiss. Göttingen 1897; a modern
proof by D. A. Klain, Adv. Math. 185 (2004) 270–288). The application to fair dice (Lemma 1 and Theorem A (a)) is
from the paper below (#112). We found no earlier machine-checked proof of Alexandrov's theorem on prescribed
curvature or of the fair-die theorem; `formalization.yaml` lists every source checked.

## Papers

- DICTO, *Fair Dice — The Aequi: Enumerating the Innumerable*, Zenodo, DICTO DOI: 10.5281/zenodo.24383314.

## How it was made

DICTO set the question and the order of the work, with Claude (Anthropic): the Lean code was written by a Claude Code
agent. `formalization.yaml` (section `automation`) records this in full.

## Checks

`scripts/check-lean-sources.py` and `scripts/verify-comparator.sh` come from Palomar's entry template (PalomarRegistry).
They check the source rules and run `lake comparator` the way Palomar does.

## Licence

Apache-2.0 (see `LICENSE`). Copyright 2026 DICTO.

## Other work by DICTO

- ORCID (all works): https://orcid.org/0009-0001-2620-2036
- Website: https://dictospheres.com
