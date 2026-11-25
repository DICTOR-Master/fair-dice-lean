module

public import Mathlib
public import Alexandrov

@[expose] public section

/-!
# Fair dice from curvature: Alexandrov's theorem, polyhedral case

**Informal statement.** `n 0, …, n (N-1)` are distinct unit vectors in Euclidean 3-space `E3`, not all in one
closed hemisphere (`∀ x ≠ 0, ∃ i, 0 < ⟪n i, x⟫`).

* The polytope `rayPolytope n r` is the convex hull of the corners `corner n r i = r i • n i` (`r i > 0`). Its
  curvature at a point `p` (`curvature`) is the area of its outer unit normals there, computed as three times the
  volume of the normal cone (`normalCone`) inside the unit ball.
* `nbhd n 0 I` is the set of directions within an angle less than π/2 of some ray `n i`, `i ∈ I`.
  `AlexandrovCondition n κ`: for every nonempty proper set `I` of rays, `Σ_{i ∈ I} κ i` is less than the area of
  that neighbourhood.
* The die `die n d` is `{x | ∀ j, ⟪n j, x⟫ ≤ d j}`. The solid angle of face `k` (`solidAngle`) is the area of
  the directions whose ray from the origin leaves the die through face `k` (`faceCone`). The die is fair about
  the origin (`IsFair`) when every face has solid angle `4π / N`.

1. `alexandrov_iff` (**Alexandrov's theorem, existence**): for `κ j > 0`, a polytope with corners `r i • n i`
   and curvature `κ j` at every corner exists if and only if `Σ κ j = 4π` and Alexandrov's condition holds.
2. `alexandrov_unique` (**uniqueness**): two such polytopes are equal up to scaling about the origin.
3. `solidAngle_eq_curvature` (**#112 Lemma 1, the polar identity**): the solid angle of face `k` of the die
   equals the curvature of the polar polytope (corners `n j / d j`) at its corner `n k / d k`.
4. `fair_die_iff` (**#112 Theorem A (a), existence**): a fair die with face normals `n` exists if and only if
   Alexandrov's condition holds for the equal curvatures `4π / N`.
5. `fair_die_unique` (**#112 Theorem A (a), uniqueness**): two fair dice with the same face normals are equal up
   to scaling about the origin.

**Sources.** A. D. Alexandrov's theorem on prescribed integral curvature, in the variational form of V. Oliker,
Adv. Math. 213 (2007), and the necessity of J. Bertrand, Geom. Dedicata 183 (2016); DICTO's paper #112: Lemma 1
and Theorem A (a). Every definition and statement is copied from the Lean library `Alexandrov` (namespace
`Alexandrov`, here `FairDice`); the comment before each group names its file.
-/

namespace FairDice

-- from Basic.lean
section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {N : ℕ}

/-- The cone of outer normals of a set `Q` at a point `p`. -/
def normalCone (Q : Set E3) (p : E3) : Set E3 :=
  {x | ∀ q ∈ Q, ⟪q, x⟫ ≤ ⟪p, x⟫}

/-- Integral Gauss curvature of `Q` at `p`: the area of the set of outer unit normals at `p`,
computed as three times the volume of the normal cone inside the unit ball. -/
noncomputable def curvature (Q : Set E3) (p : E3) : ℝ≥0∞ :=
  3 * volume (normalCone Q p ∩ ball (0 : E3) 1)

/-- The corner on ray `i`: the point at distance `r i` along the unit vector `n i`. -/
def corner (n : Fin N → E3) (r : Fin N → ℝ) (i : Fin N) : E3 := r i • n i

/-- The polytope with its corners on the given rays. -/
def rayPolytope (n : Fin N → E3) (r : Fin N → ℝ) : Set E3 :=
  convexHull ℝ (range (corner n r))

end

-- from Margin.lean
section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

variable {N : ℕ}

/-- Directions making an angle less than `arccos ε` with some ray in `I`. -/
def nbhd (n : Fin N → E3) (ε : ℝ) (I : Finset (Fin N)) : Set E3 :=
  {x | ∃ i ∈ I, ε * ‖x‖ < ⟪n i, x⟫}

end

-- from Main.lean
section
open MeasureTheory Set Metric Finset
open scoped RealInnerProductSpace ENNReal

variable {N : ℕ}

/-- Alexandrov's condition for prescribed curvatures `κ` at the corners on the rays `n`. -/
def AlexandrovCondition (n : Fin N → E3) (κ : Fin N → ℝ) : Prop :=
  ∀ I : Finset (Fin N), I.Nonempty → I ≠ Finset.univ →
    ∑ i ∈ I, κ i < 3 * (volume (nbhd n 0 I ∩ ball (0 : E3) 1)).toReal

/-- **Alexandrov's theorem, polyhedral case: existence.** -/
theorem alexandrov_iff [NeZero N] {n : Fin N → E3} (hn : ∀ i, ‖n i‖ = 1)
    (hinj : Function.Injective n) (hspan : ∀ x : E3, x ≠ 0 → ∃ i, 0 < ⟪n i, x⟫)
    {κ : Fin N → ℝ} (hκ : ∀ j, 0 < κ j) :
    (∃ r : Fin N → ℝ, (∀ i, 0 < r i) ∧
      ∀ j, curvature (rayPolytope n r) (corner n r j) = ENNReal.ofReal (κ j)) ↔
    (∑ j, κ j = 4 * Real.pi ∧ AlexandrovCondition n κ) := by
  exact Alexandrov.alexandrov_iff hn hinj hspan hκ

/-- **Alexandrov's theorem, polyhedral case: uniqueness up to scaling.** -/
theorem alexandrov_unique {n : Fin N → E3} (hn : ∀ i, ‖n i‖ = 1)
    (hinj : Function.Injective n) (hspan : ∀ x : E3, x ≠ 0 → ∃ i, 0 < ⟪n i, x⟫)
    {κ : Fin N → ℝ} (hκ : ∀ j, 0 < κ j) {r r' : Fin N → ℝ} (hr : ∀ i, 0 < r i)
    (hr' : ∀ i, 0 < r' i)
    (hc : ∀ j, curvature (rayPolytope n r) (corner n r j) = ENNReal.ofReal (κ j))
    (hc' : ∀ j, curvature (rayPolytope n r') (corner n r' j) = ENNReal.ofReal (κ j)) :
    ∃ c : ℝ, 0 < c ∧ r' = c • r := by
  exact Alexandrov.alexandrov_unique hn hinj hspan hκ hr hr' hc hc'

end

-- from Dice.lean
section
open MeasureTheory Set Metric Finset
open scoped RealInnerProductSpace ENNReal

variable {N : ℕ}

/-- The die with face normals `n j` at distances `d j` from the origin. -/
def die (n : Fin N → E3) (d : Fin N → ℝ) : Set E3 := {x | ∀ j, ⟪n j, x⟫ ≤ d j}

/-- Directions `x` whose ray from the origin leaves the die through face `k`. -/
def faceCone (n : Fin N → E3) (d : Fin N → ℝ) (k : Fin N) : Set E3 :=
  {x | ∃ t : ℝ, 0 < t ∧ t • x ∈ die n d ∧ ⟪n k, t • x⟫ = d k}

/-- The solid angle of face `k` seen from the origin (area of the directions through it). -/
noncomputable def solidAngle (n : Fin N → E3) (d : Fin N → ℝ) (k : Fin N) : ℝ≥0∞ :=
  3 * volume (faceCone n d k ∩ ball (0 : E3) 1)

/-- A die is fair about the origin when all `N` faces have solid angle `4π / N`. -/
def IsFair (n : Fin N → E3) (d : Fin N → ℝ) : Prop :=
  ∀ k, solidAngle n d k = ENNReal.ofReal (4 * Real.pi / N)

/-- **#112 Lemma 1 (the polar identity).** -/
theorem solidAngle_eq_curvature {n : Fin N → E3} (hspan : ∀ x : E3, x ≠ 0 → ∃ i, 0 < ⟪n i, x⟫)
    {d : Fin N → ℝ} (hd : ∀ j, 0 < d j) (k : Fin N) :
    solidAngle n d k =
      curvature (rayPolytope n fun j => (d j)⁻¹) (corner n (fun j => (d j)⁻¹) k) := by
  exact Alexandrov.solidAngle_eq_curvature hspan hd k

/-- **#112 Theorem A (a), existence.** A fair die with face normals `n` exists if and only if
Alexandrov's condition holds for the equal curvatures `4π / N`. -/
theorem fair_die_iff [NeZero N] {n : Fin N → E3} (hn : ∀ i, ‖n i‖ = 1)
    (hinj : Function.Injective n) (hspan : ∀ x : E3, x ≠ 0 → ∃ i, 0 < ⟪n i, x⟫) :
    (∃ d : Fin N → ℝ, (∀ j, 0 < d j) ∧ IsFair n d) ↔
      AlexandrovCondition n (fun _ => 4 * Real.pi / N) := by
  exact Alexandrov.fair_die_iff hn hinj hspan

/-- **Uniqueness of the fair die.** Two fair dice with the same face normals are equal up to
scaling about the origin. -/
theorem fair_die_unique [NeZero N] {n : Fin N → E3} (hn : ∀ i, ‖n i‖ = 1)
    (hinj : Function.Injective n) (hspan : ∀ x : E3, x ≠ 0 → ∃ i, 0 < ⟪n i, x⟫)
    {d d' : Fin N → ℝ} (hd : ∀ j, 0 < d j) (hd' : ∀ j, 0 < d' j)
    (hf : IsFair n d) (hf' : IsFair n d') : ∃ c : ℝ, 0 < c ∧ d' = c • d := by
  exact Alexandrov.fair_die_unique hn hinj hspan hd hd' hf hf'

end

end FairDice
