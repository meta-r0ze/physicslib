import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# How far the defect gap survives a perturbation

`DefectGap` proves a volume-uniform gap for PM's diagonal cost: energy `0` on the vacuum,
at least `m` on every excitation. A transfer matrix also has an off-diagonal part (for the
distinction substrate, flips between ticks). This file states, at the level of quadratic forms, how much of
that the gap tolerates. It is the min–max statement without eigenvalue machinery.

Data: a finite label set `ι`, a vacuum predicate `vac`, a diagonal energy `e` with `e = 0` on
the vacuum and `e ≥ m` off it, and a perturbation form `W` with `|W v| ≤ ε ‖v‖²`.

* `diagForm_ge`: on vectors vanishing on the vacuum, `m ‖v‖² ≤ ⟨v, e v⟩`.
* `diagForm_vacuum`: on vectors supported on the vacuum, `⟨u, e u⟩ = 0`.
* `excited_lower`: the perturbed form is at least `(m − ε) ‖v‖²` on the excited sector.
* `vacuum_upper`: the perturbed form is at most `ε ‖u‖²` on the vacuum sector.
* `gap_stable`: for unit vectors, the excited sector sits at least `m − 2ε` above the vacuum
  sector; so the gap survives whenever `ε < m / 2`.

## The limit of form bounds

For `DefectGap`, `m = 1` transition for every volume. A local off-diagonal term is a sum over
sites, so its form bound `ε` grows with the number of sites, and `gap_stable` gives a
volume-uniform gap only when the off-diagonal part is bounded uniformly in volume. For the
distinction substrate that condition is removed by the cluster expansion
(`SlabGap.slab_gap_explicit`). The gauge layer is a separate continuous field, and its gap is the
out-of-scope quantum Yang–Mills problem (`MassGap/README.md`).
-/

namespace PMAction.MassGap.GapStability
open Finset

variable {ι : Type*} [Fintype ι]

/-- Squared `ℓ²` norm. -/
def normSq (v : ι → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Quadratic form of the diagonal energy `e`. -/
def diagForm (e v : ι → ℝ) : ℝ := ∑ i, e i * v i ^ 2

theorem normSq_nonneg (v : ι → ℝ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

/-- **Diagonal gap on the excited sector.** -/
theorem diagForm_ge (vac : ι → Prop) (m : ℝ) (e v : ι → ℝ) (he : ∀ i, ¬ vac i → m ≤ e i)
    (hv : ∀ i, vac i → v i = 0) : m * normSq v ≤ diagForm e v := by
  unfold normSq diagForm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : vac i
  · simp [hv i h]
  · exact mul_le_mul_of_nonneg_right (he i h) (sq_nonneg _)

/-- **The vacuum sector has zero diagonal energy.** -/
theorem diagForm_vacuum (vac : ι → Prop) (e u : ι → ℝ) (he0 : ∀ i, vac i → e i = 0)
    (hu : ∀ i, ¬ vac i → u i = 0) : diagForm e u = 0 := by
  unfold diagForm
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : vac i
  · simp [he0 i h]
  · simp [hu i h]

/-- **Perturbed form, excited sector.** -/
theorem excited_lower (vac : ι → Prop) (m ε : ℝ) (e : ι → ℝ) (W : (ι → ℝ) → ℝ)
    (he : ∀ i, ¬ vac i → m ≤ e i) (hW : ∀ v, |W v| ≤ ε * normSq v)
    (v : ι → ℝ) (hv : ∀ i, vac i → v i = 0) :
    (m - ε) * normSq v ≤ diagForm e v + W v := by
  have h1 := diagForm_ge vac m e v he hv
  have h2 := (abs_le.mp (hW v)).1
  rw [sub_mul]
  linarith

/-- **Perturbed form, vacuum sector.** -/
theorem vacuum_upper (vac : ι → Prop) (ε : ℝ) (e : ι → ℝ) (W : (ι → ℝ) → ℝ)
    (he0 : ∀ i, vac i → e i = 0) (hW : ∀ v, |W v| ≤ ε * normSq v)
    (u : ι → ℝ) (hu : ∀ i, ¬ vac i → u i = 0) :
    diagForm e u + W u ≤ ε * normSq u := by
  have h1 := diagForm_vacuum vac e u he0 hu
  have h2 := (abs_le.mp (hW u)).2
  linarith

/-- **Gap stability.** For unit vectors, the perturbed form on the excited sector exceeds the
perturbed form on the vacuum sector by at least `m − 2ε`. In particular the gap survives
whenever `ε < m / 2`. -/
theorem gap_stable (vac : ι → Prop) (m ε : ℝ) (e : ι → ℝ) (W : (ι → ℝ) → ℝ)
    (he0 : ∀ i, vac i → e i = 0) (he : ∀ i, ¬ vac i → m ≤ e i)
    (hW : ∀ v, |W v| ≤ ε * normSq v)
    (v u : ι → ℝ) (hv : ∀ i, vac i → v i = 0) (hu : ∀ i, ¬ vac i → u i = 0)
    (hv1 : normSq v = 1) (hu1 : normSq u = 1) :
    m - 2 * ε ≤ (diagForm e v + W v) - (diagForm e u + W u) := by
  have h1 := excited_lower vac m ε e W he hW v hv
  have h2 := vacuum_upper vac ε e W he0 hW u hu
  rw [hv1, mul_one] at h1
  rw [hu1, mul_one] at h2
  linarith

/-- The gap is strictly positive when the perturbation is below half the diagonal gap. -/
theorem gap_pos (vac : ι → Prop) (m ε : ℝ) (e : ι → ℝ) (W : (ι → ℝ) → ℝ)
    (he0 : ∀ i, vac i → e i = 0) (he : ∀ i, ¬ vac i → m ≤ e i)
    (hW : ∀ v, |W v| ≤ ε * normSq v) (hε : ε < m / 2)
    (v u : ι → ℝ) (hv : ∀ i, vac i → v i = 0) (hu : ∀ i, ¬ vac i → u i = 0)
    (hv1 : normSq v = 1) (hu1 : normSq u = 1) :
    diagForm e u + W u < diagForm e v + W v := by
  have := gap_stable vac m ε e W he0 he hW v u hv hu hv1 hu1
  linarith

end PMAction.MassGap.GapStability
