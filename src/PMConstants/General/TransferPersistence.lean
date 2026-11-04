import Mathlib.Tactic

/-!
# What persists for transfer between subsystems

Two candidate transfer policies for a shared resource: equal-rate transfer
between all pairs, or directional transfer prioritising the reference direction.
Ask what persists. Bounded queues and a fixed total transfer budget select which
policies are sustainable.

* starvation_grows_linearly: a policy that starves any queue accumulates
  unbounded backlog. The drift d - s > 0 per phase means the backlog exceeds any
  finite bound B after sufficiently many phases.
* persistence_selects_equal: under bounded backlog, service must equal demand.
  A policy that starves any queue cannot persist.

Premise: the work vector (demand per phase) is given. No physical identification
of generation pairs with transfer directions is made here.
-/
noncomputable section
namespace PMConstants.General.TransferPersistence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A positive drift accumulates unbounded backlog over time.
If d - s > 0, then for any B there exists n such that drift * n > B. -/
theorem starvation_grows_linearly (d s : ι -> ℝ)
    (hdrift : (∑ j : ι, d j) - (∑ j : ι, s j) > 0) :
    ∀ B : ℝ, ∃ n : ℕ, (∑ j : ι, (d j - s j)) * ↑n > B := by
  intro B
  let drift := (∑ j : ι, d j) - (∑ j : ι, s j)
  have hpos : 0 < drift := hdrift
  obtain ⟨n, hn⟩ := exists_nat_gt (B / drift)
  use n
  calc
    (∑ j : ι, (d j - s j)) * ↑n = ((∑ j : ι, d j) - (∑ j : ι, s j)) * ↑n := by
      rw [Finset.sum_sub_distrib]
    _ > drift * (B / drift) := by
      have h1 : ((∑ j : ι, d j) - (∑ j : ι, s j)) = drift := by simp [drift]
      rw [h1]
      apply mul_lt_mul_of_pos_left hn hpos
    _ = B := by field_simp [hpos.ne']

omit [DecidableEq ι] in
/-- Persistence selects proportional allocation. If bounded backlog is required
and service must not exceed demand per source, then service must equal demand
for each queue. A policy that starves any queue cannot persist. -/
theorem persistence_selects_equal (d s : ι -> ℝ)
    (_hd : ∀ _i : ι, 0 ≤ d _i)
    (_hle : ∀ _ : ι, ∑ j : ι, s j ≤ ∑ j : ι, d j)
    (hbacklog : ∃ B : ℝ, ∀ _ : ι, ∀ n : ℕ, |(∑ j : ι, d j) - (∑ j : ι, s j)| * ↑n ≤ B) :
    ∀ _ : ι, ∑ j : ι, s j = ∑ j : ι, d j := by
  intro i0
  by_contra hneq
  have hstarve : ∑ j : ι, s j < ∑ j : ι, d j := by
    apply lt_of_le_of_ne
    · exact _hle i0
    · intro heq
      apply hneq
      rw [heq]
  have hpos : (∑ j : ι, d j) - (∑ j : ι, s j) > 0 := by linarith [hstarve]
  obtain ⟨B, hB⟩ := hbacklog
  -- For large n, the drift times n exceeds B
  have h_exceeds : ∃ n : ℕ, (∑ j : ι, (d j - s j)) * ↑n > B := by
    apply starvation_grows_linearly d s hpos
  obtain ⟨n, hn⟩ := h_exceeds
  -- The backlog bound says |drift| * n ≤ B for all n
  have h_contra : |(∑ j : ι, d j) - (∑ j : ι, s j)| * ↑n ≤ B := hB i0 n
  -- |drift| = drift since drift > 0
  have h_abs_eq : |(∑ j : ι, d j) - (∑ j : ι, s j)| = (∑ j : ι, d j) - (∑ j : ι, s j) := by
    rw [abs_of_nonneg (le_of_lt hpos)]
  have h_gt : B < |(∑ j : ι, d j) - (∑ j : ι, s j)| * ↑n := by
    calc
      B < (∑ j : ι, (d j - s j)) * ↑n := hn
      _ = ((∑ j : ι, d j) - (∑ j : ι, s j)) * ↑n := by rw [Finset.sum_sub_distrib]
      _ = |(∑ j : ι, d j) - (∑ j : ι, s j)| * ↑n := by rw [h_abs_eq]
  linarith [h_gt, h_contra]

end PMConstants.General.TransferPersistence
