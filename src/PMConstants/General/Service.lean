import Mathlib.Tactic

/-! Bounded queues with repeatable finite-cycle demand and service.
Work may vary within a cycle. Persistence forces equality of cycle totals,
not pointwise service and not a uniform phase/direction measure.
No substrate or constant is imported. -/
namespace PMConstants.General.Service
open Finset

theorem constant_drift_formula (q : ℕ → ℝ) (d : ℝ)
    (hstep : ∀ n, q (n+1) = q n + d) (n : ℕ) : q n = q 0 + n*d := by
  induction n with
  | zero => simp
  | succ n ih => rw [hstep, ih]; push_cast; ring

/-- Finite-capacity persistence excludes a nonzero constant backlog drift. -/
theorem bounded_drift_zero (q : ℕ → ℝ) (d C : ℝ)
    (hstep : ∀ n, q (n+1) = q n + d)
    (hbounded : ∀ n, 0 ≤ q n ∧ q n ≤ C) : d = 0 := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · obtain ⟨n, hn⟩ := exists_nat_gt (q 0 / (-d))
    have h := (div_lt_iff₀ (by linarith : 0 < -d)).mp hn
    have hq := (hbounded n).1
    rw [constant_drift_formula q d hstep n] at hq
    nlinarith
  · exact hd
  · obtain ⟨n, hn⟩ := exists_nat_gt ((C-q 0)/d)
    have h := (div_lt_iff₀ hd).mp hn
    have hq := (hbounded n).2
    rw [constant_drift_formula q d hstep n] at hq
    nlinarith


/-- Finite telescoping of the queue differences within one cycle. -/
theorem telescope {N : ℕ} (q : Fin (N+1) → ℝ) :
    (∑ t : Fin N, (q t.succ-q t.castSucc)) = q (Fin.last N)-q 0 := by
  rw [sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

/-- The pointwise queue equation implies the total cycle balance. -/
theorem cycle_balance {N : ℕ} (q : Fin (N+1) → ℝ)
    (demand service : Fin N → ℝ) (rate : ℝ)
    (hstep : ∀ t, q t.succ = q t.castSucc + rate*demand t-service t) :
    q (Fin.last N)-q 0 = rate*(∑ t, demand t)-(∑ t, service t) := by
  rw [← telescope]
  have heq : ∀ t, q t.succ-q t.castSucc = rate*demand t-service t := by
    intro t; rw [hstep]; ring
  simp_rw [heq]
  rw [sum_sub_distrib, mul_sum]

/-- Repeating a workload with finite backlog forces cycle-total service.
The queue may vary within and between cycles; only its boundary values need
bounds. There is no pointwise equality of arrivals and service hypothesis. -/
theorem persistent_cycle_service {N : ℕ} (q : ℕ → Fin (N+1) → ℝ)
    (demand service : Fin N → ℝ) (rate C : ℝ)
    (hstep : ∀ n t, q n t.succ = q n t.castSucc + rate*demand t-service t)
    (hlink : ∀ n, q (n+1) 0 = q n (Fin.last N))
    (hbounded : ∀ n, 0 ≤ q n 0 ∧ q n 0 ≤ C) :
    (∑ t, service t) = rate*(∑ t, demand t) := by
  have hz := bounded_drift_zero (fun n => q n 0)
    (rate*(∑ t, demand t)-(∑ t, service t)) C
    (fun n => by
      have h := cycle_balance (q n) demand service rate (hstep n)
      rw [hlink]; linarith) hbounded
  linarith

/-- With a common nonzero operation rate, cycle-total resource shares equal
cycle-total demand shares. No choice of per-trial normalized readout is made. -/
theorem normalized_cycle_share {I : Type*} [Fintype I] {N : ℕ}
    (q : I → ℕ → Fin (N+1) → ℝ)
    (demand service : I → Fin N → ℝ) (rate : ℝ) (C : I → ℝ)
    (hr : rate ≠ 0)
    (hstep : ∀ i n t, q i n t.succ = q i n t.castSucc + rate*demand i t-service i t)
    (hlink : ∀ i n, q i (n+1) 0 = q i n (Fin.last N))
    (hbounded : ∀ i n, 0 ≤ q i n 0 ∧ q i n 0 ≤ C i) (i : I) :
    (∑ t, service i t)/(∑ j, ∑ t, service j t) =
      (∑ t, demand i t)/(∑ j, ∑ t, demand j t) := by
  have hb : ∀ j, (∑ t, service j t) = rate*(∑ t, demand j t) := fun j =>
    persistent_cycle_service (q j) (demand j) (service j) rate (C j)
      (hstep j) (hlink j) (hbounded j)
  simp_rw [hb]
  rw [← mul_sum]
  exact mul_div_mul_left _ _ hr

end PMConstants.General.Service
