import Mathlib.Tactic

/-!
# Nested Rule 1: Capacity Partitioning

The partition rule of Nested Persistence (`PM-3-Nested/paper/2_nested_persistence.tex`,
"Capacity Partitioning"). Work `w i` demanded by task `i` is served by subsystems `j` with
capacity `C j` and interface overhead `h j`. A feasible allocation `s i j ≥ 0` serves every
task (`∑ j, s i j = w i`) and fits every subsystem (`∑ i, s i j + h j ≤ C j`).

* `global_budget`: feasibility implies `∑ w + ∑ h ≤ ∑ C`.
* `count_lower_bound`: with equal capacity `C > 0`, the number of subsystems is at least
  `(∑ w + ∑ h)/C`.
* `bounded_backlog_zero_drift`, `service_balance`: in a repeating cycle, a queue whose
  boundary backlog stays bounded has zero net drift, so cycle-total service equals
  `ρ ·` cycle-total demand.

These are necessary conditions. They do not construct a schedule or select a unique split.
No substrate is assumed here.
-/

namespace PersistenceMechanics.CapacityPartitioning

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A feasible allocation of demands `w` to subsystems with capacity `C` and overhead `h`. -/
structure Feasible (w : I → ℝ) (C h : J → ℝ) (s : I → J → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ s i j
  serves : ∀ i, ∑ j, s i j = w i
  fits : ∀ j, ∑ i, s i j + h j ≤ C j

/-- **The global budget.** -/
theorem global_budget {w : I → ℝ} {C h : J → ℝ} {s : I → J → ℝ} (hf : Feasible w C h s) :
    ∑ i, w i + ∑ j, h j ≤ ∑ j, C j := by
  have hw : ∑ i, w i = ∑ j, ∑ i, s i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (hf.serves i).symm
  calc ∑ i, w i + ∑ j, h j = ∑ j, (∑ i, s i j + h j) := by
        rw [hw, Finset.sum_add_distrib]
    _ ≤ ∑ j, C j := Finset.sum_le_sum fun j _ => hf.fits j

/-- **Subsystem count.** With equal capacity `Cc > 0` there are at least
`(∑ w + ∑ h)/Cc` subsystems. -/
theorem count_lower_bound {w : I → ℝ} {h : J → ℝ} {s : I → J → ℝ} {Cc : ℝ} (hC : 0 < Cc)
    (hf : Feasible w (fun _ => Cc) h s) :
    (∑ i, w i + ∑ j, h j) / Cc ≤ Fintype.card J := by
  have hb := global_budget hf
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hb
  rw [div_le_iff₀ hC]
  exact hb

/-- **Bounded backlog forces zero drift.** If the boundary queue `q0 + n D` stays within `B`
for every cycle `n`, then `D = 0`. -/
theorem bounded_backlog_zero_drift (q0 D B : ℝ) (h : ∀ n : ℕ, |q0 + n * D| ≤ B) : D = 0 := by
  by_contra hD
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · obtain ⟨n, hn⟩ := exists_nat_gt ((q0 + B) / (-D))
    have hb := (abs_le.mp (h n)).1
    have hlt : q0 + B < n * (-D) := by rwa [div_lt_iff₀ (by linarith)] at hn
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_gt ((B - q0) / D)
    have hb := (abs_le.mp (h n)).2
    have hlt : B - q0 < n * D := by rwa [div_lt_iff₀ hpos] at hn
    linarith

/-- **Service balance over a cycle.** Bounded backlog with per-cycle drift
`ρ · demand − service` forces `service = ρ · demand`. -/
theorem service_balance (q0 ρ Sd Ss B : ℝ) (h : ∀ n : ℕ, |q0 + n * (ρ * Sd - Ss)| ≤ B) :
    Ss = ρ * Sd := by
  have := bounded_backlog_zero_drift q0 _ B h
  linarith

/-- Constant queue increments give the canonical affine backlog. -/
theorem constant_drift_formula (q : ℕ → ℝ) (d : ℝ)
    (hstep : ∀ n, q (n+1) = q n+d) (n : ℕ) : q n = q 0+n*d := by
  induction n with
  | zero => simp
  | succ n ih => rw [hstep,ih]; push_cast; ring

/-- Convert nonnegative finite queue bounds to the canonical absolute-backlog hypothesis. -/
theorem queue_absolute_bound (q : ℕ → ℝ) (d C : ℝ)
    (hstep : ∀ n, q (n+1) = q n+d)
    (hbounded : ∀ n, 0 ≤ q n ∧ q n ≤ C) :
    ∀ n : ℕ, |q 0+n*d| ≤ C := by
  intro n
  rw [← constant_drift_formula q d hstep n, abs_of_nonneg (hbounded n).1]
  exact (hbounded n).2

/-- The queue and absolute-backlog presentations are equivalent when the
nonnegative initial queue from the queue hypotheses is retained. -/
theorem bounded_queue_iff (q : ℕ → ℝ) (d : ℝ)
    (hstep : ∀ n, q (n+1) = q n+d) :
    (∃ C, ∀ n, 0 ≤ q n ∧ q n ≤ C) ↔
      0 ≤ q 0 ∧ ∃ B, ∀ n : ℕ, |q 0+n*d| ≤ B := by
  constructor
  · rintro ⟨C,h⟩
    exact ⟨(h 0).1,C,queue_absolute_bound q d C hstep h⟩
  · rintro ⟨h0,B,h⟩
    have hd := bounded_backlog_zero_drift (q 0) d B h
    refine ⟨q 0,fun n => ?_⟩
    rw [constant_drift_formula q d hstep n,hd]
    simpa using And.intro h0 (le_refl (q 0))

/-- The structure is exactly the conjunction form of the allocation rule. -/
theorem feasible_iff (w : I → ℝ) (C h : J → ℝ) (s : I → J → ℝ) :
    Feasible w C h s ↔ (∀ i j, 0 ≤ s i j) ∧
      (∀ i, ∑ j, s i j = w i) ∧ (∀ j, (∑ i, s i j)+h j ≤ C j) :=
  ⟨fun hf => ⟨hf.nonneg, hf.serves, hf.fits⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Splitting an unchanged insufficient total budget cannot remove overload. -/
theorem no_allocation_under_overload (demand : I → ℝ)
    (capacity overhead : J → ℝ) (hcost : ∀ j, 0 ≤ overhead j)
    (hover : (∑ j, capacity j) < ∑ i, demand i) :
    ¬ ∃ service, Feasible demand capacity overhead service := by
  rintro ⟨service, h⟩
  have hb := global_budget h
  have ho : 0 ≤ ∑ j, overhead j := sum_nonneg (fun j _ => hcost j)
  linarith

/-- A continuum of distinct divisions can obey the same capacity constraints. -/
theorem feasible_family (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Feasible (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => 0) (fun _ j => if j = 0 then p else 1-p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; split_ifs <;> linarith
  · intro i; norm_num [Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [Fin.sum_univ_succ] <;> linarith

/-- Persistence feasibility does not imply full utilization of every worker. -/
theorem feasible_with_idle_capacity :
    Feasible (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => 0) (fun _ j => if j = 0 then 1 else 0) ∧
      (∑ _i : Fin 1, (1 : ℝ)) < ∑ _j : Fin 2, (1 : ℝ) := by
  constructor
  · simpa using feasible_family 1 (by norm_num) (by norm_num)
  · norm_num

end PersistenceMechanics.CapacityPartitioning
