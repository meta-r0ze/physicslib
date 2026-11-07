import PMAtoms.E8Tick
import Mathlib.Tactic

/-! **Experimental/candidate module.**

# Clock composition laws

The substrate supplies one raw tick `Δ = 43`.  This module records three
distinct ways a system can compose that tick:

* nested gating: `period = k₁ · k₂ · … · Δ`
* parallel channels: `rate = Σ rateᵢ`
* serial waits: `lifetime = Σ lifetimeᵢ`

They are not interchangeable.  The module only records the algebra; the E8
composition rule remains a model question.
-/

noncomputable section
namespace PMAtoms
open scoped BigOperators

/-- Nested clock period: each level multiplies the previous period by an
integer gate factor. -/
def nestedPeriod : List Nat → ℝ
  | [] => e8Tick
  | k :: ks => (k : ℝ) * nestedPeriod ks

theorem nestedPeriod_nil : nestedPeriod [] = e8Tick := rfl

theorem nestedPeriod_cons (k : Nat) (ks : List Nat) :
    nestedPeriod (k :: ks) = (k : ℝ) * nestedPeriod ks := rfl

theorem nestedPeriod_eq_prod_mul_tick (factors : List Nat) :
    nestedPeriod factors = (factors.prod : ℝ) * e8Tick := by
  induction factors with
  | nil => simp [nestedPeriod]
  | cons k ks ih =>
      simp [nestedPeriod, List.prod_cons, ih]
      ring

theorem nestedPeriod_pos {factors : List Nat}
    (h : ∀ k ∈ factors, 0 < k) : 0 < nestedPeriod factors := by
  induction factors with
  | nil => unfold nestedPeriod; rw [e8Tick_eq]; norm_num
  | cons k ks ih =>
      rw [nestedPeriod_cons]
      have hk : (0 : ℝ) < k := by exact_mod_cast h k (by simp)
      have hks : 0 < nestedPeriod ks := ih (by intro j hj; exact h j (by simp [hj]))
      exact mul_pos hk hks

/-- Nested clock flux: one over the nested period. -/
def nestedFlux (factors : List Nat) : ℝ := 1 / nestedPeriod factors

theorem nestedFlux_eq (factors : List Nat) :
    nestedFlux factors = 1 / nestedPeriod factors := rfl

theorem nestedFlux_pos {factors : List Nat}
    (h : ∀ k ∈ factors, 0 < k) : 0 < nestedFlux factors :=
  one_div_pos.mpr (nestedPeriod_pos h)

/-- Parallel channel rate: rates add. -/
def parallelRate (rates : List ℝ) : ℝ := rates.sum

theorem parallelRate_nil : parallelRate [] = 0 := rfl

theorem parallelRate_cons (r : ℝ) (rs : List ℝ) :
    parallelRate (r :: rs) = r + parallelRate rs := rfl

/-- Serial independent waits: lifetimes add. -/
def serialLifetime (lifetimes : List ℝ) : ℝ := lifetimes.sum

theorem serialLifetime_nil : serialLifetime [] = 0 := rfl

theorem serialLifetime_cons (t : ℝ) (ts : List ℝ) :
    serialLifetime (t :: ts) = t + serialLifetime ts := rfl

/-- Gated rate: nested flux times a per-cycle weight. -/
def clockDividedRate (factors : List Nat) (weight : ℝ) : ℝ :=
  nestedFlux factors * weight

theorem clockDividedRate_eq (factors : List Nat) (weight : ℝ) :
    clockDividedRate factors weight = weight / nestedPeriod factors := by
  unfold clockDividedRate nestedFlux
  ring

theorem clockDividedRate_pos {factors : List Nat} {weight : ℝ}
    (h : ∀ k ∈ factors, 0 < k) (hw : 0 < weight) :
    0 < clockDividedRate factors weight :=
  mul_pos (nestedFlux_pos h) hw

end PMAtoms
