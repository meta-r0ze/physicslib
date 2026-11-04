import PMConstants.Electroweak
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Polynomial.Derivative

/-! Exact interface matching is distinct from a small mismatch. Its unique
positive scalar coupling, if a solution exists, need not equal the separate
bandwidth formula. Taylor inequalities certify a nonzero baseline mismatch.
The radial excitation is normalized as φ=(v+h)/√2. -/
noncomputable section
namespace PMConstants.Matching

def regulator (lam : ℝ) : ℝ := Real.exp (-2*lam) / lam

theorem regulator_strict {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    regulator b < regulator a := by
  have hb : 0 < b := ha.trans hab
  have he : Real.exp (-2*b) < Real.exp (-2*a) :=
    Real.exp_lt_exp.mpr (by linarith)
  unfold regulator
  calc
    Real.exp (-2*b)/b < Real.exp (-2*a)/b := (div_lt_div_iff_of_pos_right hb).mpr he
    _ < Real.exp (-2*a)/a := div_lt_div_of_pos_left (Real.exp_pos _) ha hab

theorem matching_unique {a b aperture : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : regulator a = aperture) (hB : regulator b = aperture) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have := regulator_strict ha h; linarith
  · exact h
  · have := regulator_strict hb h; linarith

/-- Certified rational enclosure; no floating point or numerical axiom. -/
theorem positive_exponential_bounds :
    (1.2954 : ℝ) < Real.exp (2*selfCoupling) ∧
      Real.exp (2*selfCoupling) < 1.2955 := by
  have hlo := Real.sum_le_exp_of_nonneg (show 0 ≤ 2*selfCoupling by
    linarith [self_coupling_pos]) 5
  have hhi := Real.exp_bound' (show 0 ≤ 2*selfCoupling by
    linarith [self_coupling_pos]) (show 2*selfCoupling ≤ 1 by
    norm_num [selfCoupling]) (n := 6) (by decide)
  norm_num [selfCoupling, Finset.sum_range_succ] at hlo hhi ⊢
  constructor <;> linarith

/-- The proposed self-coupling and exact aperture matching are incompatible
without a correction term. This proves the discrepancy, not its origin. -/
theorem baseline_matching_gap :
    (1/2000 : ℝ) < 6*overhead - regulator selfCoupling ∧
      6*overhead - regulator selfCoupling < 1/1000 := by
  obtain ⟨hlo, hhi⟩ := positive_exponential_bounds
  have he := Real.exp_pos (2*selfCoupling)
  have hd : 0 < Real.exp (2*selfCoupling) * selfCoupling :=
    mul_pos he self_coupling_pos
  have hreg : regulator selfCoupling = 1 / (Real.exp (2*selfCoupling) * selfCoupling) := by
    rw [regulator, show -2*selfCoupling = -(2*selfCoupling) by ring, Real.exp_neg]
    simp [div_eq_mul_inv, mul_comm]
  rw [hreg]
  constructor
  · have h : 1 < (6*overhead - 1/2000) * (Real.exp (2*selfCoupling) * selfCoupling) := by
      norm_num [overhead, selfCoupling] at *
      nlinarith
    have := (div_lt_iff₀ hd).mpr h
    linarith
  · have h : (6*overhead - 1/1000) * (Real.exp (2*selfCoupling) * selfCoupling) < 1 := by
      norm_num [overhead, selfCoupling] at *
      nlinarith
    have := (lt_div_iff₀ hd).mpr h
    linarith

theorem baseline_not_exact_match : regulator selfCoupling ≠ 6*overhead := by
  have := baseline_matching_gap.1
  linarith

/-- In the canonically normalized fluctuation `h`, the second derivative at
the vacuum is `2 lam v²`. -/
def radialPotential (lam v : ℝ) : Polynomial ℝ :=
  Polynomial.C (lam/4) * (Polynomial.X^2 + Polynomial.C (2*v)*Polynomial.X)^2

theorem higgs_curvature (lam v : ℝ) :
    (radialPotential lam v).derivative.derivative.eval 0 = 2*lam*v^2 := by
  simp [radialPotential, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_add]
  ring

end PMConstants.Matching
