import PMElementaryParticles.PhysicalUnits
import PMElementaryParticles.MassiveWidth
import PMSubstrate.Impedance
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The muon lifetime with the electron's phase space and the one-loop QED factor

`PhysicalUnits.muonLifetimeSeconds` is the tree-level `192π³/(G_F² m_μ⁵)` with the E8 `G_F` and
`m_μ/m_e`. The measured lifetime includes two further factors:

* the massive-daughter phase space, `f(r) = 1 − 8r + 8r³ − r⁴ − 12r² log r` with `r = (m_e/m_μ)²`, derived in
  this library (`MassiveWidth.closed_width`, `phase`), here at the E8 ratio `r = 1/muon²`;
* the one-loop QED factor `Q = 1 − (α/2π)(π² − 25/4)` (Kinoshita–Sirlin, Berman). This factor is
  **supplied**, not derived here; it is evaluated at the E8 `α = 1/geometricIndex`.

`muonLifetimeCorrected = muonLifetimeSeconds / (f · Q)`.

* `phase_bounds`: `0.99981294 < f < 0.99981296`.
* `qed_bounds`: `0.99579615 < Q < 0.99579616`.
* `corrected_bounds`: `2.196987 µs < τ < 2.196998 µs`.

Higher-order QED (the two-loop term, relative size `≈ 3.6·10⁻⁵`) is not included; the measured
lifetime's `1 ppm` error is below that, so this row tests the one-loop picture and the E8 `G_F` at the
`10⁻⁵` level. The `fermi` row compares `G_F` itself.
-/

noncomputable section
namespace PMElementaryParticles.MuonLifetimeCorrected

open PMElementaryParticles

/-- `r = (m_e/m_μ)²` at the E8 mass ratio. -/
def r : ℝ := 1 / LeptonMasses.muon ^ 2

/-- The massive-daughter phase-space factor. -/
def phaseFactor : ℝ := MassiveWidth.phase r

/-- E8 fine-structure constant. -/
def α : ℝ := 1 / PMSubstrate.geometricIndex

/-- The one-loop QED factor (supplied). -/
def qedFactor : ℝ := 1 - α / (2 * Real.pi) * (Real.pi ^ 2 - 25 / 4)

/-- The corrected muon lifetime in seconds. -/
def muonLifetimeCorrected : ℝ := PhysicalUnits.muonLifetimeSeconds / (phaseFactor * qedFactor)

theorem r_bounds : (2.339010677e-5 : ℝ) < r ∧ r < (2.339010682e-5 : ℝ) := by
  have hm := LeptonMasses.muon_value
  have hpos : (0 : ℝ) < LeptonMasses.muon := by linarith [hm.1]
  have h2lo : (206.7682716 : ℝ) ^ 2 < LeptonMasses.muon ^ 2 :=
    pow_lt_pow_left₀ hm.1 (by norm_num) (by norm_num)
  have h2hi : LeptonMasses.muon ^ 2 < (206.7682718 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hm.2 hpos.le (by norm_num)
  have hsq : 0 < LeptonMasses.muon ^ 2 := by positivity
  unfold r
  constructor
  · rw [lt_div_iff₀ hsq]; nlinarith
  · rw [div_lt_iff₀ hsq]; nlinarith

theorem log_r_lower : (-11 : ℝ) < Real.log r := by
  have hr := r_bounds
  have hrpos : 0 < r := by linarith [hr.1]
  have he : Real.exp (-11) < r := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h11 : Real.exp (-11) = 1 / Real.exp 1 ^ 11 := by
      rw [← Real.exp_nat_mul, Real.exp_neg]; norm_num
    rw [h11]
    have hp : (2.7182818283 : ℝ) ^ 11 < Real.exp 1 ^ 11 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    have hpos : (0 : ℝ) < Real.exp 1 ^ 11 := by positivity
    rw [div_lt_iff₀ hpos]
    nlinarith [hr.1]
  have := Real.log_lt_log (Real.exp_pos _) he
  rwa [Real.log_exp] at this

theorem log_r_upper : Real.log r < -10 := by
  have hr := r_bounds
  have hrpos : 0 < r := by linarith [hr.1]
  have he : r < Real.exp (-10) := by
    have h1 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
    have h10 : Real.exp (-10) = 1 / Real.exp 1 ^ 10 := by
      rw [← Real.exp_nat_mul, Real.exp_neg]; norm_num
    rw [h10]
    have hp : Real.exp 1 ^ 10 < (2.7182818286 : ℝ) ^ 10 :=
      pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    have hpos : (0 : ℝ) < Real.exp 1 ^ 10 := by positivity
    rw [lt_div_iff₀ hpos]
    nlinarith [hr.2]
  have := Real.log_lt_log hrpos he
  rwa [Real.log_exp] at this

theorem phase_bounds : (0.99981294 : ℝ) < phaseFactor ∧ phaseFactor < 0.99981296 := by
  have hr := r_bounds
  have hrpos : 0 < r := by linarith [hr.1]
  have hr1 : r < 1 := by linarith [hr.2]
  have hlog_neg : Real.log r < 0 := Real.log_neg hrpos hr1
  have hlog := log_r_lower
  have hr2 : 0 < r ^ 2 := by positivity
  have hlog2 := log_r_upper
  have t1 : 120 * r ^ 2 < -12 * r ^ 2 * Real.log r := by nlinarith
  have r2l : (5.47e-10 : ℝ) < r ^ 2 := by nlinarith [pow_lt_pow_left₀ hr.1 (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)]
  have t2 : -12 * r ^ 2 * Real.log r < 132 * r ^ 2 := by nlinarith
  have r3 : 0 < r ^ 3 := by positivity
  have r4 : 0 < r ^ 4 := by positivity
  have r3u : r ^ 3 < (1e-13 : ℝ) := by nlinarith [pow_lt_pow_left₀ hr.2 hrpos.le (by norm_num : (3 : ℕ) ≠ 0)]
  have r4u : r ^ 4 < (1e-17 : ℝ) := by nlinarith [pow_lt_pow_left₀ hr.2 hrpos.le (by norm_num : (4 : ℕ) ≠ 0)]
  have r2u : r ^ 2 < (5.48e-10 : ℝ) := by nlinarith [pow_lt_pow_left₀ hr.2 hrpos.le (by norm_num : (2 : ℕ) ≠ 0)]
  unfold phaseFactor MassiveWidth.phase
  constructor <;> nlinarith [hr.1, hr.2]

theorem alpha_bounds : (0.0072973525624 : ℝ) < α ∧ α < (0.0072973525625 : ℝ) := by
  have h := PMSubstrate.geometricIndex_bounds
  have hpos : (0 : ℝ) < PMSubstrate.geometricIndex := by linarith [h.1]
  unfold α
  constructor
  · rw [lt_div_iff₀ hpos]; nlinarith [h.2]
  · rw [div_lt_iff₀ hpos]; nlinarith [h.1]

theorem qed_bounds : (0.99579615 : ℝ) < qedFactor ∧ qedFactor < 0.99579616 := by
  have ha := alpha_bounds
  have hp1 : (3.14159265358979 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hp2 : Real.pi < (3.14159265358980 : ℝ) := by linarith [Real.pi_lt_d20]
  have hppos : 0 < Real.pi := Real.pi_pos
  -- c = (π² − 25/4)/(2π) = π/2 − 25/(8π)
  have hc : qedFactor = 1 - α * (Real.pi / 2 - 25 / (8 * Real.pi)) := by
    unfold qedFactor; field_simp; ring
  have hinv1 : (1 / 3.14159265358980 : ℝ) < 1 / Real.pi := one_div_lt_one_div_of_lt hppos hp2
  have hinv2 : 1 / Real.pi < (1 / 3.14159265358979 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) hp1
  have hcl : (0.57607793 : ℝ) < Real.pi / 2 - 25 / (8 * Real.pi) := by
    have : 25 / (8 * Real.pi) = (25 / 8) * (1 / Real.pi) := by field_simp
    rw [this]; nlinarith
  have hcu : Real.pi / 2 - 25 / (8 * Real.pi) < (0.57607794 : ℝ) := by
    have : 25 / (8 * Real.pi) = (25 / 8) * (1 / Real.pi) := by field_simp
    rw [this]; nlinarith
  rw [hc]
  constructor <;> nlinarith [ha.1, ha.2]

theorem corrected_bounds :
    (2.196987e-6 : ℝ) < muonLifetimeCorrected ∧ muonLifetimeCorrected < (2.196998e-6 : ℝ) := by
  have ht := PhysicalUnits.muonLifetimeSeconds_tight
  have hf := phase_bounds
  have hq := qed_bounds
  have hd1 : (0.99981294 : ℝ) * 0.99579615 < phaseFactor * qedFactor :=
    mul_lt_mul'' hf.1 hq.1 (by norm_num) (by norm_num)
  have hd2 : phaseFactor * qedFactor < (0.99981296 : ℝ) * 0.99579616 :=
    mul_lt_mul'' hf.2 hq.2 (by linarith [hf.1]) (by linarith [hq.1])
  have hdpos : 0 < phaseFactor * qedFactor := lt_trans (by norm_num) hd1
  have htpos : (0 : ℝ) < PhysicalUnits.muonLifetimeSeconds := lt_trans (by norm_num) ht.1
  unfold muonLifetimeCorrected
  constructor
  · rw [lt_div_iff₀ hdpos]
    calc (2.196987e-6 : ℝ) * (phaseFactor * qedFactor)
        < 2.196987e-6 * ((0.99981296 : ℝ) * 0.99579616) := by nlinarith
      _ < 2.187343e-6 := by norm_num
      _ < _ := ht.1
  · rw [div_lt_iff₀ hdpos]
    calc PhysicalUnits.muonLifetimeSeconds < 2.187352e-6 := ht.2
      _ < 2.196998e-6 * ((0.99981294 : ℝ) * 0.99579615) := by norm_num
      _ < _ := by nlinarith

end PMElementaryParticles.MuonLifetimeCorrected
