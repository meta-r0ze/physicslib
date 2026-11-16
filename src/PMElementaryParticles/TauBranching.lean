import PMElementaryParticles.LeptonMasses
import PMElementaryParticles.MassiveWidth
import PMSubstrate.E8Values
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The tau's electronic branching fraction: what EP derives and what is left

`TauLifetime` and `TauE8` use `B(τ → eνν̄) = 0.1782` as a supplied input. Its parts:

* **Leptonic channels.** One `G_F` for every lepton (`WeakMatching.fermi_from_reference`), so
  `Γ(τ → μνν̄)/Γ(τ → eνν̄) = f(r)` with `r = (m_μ/m_τ)²` and the derived massive phase factor
  `f = MassiveWidth.phase` (the electron's own factor `f(m_e²/m_τ²)` differs from `1` by `3·10⁻⁷`).
  At the E8 masses `0.9724 < f(r) < 0.9727` (`phase_bounds`).
* **Hadronic channel at parton level.** `τ → ν + (d̄u)` is the same contact process once per
  colour: `N_c = D − 1 = 3` colour axes (`colours_eq`; axis `0` is the lepton axis).
  Its width is `N_c · h · Γ_e`, where `h` collects what the parton count leaves out (the first
  CKM row, the strong-interaction dressing of the quark pair, short-distance electroweak factor).

So `B_e = 1/(1 + f(r) + N_c h)` (`branching`).

* `parton_level`: with `h = 1`, `0.2010 < B_e < 0.2012`.
* `supplied_needs`: the supplied `0.1782` is `B_e` at `1.2129 < h < 1.2132`.

So the leptonic part and the colour count are E8's; the remaining input is the hadronic factor
`h ≈ 1.213`, the strong dressing of a quark pair at the tau mass. That belongs to PMHadrons
(PMHadrons REVIEW).
-/

noncomputable section
namespace PMElementaryParticles.TauBranching
open PMElementaryParticles.LeptonMasses

/-- Colour axes: `D − 1`. -/
def colours : ℝ := (PMSubstrate.E8Values.D : ℝ) - 1

theorem colours_eq : colours = 3 := by
  unfold colours; rw [PMSubstrate.E8Values.D_eq]; norm_num

/-- `r = (m_μ/m_τ)²` at the E8 masses. -/
def r : ℝ := (muon / tau) ^ 2

/-- The electronic branching fraction with hadronic factor `h`. -/
def branching (h : ℝ) : ℝ := 1 / (1 + MassiveWidth.phase r + colours * h)

theorem r_bounds : (0.0035363 : ℝ) < r ∧ r < 0.0035364 := by
  have hm := muon_value
  unfold r; rw [tau_value]
  constructor <;> nlinarith [hm.1, hm.2]

theorem log_r_bounds : (-6 : ℝ) < Real.log r ∧ Real.log r < -5 := by
  have hr := r_bounds
  have hrpos : 0 < r := by linarith [hr.1]
  have e1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have e2 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  constructor
  · have he : Real.exp (-6) < r := by
      have h6 : Real.exp (-6) = 1 / Real.exp 1 ^ 6 := by
        rw [← Real.exp_nat_mul, Real.exp_neg]; norm_num
      rw [h6, div_lt_iff₀ (by positivity)]
      have hp : (2.7182818283 : ℝ) ^ 6 < Real.exp 1 ^ 6 := pow_lt_pow_left₀ e1 (by norm_num) (by norm_num)
      nlinarith [hr.1]
    have := Real.log_lt_log (Real.exp_pos _) he
    rwa [Real.log_exp] at this
  · have he : r < Real.exp (-5) := by
      have h5 : Real.exp (-5) = 1 / Real.exp 1 ^ 5 := by
        rw [← Real.exp_nat_mul, Real.exp_neg]; norm_num
      rw [h5, lt_div_iff₀ (by positivity)]
      have hp : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 := pow_lt_pow_left₀ e2 (by positivity) (by norm_num)
      nlinarith [hr.2]
    have := Real.log_lt_log hrpos he
    rwa [Real.log_exp] at this

theorem phase_bounds : (0.9724 : ℝ) < MassiveWidth.phase r ∧ MassiveWidth.phase r < 0.9727 := by
  have hr := r_bounds
  have hl := log_r_bounds
  have hrpos : 0 < r := by linarith [hr.1]
  have hr2 : 0 < r ^ 2 := by positivity
  have t1 : 60 * r ^ 2 < -12 * r ^ 2 * Real.log r := by nlinarith
  have t2 : -12 * r ^ 2 * Real.log r < 72 * r ^ 2 := by nlinarith
  have r2u : r ^ 2 < (1.3e-5 : ℝ) := by nlinarith
  have r3 : 0 < r ^ 3 := by positivity
  have r3u : r ^ 3 < (1e-7 : ℝ) := by nlinarith
  have r4 : 0 < r ^ 4 := by positivity
  have r4u : r ^ 4 < (1e-9 : ℝ) := by nlinarith
  unfold MassiveWidth.phase
  constructor <;> nlinarith

theorem parton_level : (0.2010 : ℝ) < branching 1 ∧ branching 1 < 0.2012 := by
  have hf := phase_bounds
  unfold branching; rw [colours_eq]
  constructor
  · rw [lt_div_iff₀ (by linarith [hf.1])]; nlinarith
  · rw [div_lt_iff₀ (by linarith [hf.1])]; nlinarith

theorem supplied_needs (h : ℝ) (hb : branching h = 0.1782) : 1.2129 < h ∧ h < 1.2132 := by
  have hf := phase_bounds
  unfold branching at hb; rw [colours_eq] at hb
  have hd : 1 + MassiveWidth.phase r + 3 * h ≠ 0 := by
    intro h0; rw [h0, div_zero] at hb; norm_num at hb
  have : 1 + MassiveWidth.phase r + 3 * h = 1 / 0.1782 := by
    rw [← hb]; field_simp
  constructor <;> nlinarith

end PMElementaryParticles.TauBranching
