import PMConstants.Values
import PMSubstrate.Impedance
import Mathlib.Analysis.Real.Pi.Bounds

/-! **Experimental/candidate module.**

# Paper V's composite mass formulas against CODATA 2022 and PDG

Masses in units of `m_e` unless stated. `α⁻¹` is Paper I's derived `geometricIndex`
(`PMSubstrate.geometricIndex_bounds`), `α = 1/α⁻¹` (`PMConstants.Values.alpha_bounds`).
`Z_TOL = χ(R_M − σ)/(N³ R_M σ)` and `Z_MAR = 1/(Δ² L_embed (σ+1))` are Paper I's Toll and Margin.

| Formula | Value | Comparison |
| --- | --- | --- |
| `m_p = Δ² − πD − 1/D + 5Z_TOL − Z_MAR/χ − α(D + 1/D)` | `1836.15267344` | CODATA `1836.152673426(32)`: `proton_ratio` within `0.6σ` |
| `m_n = Δ² − πD − 1/D + σ/2 + 3Z_TOL − Z_MAR` | `1838.68366203` | CODATA `1838.68366200(74)`: `neutron_ratio` within `0.1σ` |
| `m_π⁰ = 2α⁻¹ − σχ + 1/(ν − χ)` | `134.97701` MeV | PDG `134.9768(5)`: `pion_mass` within `0.9σ` |
| `m_K⁰ = (σ+χ)α⁻¹ − σ + Dσ − 2π/(ν − χ)` | `497.6124` MeV | PDG `497.611(13)`: `kaon0_mass` within `0.2σ` |
| `m_K⁺ = (σ+χ)α⁻¹ − σ + Dπ − 1/√2 − α(σ−χ)/χ` | `493.6762` MeV | PDG `493.677(16)`: `kaonPlus_mass` within `0.1σ` |
| `r_p = D ħ/(m_p c)` | `0.841236` fm | CODATA 2022 `0.84075(64)`: `proton_radius` within `0.8σ` |

`m_e c² = 0.51099895069` MeV and `ħc = 197.3269804` MeV·fm (CODATA 2022); their uncertainties are
far below the comparisons. These certify the stated formulas' values. They do not derive the
formulas: each term's assignment (which dimensions a composite synchronizes, the charge-load
factors) is the paper's proposed ledger.
-/

noncomputable section
namespace PMElementaryParticles.CompositeMasses
open PMSubstrate

def zTol : ℝ := 2 * (172 - 5) / (32 ^ 3 * 172 * 5)
def zMar : ℝ := 1 / (43 ^ 2 * 31 * 6)
def αe : ℝ := PMConstants.Values.alpha
def αinv : ℝ := geometricIndex
def base : ℝ := 43 ^ 2 - Real.pi * 4 - 1 / 4

def me : ℝ := 0.51099895069
def hbarc : ℝ := 197.3269804

def proton : ℝ := base + 5 * zTol - zMar / 2 - αe * (4 + 1 / 4)
def neutron : ℝ := base + 5 / 2 + 3 * zTol - zMar
def pion0 : ℝ := 2 * αinv - 5 * 2 + 1 / (16 - 2)
def kaon0 : ℝ := (5 + 2) * αinv - 5 + 4 * 5 - 2 * (Real.pi / (16 - 2))
def kaonPlus : ℝ := (5 + 2) * αinv - 5 + 4 * Real.pi - 1 / Real.sqrt 2 - αe * ((5 - 2) / 2)

lemma pi_b : (3.14159265358979323846 : ℝ) < Real.pi ∧ Real.pi < 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩
lemma a_b : (0.007297352562 : ℝ) < αe ∧ αe < 0.007297352563 :=
  PMConstants.Values.alpha_bounds
lemma g_b : (137.035999212381397211 : ℝ) < αinv ∧ αinv < 137.035999212381397213 :=
  geometricIndex_bounds

theorem pion0_pos : 0 < pion0 := by
  unfold pion0
  have hg := g_b
  linarith

theorem kaon0_pos : 0 < kaon0 := by
  unfold kaon0
  have hg := g_b; have hp := pi_b
  linarith

theorem kaonPlus_pos : 0 < kaonPlus := by
  unfold kaonPlus
  have hg := g_b; have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  nlinarith [hg.1, hp.1, ha.1, hs.1]

theorem proton_value : 1836.152673444 < proton ∧ proton < 1836.152673445 := by
  have hp := pi_b; have ha := a_b
  unfold proton base zTol zMar
  constructor <;> nlinarith [hp.1, hp.2, ha.1, ha.2]

theorem neutron_value : 1838.6836620 < neutron ∧ neutron < 1838.6836621 := by
  have hp := pi_b
  unfold neutron base zTol zMar
  constructor <;> nlinarith [hp.1, hp.2]

theorem kaonPlus_value : (966 : ℝ) < kaonPlus ∧ kaonPlus < (967 : ℝ) := by
  have hg := g_b; have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  unfold kaonPlus
  constructor <;> nlinarith [hg.1, hg.2, hp.1, hp.2, hs.1, hs.2, ha.1, ha.2]

/-- Direct two-sided enclosure of the neutral pion in `m_e` units. -/
theorem pion0_value : (264.1 : ℝ) < pion0 ∧ pion0 < (264.2 : ℝ) := by
  have hg := g_b; have ha := a_b
  unfold pion0
  constructor <;> nlinarith [hg.1, hg.2, ha.1, ha.2]

def protonWith (k j : ℕ) : ℝ := base + k * zTol - zMar / j - αe * (4 + 1 / 4)
def neutronWith (k j : ℕ) : ℝ := base + 5 / 2 + k * zTol - zMar / j

lemma zTol_val : zTol = 167 / 14090240 := by norm_num [zTol]
lemma zMar_val : zMar = 1 / 343914 := by norm_num [zMar]

