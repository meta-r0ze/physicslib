import PMElementaryParticles.SharedUnits
import PMConstants.Values
import PMSubstrate.Impedance
import Mathlib.Analysis.Real.Pi.Bounds

/-!

# Composite masses: the occupancy cost of a persistent carrier cohort

The mass of an E8 composite is what its persistent configuration costs on the
substrate. Masses are in `m_e` unless stated. Every numeral is the canonical
`PMSubstrate.E8Values` invariant (`D = 4`, `Δ = 43`, `ν = 16`, `σ = 5`, `χ = 2`,
`R_M = 172`, `N = 32`, `L_embed = 31`), so no bare literal remains. `α⁻¹` is the
derived six-pillar cell budget (`geometricIndex`), `α = 1/α⁻¹`.

Paper I's Toll and Margin are the invariants

* `Z_TOL = χ(R_M − σ)/(N³ R_M σ)` (`zTol`),
* `Z_MAR = 1/(Δ² L_embed (σ+1))` (`zMar`),

and the nucleons share the pillar base `Δ² − πD − 1/D`:

| Formula | Value | Comparison |
| --- | --- | --- |
| `m_p = base + σ Z_TOL − Z_MAR/χ − α(D + 1/D)` | `1836.15267344` | CODATA `1836.152673426(32)`: `proton_ratio` within `0.6σ` |
| `m_n = base + σ/2 + (σ−χ) Z_TOL − Z_MAR` | `1838.68366203` | CODATA `1838.68366200(74)`: `neutron_ratio` within `0.1σ` |
| `m_π⁰ = 2α⁻¹ − χσ + 1/(ν − χ)` | `134.97701` MeV | PDG `134.9768(5)`: `pion_mass` within `0.9σ` |
| `m_K⁰ = (σ+χ)α⁻¹ − σ + Dσ − χπ/(ν − χ)` | `497.6124` MeV | PDG `497.611(13)`: `kaon0_mass` within `0.2σ` |
| `m_K⁺ = (σ+χ)α⁻¹ − σ + Dπ − 1/√2 − α(σ−χ)/χ` | `493.6762` MeV | PDG `493.677(16)`: `kaonPlus_mass` within `0.1σ` |
| `r_p = D ħ/(m_p c)` | `0.841236` fm | CODATA 2022 `0.84075(64)`: `proton_radius` within `0.8σ` |

Standard-Model names above are **comparison labels** for the E8 composites; the
right-hand column is the comparison (CODATA/PDG), the formula is the derived E8
occupancy cost. `m_e c² = 0.51099895069` MeV and `ħc = 197.3269804` MeV·fm
(CODATA 2022); their uncertainties are far below the comparisons. These certify
the stated formulas' values. They do not derive the formulas: each term's
assignment (which dimensions a composite synchronizes, the charge-load factors)
is the paper's proposed ledger (`M`). The cell-budget form of the mesons and the `e8p` pulls are in
`MesonMasses` and `tools/e8p/E8PConstants/PMHadrons/CompositeMassPulls.lean`.
-/

noncomputable section
namespace PMHadrons.CompositeMasses
open PMElementaryParticles
open PMSubstrate
open PMSubstrate.E8Values
export PMElementaryParticles.SharedUnits (αe αinv me hbarc pi_b a_b g_b)

/-- Paper I's Toll `Z_TOL = χ(R_M − σ)/(N³ R_M σ)`. -/
def zTol : ℝ := (chi : ℝ) * ((RM : ℝ) - (sigma : ℝ)) /
  ((N : ℝ) ^ 3 * (RM : ℝ) * (sigma : ℝ))

/-- Paper I's Margin `Z_MAR = 1/(Δ² L_embed (σ+1))`. -/
def zMar : ℝ := 1 / ((Delta : ℝ) ^ 2 * (embeddingLoad : ℝ) * ((sigma : ℝ) + 1))

/-- The pillar base `Δ² − πD − 1/D` shared by the nucleons. -/
def base : ℝ := (Delta : ℝ) ^ 2 - Real.pi * (D : ℝ) - 1 / (D : ℝ)

/-- Proton: base minus the pillar costs `σ Z_TOL`, `Z_MAR/χ`, `α(D + 1/D)`. -/
def proton : ℝ := base + (sigma : ℝ) * zTol - zMar / (chi : ℝ) -
  αe * ((D : ℝ) + 1 / (D : ℝ))

/-- Neutron: proton's base with the `σ/2` symmetry share and `(σ−χ) Z_TOL`. -/
def neutron : ℝ := base + (sigma : ℝ) / 2 + ((sigma : ℝ) - (chi : ℝ)) * zTol - zMar

def pion0 : ℝ := 2 * αinv - (chi : ℝ) * (sigma : ℝ) + 1 / ((nu : ℝ) - (chi : ℝ))

def kaon0 : ℝ := ((sigma : ℝ) + (chi : ℝ)) * αinv - (sigma : ℝ) + (D : ℝ) * (sigma : ℝ) -
  (chi : ℝ) * Real.pi / ((nu : ℝ) - (chi : ℝ))

def kaonPlus : ℝ := ((sigma : ℝ) + (chi : ℝ)) * αinv - (sigma : ℝ) + (D : ℝ) * Real.pi -
  1 / Real.sqrt 2 - αe * (((sigma : ℝ) - (chi : ℝ)) / (chi : ℝ))

theorem pion0_pos : 0 < pion0 := by
  unfold pion0
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq]
  have hg := g_b
  linarith

theorem kaon0_pos : 0 < kaon0 := by
  unfold kaon0
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq, PMSubstrate.E8Values.D_eq]
  have hg := g_b; have hp := pi_b
  linarith

theorem kaonPlus_pos : 0 < kaonPlus := by
  unfold kaonPlus
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.D_eq]
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
  rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.D_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.RM_eq, PMSubstrate.E8Values.N_eq,
    PMSubstrate.E8Values.embeddingLoad_eq]
  constructor <;> nlinarith [hp.1, hp.2, ha.1, ha.2]

theorem neutron_value : 1838.6836620 < neutron ∧ neutron < 1838.6836621 := by
  have hp := pi_b
  unfold neutron base zTol zMar
  rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.D_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.RM_eq, PMSubstrate.E8Values.N_eq,
    PMSubstrate.E8Values.embeddingLoad_eq]
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
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.D_eq]
  constructor <;> nlinarith [hg.1, hg.2, hp.1, hp.2, hs.1, hs.2, ha.1, ha.2]

/-- Direct two-sided enclosure of the neutral pion in `m_e` units. -/
theorem pion0_value : (264.1 : ℝ) < pion0 ∧ pion0 < (264.2 : ℝ) := by
  have hg := g_b; have ha := a_b
  unfold pion0
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq]
  constructor <;> nlinarith [hg.1, hg.2, ha.1, ha.2]

def protonWith (k j : ℕ) : ℝ := base + k * zTol - zMar / j -
  αe * ((D : ℝ) + 1 / (D : ℝ))
def neutronWith (k j : ℕ) : ℝ := base + (sigma : ℝ) / 2 + k * zTol - zMar / j

lemma zTol_val : zTol = 167 / 14090240 := by
  unfold zTol
  rw [PMSubstrate.E8Values.RM_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.N_eq]
  norm_num
lemma zMar_val : zMar = 1 / 343914 := by
  unfold zMar
  rw [PMSubstrate.E8Values.Delta_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.embeddingLoad_eq]
  norm_num

/-! ## Masses in MeV and the proton radius (`m_e`, `ħc` as unit inputs)

Direct enclosures of the E8 values, so the comparison layer does not have to read them off a
pull against the measurement. -/

/-- E8 neutral pion in MeV: `134.97701…`. -/
theorem pion0_mev_value : (134.977014 : ℝ) < pion0 * me ∧ pion0 * me < 134.977015 := by
  have hg := g_b
  unfold pion0 me
  rw [PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq,
    PMSubstrate.E8Values.nu_eq]
  constructor <;> nlinarith [hg.1, hg.2]

/-- E8 neutral kaon in MeV: `497.61241…`. -/
theorem kaon0_mev_value : (497.612411 : ℝ) < kaon0 * me ∧ kaon0 * me < 497.612412 := by
  have hg := g_b; have hp := pi_b
  unfold kaon0 me
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.D_eq,
    PMSubstrate.E8Values.nu_eq]
  constructor <;> nlinarith [hg.1, hg.2, hp.1, hp.2]

/-- E8 charged kaon in MeV: `493.67624…`. -/
theorem kaonPlus_mev_value :
    (493.676245 : ℝ) < kaonPlus * me ∧ kaonPlus * me < 493.676246 := by
  have hg := g_b; have hp := pi_b; have ha := a_b
  have hs : (0.7071067811 : ℝ) < 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 0.7071067812 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    constructor
    · rw [lt_div_iff₀ hpos]; nlinarith
    · rw [div_lt_iff₀ hpos]; nlinarith
  unfold kaonPlus me
  rw [PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.D_eq]
  constructor <;> nlinarith [hg.1, hg.2, hp.1, hp.2, hs.1, hs.2, ha.1, ha.2]

/-- E8 proton charge radius `4ħ/(m_p c)` in fm: `0.84123564…`. -/
theorem protonRadius_value :
    (0.8412356 : ℝ) < 4 * hbarc / (proton * me) ∧ 4 * hbarc / (proton * me) < 0.8412357 := by
  have h := proton_value
  have hpos : 0 < proton * me := by unfold me; nlinarith
  constructor
  · rw [lt_div_iff₀ hpos]; unfold hbarc me; nlinarith
  · rw [div_lt_iff₀ hpos]; unfold hbarc me; nlinarith
