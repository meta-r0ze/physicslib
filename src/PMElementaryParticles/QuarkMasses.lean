import PMElementaryParticles.CompositeMasses
import PMConstants.StrongRunning

/-!
# Paper V's quark mass formulas against PDG 2024

Units of `m_e`, `η = 171/172`. Uncertainties as used by the shared calculator (PDG 2024):
`m_u = 2.16(7)`, `m_d = 4.70(7)`, `m_s = 93.5(8)` MeV; `m_c = 1273.0(46)`, `m_b = 4183(7)`,
`m_t = 172570(290)` MeV.

| Formula | MeV | Pull |
| --- | --- | --- |
| `m_u = D/η` | `2.0560` | `(−1.5, −1.4)` |
| `m_d = (D+σ)/η` | `4.6260` | `(−1.1, −1.0)` |
| `m_s = (DΔ + 2σ)/η` | `93.546` | `(0, 0.1)` |
| `m_c = DΔ²/(η(σ−χ))` | `1267.15` | `(−1.3, −1.2)` |
| `m_b = Δ²(D + χ/σ)/η` | `4181.6` | `(−0.3, −0.1)` |
| `m_t = Δ³(D + 1/D)` | `172668` | `(0.3, 0.4)` |

These are the formulas Paper III's `StrongRunning` uses for the flavour thresholds (`m_c`, `m_b`).
-/

noncomputable section
namespace PMElementaryParticles.QuarkMasses
open PMElementaryParticles.CompositeMasses

def η : ℝ := PMSubstrate.E8Values.overhead
def up : ℝ := (PMSubstrate.E8Values.D : ℝ) / η
def down : ℝ := ((PMSubstrate.E8Values.D : ℝ) + (PMSubstrate.E8Values.sigma : ℝ)) / η
def strange : ℝ := ((PMSubstrate.E8Values.D : ℝ) * (PMSubstrate.E8Values.Delta : ℝ) +
  (PMSubstrate.E8Values.chi : ℝ) * (PMSubstrate.E8Values.sigma : ℝ)) / η
def charm : ℝ := (PMSubstrate.E8Values.D : ℝ) * (PMSubstrate.E8Values.Delta : ℝ)^2 /
  (η * ((PMSubstrate.E8Values.sigma : ℝ) - (PMSubstrate.E8Values.chi : ℝ)))
def bottom : ℝ := (PMSubstrate.E8Values.Delta : ℝ)^2 *
  ((PMSubstrate.E8Values.D : ℝ) +
    (PMSubstrate.E8Values.chi : ℝ) / (PMSubstrate.E8Values.sigma : ℝ)) / η
def top : ℝ := (PMSubstrate.E8Values.Delta : ℝ)^3 *
  ((PMSubstrate.E8Values.D : ℝ) + 1 / (PMSubstrate.E8Values.D : ℝ))

theorem pulls :
    (-1.5 < (up * me - 2.16) / 0.07 ∧ (up * me - 2.16) / 0.07 < -1.4) ∧
    (-1.1 < (down * me - 4.70) / 0.07 ∧ (down * me - 4.70) / 0.07 < -1.0) ∧
    (0 < (strange * me - 93.5) / 0.8 ∧ (strange * me - 93.5) / 0.8 < 0.1) ∧
    (-1.3 < (charm * me - 1273.0) / 4.6 ∧ (charm * me - 1273.0) / 4.6 < -1.2) ∧
    (-0.3 < (bottom * me - 4183) / 7 ∧ (bottom * me - 4183) / 7 < -0.1) ∧
    (0.3 < (top * me - 172570) / 290 ∧ (top * me - 172570) / 290 < 0.4) := by
  unfold up down strange charm bottom top η me
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.overhead_eq]
  norm_num

/-- The thresholds Paper III orders are these formulas. -/
theorem threshold_match : charm = PMConstants.StrongRunning.mCharm ∧ bottom = PMConstants.StrongRunning.mBottom := by
  unfold charm bottom η PMConstants.StrongRunning.mCharm PMConstants.StrongRunning.mBottom PMConstants.overhead
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.overhead_eq]
  constructor <;> ring

end PMElementaryParticles.QuarkMasses
