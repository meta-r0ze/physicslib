import PMElementaryParticles.CompositeMasses
import PMConstants.StrongRunning

/-!

# Paper V's quark mass formulas

Units of `m_e`, `η = 171/172`. The formulas are E8; this module keeps them and
their **E8-only** enclosures. The measured PDG 2024 pull comparisons live in
`tools/e8p/E8PConstants/QuarkMassPulls.lean`.

| Formula | MeV |
| --- | --- |
| `m_u = D/η` | `2.0560` |
| `m_d = (D+σ)/η` | `4.6260` |
| `m_s = (DΔ + 2σ)/η` | `93.546` |
| `m_c = DΔ²/(η(σ−χ))` | `1267.15` |
| `m_b = Δ²(D + χ/σ)/η` | `4181.6` |
| `m_t = Δ³(D + 1/D)` | `172668` |

These are the formulas Paper III's `StrongRunning` uses for the flavour
thresholds (`m_c`, `m_b`).
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

/-- E8-only enclosure of the up-quark mass, matching the `e8p` catalog interval. -/
theorem up_value : (2.055 : ℝ) < up * me ∧ up * me < (2.062 : ℝ) := by
  unfold up η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me]

/-- E8-only enclosure of the down-quark mass. -/
theorem down_value : (4.623 : ℝ) < down * me ∧ down * me < (4.63 : ℝ) := by
  unfold down η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me]

/-- E8-only enclosure of the strange-quark mass. -/
theorem strange_value : (93.5 : ℝ) < strange * me ∧ strange * me < (93.58 : ℝ) := by
  unfold strange η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me]

/-- E8-only enclosure of the charm-quark mass. -/
theorem charm_value : (1267.02 : ℝ) < charm * me ∧ charm * me < (1267.48 : ℝ) := by
  unfold charm η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me]

/-- E8-only enclosure of the bottom-quark mass. -/
theorem bottom_value : (4180.9 : ℝ) < bottom * me ∧ bottom * me < (4182.3 : ℝ) := by
  unfold bottom η
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.chi_eq, PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.overhead_eq]
  norm_num [me]

/-- E8-only enclosure of the top-quark mass. -/
theorem top_value : (172657 : ℝ) < top * me ∧ top * me < (172686 : ℝ) := by
  unfold top
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq]
  norm_num [me]

/-- The thresholds Paper III orders are these formulas. -/
theorem threshold_match : charm = PMConstants.StrongRunning.mCharm ∧ bottom = PMConstants.StrongRunning.mBottom := by
  unfold charm bottom η PMConstants.StrongRunning.mCharm PMConstants.StrongRunning.mBottom PMConstants.overhead
  rw [PMSubstrate.E8Values.D_eq, PMSubstrate.E8Values.Delta_eq,
    PMSubstrate.E8Values.sigma_eq, PMSubstrate.E8Values.chi_eq,
    PMSubstrate.E8Values.overhead_eq]
  constructor <;> ring

end PMElementaryParticles.QuarkMasses
