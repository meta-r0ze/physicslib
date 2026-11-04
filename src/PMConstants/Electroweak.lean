import PMConstants.Partition
import Mathlib.Analysis.Real.Sqrt

/-!
# The proposed electroweak constants and their dependency graph

These are the manuscript's proposed allocation laws, evaluated consistently.
The dimensionful input `me` supplies the unit of mass. No absolute mass in GeV
is inferred from dimensionless lattice data. Electromagnetic matching and the
allocation laws remain physical obligations, separate from their consequences.
-/

noncomputable section
namespace PMConstants.Electroweak

def bareYukawa : ℝ := 1 / (31 * 6 * 43^2)
def electronYukawa (α : ℝ) : ℝ := bareYukawa * (1 + 5/4 * α)
def effectiveDimension : ℝ := 4 + 2 / (4 * Real.pi)
def vevRatio (α : ℝ) : ℝ :=
  (2 * 43^2 - (16 + 4 * 43)) / α *
    (1 + α / effectiveDimension) * (1 - bareYukawa / 3)
def vev (α me : ℝ) : ℝ := vevRatio α * me
def higgsMass (α me : ℝ) : ℝ := Real.sqrt (2 * selfCoupling) * vev α me
def fermi (α me : ℝ) : ℝ := 1 / (Real.sqrt 2 * (vev α me)^2)
def weakSquared (α : ℝ) : ℝ := 4 * Real.pi * α / clockRatio
def hyperchargeSquared (α : ℝ) : ℝ := 4 * Real.pi * α / (1 - clockRatio)
def strongSquared (α : ℝ) : ℝ := 4 * Real.pi * strongCoupling α

theorem exact_counts :
    2 * 43^2 - (16 + 4 * 43) = (3510 : ℕ) ∧
      bareYukawa = 1/343914 ∧ 0 < bareYukawa ∧ bareYukawa < 1 := by
  norm_num [bareYukawa]

theorem effective_dimension_pos : 0 < effectiveDimension := by
  unfold effectiveDimension
  positivity

theorem ratio_pos {α : ℝ} (hα : 0 < α) : 0 < vevRatio α := by
  have hb : 0 < 1 - bareYukawa / 3 := by linarith [exact_counts.2.2.2]
  have hd := effective_dimension_pos
  unfold vevRatio
  have hnum : (0 : ℝ) < 2 * 43^2 - (16 + 4 * 43) := by norm_num
  exact mul_pos (mul_pos (div_pos hnum hα) (by positivity)) hb

theorem constants_positive {α me : ℝ} (hα : 0 < α) (hme : 0 < me) :
    0 < electronYukawa α ∧ 0 < vev α me ∧ 0 < higgsMass α me ∧
      0 < fermi α me ∧ 0 < weakSquared α ∧ 0 < hyperchargeSquared α ∧
      0 < strongSquared α := by
  have hv : 0 < vev α me := mul_pos (ratio_pos hα) hme
  have hw := clock_ratio_bounds
  have hs : 0 < strongCoupling α := by
    unfold strongCoupling
    exact mul_pos (by linarith [overhead_bounds.1]) hα
  refine ⟨?_, hv, ?_, ?_, ?_, ?_, ?_⟩
  · unfold electronYukawa; exact mul_pos exact_counts.2.2.1 (by positivity)
  · exact mul_pos (Real.sqrt_pos.mpr (by linarith [self_coupling_pos])) hv
  · unfold fermi; positivity
  · exact div_pos (by positivity) hw.1
  · exact div_pos (by positivity) (by linarith [hw.2])
  · unfold strongSquared; positivity

/-- The dressed couplings reproduce the stipulated mixing ratio exactly. -/
theorem mixing_identity {α : ℝ} (hα : 0 < α) :
    hyperchargeSquared α / (weakSquared α + hyperchargeSquared α) = clockRatio := by
  have hc := clock_ratio_bounds
  have hp := Real.pi_pos
  unfold hyperchargeSquared weakSquared
  have hden : 4 * Real.pi * α / clockRatio + 4 * Real.pi * α / (1-clockRatio) ≠ 0 := by
    have h1 : 0 < 4 * Real.pi * α / clockRatio := div_pos (by positivity) hc.1
    have h2 : 0 < 4 * Real.pi * α / (1-clockRatio) :=
      div_pos (by positivity) (by linarith [hc.2])
    linarith
  apply (div_eq_iff hden).mpr
  field_simp [hc.1.ne', (sub_pos.mpr hc.2).ne']
  ring

theorem fermi_normalization {α me : ℝ} (hα : 0 < α) (hme : 0 < me) :
    fermi α me * Real.sqrt 2 * (vev α me)^2 = 1 := by
  have hv := (constants_positive hα hme).2.1
  unfold fermi
  field_simp

theorem higgs_mass_squared (α me : ℝ) :
    (higgsMass α me)^2 = 2 * selfCoupling * (vev α me)^2 := by
  unfold higgsMass
  rw [mul_pow, Real.sq_sqrt (by linarith [self_coupling_pos])]

/-- Changing the mass unit rescales every dimensionful output together. -/
theorem mass_scale_covariance (α me c : ℝ) :
    vev α (c*me) = c * vev α me ∧
      higgsMass α (c*me) = c * higgsMass α me := by
  simp only [vev, higgsMass]
  constructor <;> ring

/-- Neither side of the manuscript's Higgs/aperture match contains the VEV. -/
def interfaceMatch (_v : ℝ) : Prop :=
  Real.exp (-2 * selfCoupling) / selfCoupling = 6 * overhead

theorem interface_match_cannot_select_scale (v w : ℝ) :
    interfaceMatch v ↔ interfaceMatch w := Iff.rfl

/-- Closing the electron mass law imposes a further dimensionless equation.
It does not determine the overall mass unit. -/
theorem electron_mass_closure {α me : ℝ} (hme : me ≠ 0) :
    electronYukawa α * vev α me / Real.sqrt 2 = me ↔
      electronYukawa α * vevRatio α = Real.sqrt 2 := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_eq_iff hs]
  unfold vev
  constructor
  · intro h; exact (mul_right_cancel₀ hme (by nlinarith :
      (electronYukawa α * vevRatio α) * me = Real.sqrt 2 * me))
  · intro h; rw [← mul_assoc, h, mul_comm]

end PMConstants.Electroweak
