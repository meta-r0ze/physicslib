import PMCosmology.Scaling
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Conditional homogeneous-background consistency. Density dilution laws,
scale factor, continuity equation and the identification of load with density
are premises. Neither Friedmann dynamics nor those premises are derived here. -/
noncomputable section
namespace PMCosmology.Background

/-- Supplied pressureless-matter and radiation dilution, in terms of redshift. -/
def matter (ρm z : ℝ) : ℝ := ρm*(1+z)^3
def radiation (ρr z : ℝ) : ℝ := ρr*(1+z)^4

/-- Equality is at 1+z=ρm₀/ρr₀, not z=ρm₀/ρr₀. -/
theorem equality_redshift (ρm ρr z : ℝ) (hr : 0 < ρr) (hz : -1 < z) :
    matter ρm z = radiation ρr z ↔ z = ρm/ρr-1 := by
  have hn : (1+z)^3 ≠ 0 := pow_ne_zero _ (by linarith)
  have he : matter ρm z = radiation ρr z ↔ ρm = ρr*(1+z) := by
    unfold matter radiation
    rw [pow_succ]
    constructor
    · intro h
      apply mul_right_cancel₀ hn
      nlinarith only [h]
    · intro h
      rw [h]
      ring
  rw [he]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- The proposed geometric equality redshift requires a density-amplitude
ratio; the geometric product alone does not derive that ratio. -/
theorem geometric_equality_requires_ratio (ρm ρr : ℝ) (hr : 0 < ρr) :
    matter ρm (1075*Real.pi) = radiation ρr (1075*Real.pi) ↔
      ρm/ρr = 1+1075*Real.pi := by
  rw [equality_redshift ρm ρr _ hr (by have := Real.pi_pos; linarith)]
  constructor <;> intro h <;> linarith

/-- If the vacuum density is postulated to track load, its derivative tracks it. -/
theorem density_derivative (ρ0 a Ldot : ℝ) (L : ℝ → ℝ)
    (hL : HasDerivAt L Ldot a) :
    HasDerivAt (fun x => ρ0*L x) (ρ0*Ldot) a := hL.const_mul ρ0

/-- From a ρ'(a)=-3(1+w)ρ(a), load-proportional density has this equation of state.
A variable load alone does not supply this conservation equation. -/
theorem equation_of_state (a ρ0 L Ldot w : ℝ) (hρ : ρ0 ≠ 0) (hL : L ≠ 0) :
    a*(ρ0*Ldot) = -3*(1+w)*(ρ0*L) ↔ w = -1-a*Ldot/(3*L) := by
  constructor
  · intro h
    have hz : ρ0*(a*Ldot+3*(1+w)*L) = 0 := by nlinarith only [h]
    have he := (mul_eq_zero.mp hz).resolve_left hρ
    field_simp [hL]
    nlinarith only [he]
  · intro h
    rw [h]
    field_simp [hL]
    ring

/-- Under that same contract, w=-1 iff load is instantaneously constant. -/
theorem vacuum_equation_iff (a L Ldot : ℝ) (ha : 0 < a) (hL : L ≠ 0) :
    -1-a*Ldot/(3*L) = -1 ↔ Ldot = 0 := by
  have hd : 3*L ≠ 0 := mul_ne_zero (by norm_num) hL
  constructor
  · intro h
    have hz : a*Ldot/(3*L)=0 := by linarith
    have hm := (div_eq_zero_iff).mp hz
    rcases hm with hm | hm
    · exact (mul_eq_zero.mp hm).resolve_left ha.ne'
    · exact False.elim (hd hm)
  · intro h; simp [h]


/-- The proposed geometric equality redshift `z_eq = 1075π`, with a rational enclosure. -/
theorem z_eq_bounds : (3377.2121 : ℝ) < 1075*Real.pi ∧ 1075*Real.pi < 3377.2122 := by
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  constructor <;> nlinarith

end PMCosmology.Background
