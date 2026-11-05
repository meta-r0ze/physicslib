import PMConstants.ScaleConsistency

/-!
# What a derived interface factor must contain

`ScaleConsistency` showed the W/Z readouts need one interface factor `1.0362 < k < 1.0365`
on `α`. This module asks what kind of response can supply it.

* `scale_homogeneous_log`: if a species' response to a probe scale is additive over scale
  ratios (homogeneity in scale: each factor of scale contributes the same) and continuous,
  it is `κ · log` of the scale ratio. One coefficient per species is the whole freedom.
* `zpole_screening_overshoots`: the calculator's Z-pole coupling
  `α⁻¹(1 − Δα) − η`, with the comparison input `0.0589 < Δα < 0.0591`, gives `k > 1.07`.
  Pure screening at the Z pole is therefore not the interface coupling.
* `antiscreening_required`: writing `1/k = 1 − Δα + X`, the same inputs force
  `0.0236 < X < 0.0242`. A positive term of opposite sign to screening is required.

`Δα` is a labelled comparison input, not a derived number. Deriving the screening
coefficient and the opposite-sign term from the substrate is the remaining obligation.
-/

noncomputable section
namespace PMConstants.ScaleResponse
open PMConstants ElectroweakE8 CertifiedConstants

/-! ## Scale homogeneity forces logarithmic response -/

theorem scale_homogeneous_log (f : ℝ → ℝ)
    (hmul : ∀ x y, 0 < x → 0 < y → f (x*y) = f x + f y)
    (hcont : ContinuousOn f (Set.Ioi 0)) :
    ∀ x, 0 < x → f x = f (Real.exp 1) * Real.log x := by
  have h1 : f 1 = 0 := by
    have := hmul 1 1 one_pos one_pos; simp at this; linarith
  let g : ℝ →+ ℝ :=
    { toFun := fun t => f (Real.exp t)
      map_zero' := by simp [h1]
      map_add' := fun s t => by
        simp only [Real.exp_add]; exact hmul _ _ (Real.exp_pos s) (Real.exp_pos t) }
  have hg : Continuous g :=
    hcont.comp_continuous Real.continuous_exp (fun t => Real.exp_pos t)
  have hlin : ∀ t, g t = t * g 1 := by
    intro t
    have := (g.toRealLinearMap hg).map_smul t 1
    simpa [smul_eq_mul] using this
  intro x hx
  have := hlin (Real.log x)
  simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Real.exp_log hx] at this
  rw [this, mul_comm]

/-! ## The Z-pole coupling is not the interface coupling -/

def zpoleInverse (dα : ℝ) : ℝ := (1/α) * (1 - dα) - overhead
def zpoleFactor (dα : ℝ) : ℝ := (1/α) / zpoleInverse dα

lemma inv_alpha_bounds : (137.0359992 : ℝ) < 1/α ∧ 1/α < 137.0359993 := by
  have h := PMSubstrate.geometricIndex_bounds
  have hi : 1/α = PMSubstrate.geometricIndex := by simp [α, PMSubstrate.causalCoupling]
  rw [hi]; constructor <;> linarith [h.1, h.2]

theorem zpole_screening_overshoots {dα : ℝ} (h : 0.0589 < dα ∧ dα < 0.0591) :
    1.07 < zpoleFactor dα := by
  have ha := inv_alpha_bounds
  rw [one_div] at ha
  have hz : 0 < zpoleInverse dα := by
    unfold zpoleInverse; norm_num [overhead]; nlinarith [ha.1, h.2]
  unfold zpoleFactor
  rw [lt_div_iff₀ hz]
  unfold zpoleInverse; norm_num [overhead]
  nlinarith [ha.1, ha.2, h.1, h.2]

theorem zpole_not_interface {dα k : ℝ} (h : 0.0589 < dα ∧ dα < 0.0591) (hk : 0 < k)
    (hz : k * GaugeSpectrum.zMassSquared α ElectroweakBounds.electronGeV =
      ScaleConsistency.zAnchor^2) : k ≠ zpoleFactor dα := by
  have h1 := (ScaleConsistency.z_needs_factor hk hz).2
  have h2 := zpole_screening_overshoots h
  intro he; rw [he] at h1; linarith

/-! ## An opposite-sign term is required -/

theorem antiscreening_required {dα k X : ℝ} (h : 0.0589 < dα ∧ dα < 0.0591) (hk : 0 < k)
    (hz : k * GaugeSpectrum.zMassSquared α ElectroweakBounds.electronGeV =
      ScaleConsistency.zAnchor^2)
    (hdec : 1/k = 1 - dα + X) : 0.0236 < X ∧ X < 0.0242 := by
  have hb := ScaleConsistency.z_needs_factor hk hz
  have hk0 : 0 < k := hk
  have hX : X = 1/k - 1 + dα := by linarith
  have hlo : 1/1.0365 < 1/k := one_div_lt_one_div_of_lt hk0 hb.2
  have hhi : 1/k < 1/1.0362 := one_div_lt_one_div_of_lt (by norm_num) hb.1
  rw [hX]
  constructor
  · norm_num at hlo ⊢; linarith [h.1]
  · norm_num at hhi ⊢; linarith [h.2]

end PMConstants.ScaleResponse
