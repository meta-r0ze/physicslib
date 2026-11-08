import PMConstants.InterfaceGeometry
import PMConstants.VevReadout
import PMSubstrate.PersistenceMaximin

/-! **Interface response as one exact repair per active mode.**

The response law is assembled from three already-owned facts:

* exact repair is linear, not iterated (`VevReadout.exact_net_is_identity`);
* the five active modes carry the uniform maximin weight
  (`InterfaceGeometry.uniform_five_weights`);
* the active mode count is the substrate configuration dimension
  (`PMSubstrate.Derived.configDim`).

The remaining input is the per-mode repair `α`; the factor is then

```
K = 1 + σ α.
```
-/

noncomputable section
namespace PMConstants.InterfaceResponseLaw

open PMConstants

/-- Interface factor for a supplied per-mode repair. -/
def interfaceFactor (perMode : ℝ) : ℝ :=
  1 + perMode * InterfaceGeometry.activeResponseModes

/-- The factor is linear in the five active modes. -/
theorem interfaceFactor_eq (perMode : ℝ) :
    interfaceFactor perMode = 1 + 5 * perMode := by
  unfold interfaceFactor
  rw [InterfaceGeometry.activeResponseModes_eq]
  ring

/-- With the substrate admittance as the per-mode repair, `K = 1 + 5α`. -/
theorem interfaceFactor_alpha :
    interfaceFactor CertifiedConstants.α = 1 + 5 * CertifiedConstants.α :=
  interfaceFactor_eq _

/-- The geometric factor is the same as `1 + α·σ`. -/
theorem interfaceFactor_sigma :
    interfaceFactor CertifiedConstants.α =
      1 + CertifiedConstants.α * PMSubstrate.E8Values.sigma := by
  rw [interfaceFactor_alpha, PMSubstrate.E8Values.sigma_eq]
  ring

/-- Exact repair supplies the linear, non-iterated form. -/
theorem exact_repair_linear {Dsp T : Type*} [AddGroup Dsp] (prepare : Dsp → T) (run : T → T)
    (observe : T → Dsp) (hexact : ∀ d, observe (run (prepare d)) = 0) :
    (fun d => d - observe (run (prepare d))) = id :=
  VevReadout.exact_net_is_identity prepare run observe hexact

/-- **The substrate interface correction is derived and lands in the Z window.** With the
response law `k_sub = 1 + σα` (`interfaceFactor_sigma`: exact linear repair, the five geometric
modes `InterfaceGeometry.activeResponseModes_eq_sigma`, maximin uniform weight, per-mode repair
`α`), the on-shell correction is `Δr_sub = 1 − 1/k_sub = 5α/(1+5α)`, the window value
`InterfaceWeightWindow.deltaRWeight 5` (`weight_five_in_window`). The naive isotropic root sum is
excluded (`InterfaceSpectralCandidate.simple_root_sum_excluded`), so this is the substrate value,
compared to the window only afterwards. -/
theorem substrate_deltaR_in_window :
    0.0349 < InterfaceCorrection.deltaR (interfaceFactor CertifiedConstants.α) ∧
      InterfaceCorrection.deltaR (interfaceFactor CertifiedConstants.α) < 0.0353 := by
  have hval : InterfaceCorrection.deltaR (interfaceFactor CertifiedConstants.α) =
      InterfaceWeightWindow.deltaRWeight 5 := by
    rw [interfaceFactor_sigma, PMSubstrate.E8Values.sigma_eq]
    unfold InterfaceCorrection.deltaR InterfaceWeightWindow.deltaRWeight
    have hd : (1 : ℝ) + CertifiedConstants.α * ((5 : ℕ) : ℝ) ≠ 0 := by
      have hα : (0 : ℝ) < CertifiedConstants.α :=
        lt_trans (by norm_num) CertifiedConstants.alpha_bounds.1
      positivity
    field_simp
    ring
  rw [hval]
  exact InterfaceWeightWindow.weight_five_in_window

end PMConstants.InterfaceResponseLaw
