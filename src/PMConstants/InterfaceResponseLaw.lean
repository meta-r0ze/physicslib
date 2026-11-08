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

end PMConstants.InterfaceResponseLaw
