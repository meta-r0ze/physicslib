import PMConstants.VevClosure
import PMConstants.ScaleConsistency
import PMConstants.ScalarNormalization

/-! **Downstream constants conditional on the VEV closure.**

The VEV is now a composed ledger (`VevClosure.vev_closure`).  This module packages
the constants that depend on it:

* `G_F = 1/(√2 v²)`
* `m_H² = 2λv²`
* electron closure `y_e v/√2 = m_e`

The W/Z absolute scale still needs the identification of the canonical scalar VEV
with the substrate amplitude (`vev = canonicalVev`); the tree-level ratio is
independent of that scale.
-/

noncomputable section
namespace PMConstants.VevDownstream

open PMConstants ElectroweakE8 CertifiedConstants
open PMConstants.ChainCouplings

/-- The electroweak outputs conditional on the VEV ledger at the certified `α`. -/
theorem vev_downstream {me : ℝ} (hme : 0 < me) :
    0 < vev CertifiedConstants.α me ∧
      fermi CertifiedConstants.α me * Real.sqrt 2 * (vev CertifiedConstants.α me) ^ 2 = 1 ∧
      (higgsMass CertifiedConstants.α me) ^ 2 =
        2 * selfCoupling * (vev CertifiedConstants.α me) ^ 2 ∧
      ScaleConsistency.closureYukawa * vev CertifiedConstants.α me / Real.sqrt 2 = me := by
  have hα : 0 < CertifiedConstants.α := by
    linarith [CertifiedConstants.alpha_bounds.1]
  exact ⟨(constants_positive hα hme).2.1, fermi_normalization hα hme,
    higgs_mass_squared CertifiedConstants.α me, ScaleConsistency.closure_exact hme.ne'⟩
/-- W mass in terms of the canonical VEV once the VEV identification is supplied. -/
theorem w_mass_from_canonical_vev {toll : ℝ} {m : ℕ} {vsub α me : ℝ}
    (ht : 0 < toll) (hm : 0 < m)
    (hvev : vev α me = ScalarNormalization.canonicalVev toll m vsub) :
    chainCoupling (1 / 2) toll m 43 * (vev α me) ^ 2 / 4 = 3 / 344 * vsub ^ 2 := by
  rw [hvev]
  exact ScalarNormalization.w_mass_geometric ht hm vsub

end PMConstants.VevDownstream
