import PMFlavor.CKM

/-!
# The reactor angle as a node conductance into the spatial axes

The PMNS reactor angle is written `sin²θ₁₃ = (σ − χ)/α⁻¹`. Its pieces are E8 quantities with
established readings:
* `α = 1/Z_geo` is the node admittance in units of one open channel (`PMSubstrate.causalCoupling`),
  and a node's through weight is its conductance in those units
  (`PMConstants.HandoffAdmittance.node_current`, Landauer's relation derived from the two streams);
* `σ − χ = D − 1` are the spatial axes (`PMConstants.VevLedger.noiseDenominator_eq_orthogonal`),
  the axes on which readout events occur (`PMConstants.VevEvent`).

**Construction (candidate formula).** Premises named: the outlets are the `D − 1` spatial-axis
labels, and the mixing probability is read as a conductance (Landauer). A transfer through the node
into those channels in parallel (admittances add, `PMSubstrate.ProtocolToll`) then has probability
`(D − 1)/Z_geo`. A lepton-axis state is the node passage itself (`NodeElimination`, Landauer), so its
path has no boundary to cross, unlike the quark path of `VubSeriesPath`, which enters and leaves the
node. The outlet count is the dressing's (`DressingChannels`: three spatial axes); deriving both from
one count is open (REVIEW). The comparison with data is in e8p (`E8PConstants.FlavourPulls.reactor_pull`).
-/

noncomputable section
namespace PMFlavor.ReactorConductance
open PMFlavor.CKM

lemma αinv_pos : 0 < αinv := by linarith [ai_bounds.1]

end PMFlavor.ReactorConductance
