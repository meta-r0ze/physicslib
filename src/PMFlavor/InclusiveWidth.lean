import PMElementaryParticles.InclusiveMixing
import PMFlavor.PMNS

/-!
# The on-axis label-change matrix in an inclusive width

`PMElementaryParticles.InclusiveMixing.equal_kinematics`: for unresolved, orthogonal channels with equal
kinematics, any unitary mixing cancels from the inclusive width. Applied to the on-axis matrix e8p
prints (`PMNS.matrix`, read out as the PMNS), the inclusive muon width is the unmixed one; only
unitarity is used, not the angle formulas. (Moved from PMElementaryParticles, which no longer
imports PMFlavor.)
-/

noncomputable section
namespace PMFlavor.InclusiveWidth
open PMElementaryParticles PMElementaryParticles.InclusiveMixing

/-- Apply the on-axis matrix to the inclusive muon width.
The result uses unitarity only; the numerical angle formulas play no role. -/
theorem pmns_muon_width (G m : ℝ) (electron muon : Fin 3) :
    inclusive PMFlavor.PMNS.matrix electron muon
      (fun _ _ => G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3)) =
      ∫ E in (0 : ℝ)..m/2, MuonRate.rate G m E := by
  rw [MuonRate.muon_rate]
  exact equal_kinematics _ PMFlavor.PMNS.rows _ _ _

end PMFlavor.InclusiveWidth
