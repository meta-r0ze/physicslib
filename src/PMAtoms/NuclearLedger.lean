import PMAtoms.TwoLedger
import PMAtoms.NuclearRegime
import Mathlib.Tactic

/-!
# Certified nuclear ledger

`certifiedMass` is the smooth shell/packing/charge ledger.  It is valid through
the deformed-actinide frontier; the post-frontier collective regime is separate.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- The smooth certified mass ledger. -/
def certifiedMass (z n : Nat) : ℝ :=
  nuclearMassPackingShellPaired z n

/-- The certified domain: everything up to the deformed frontier. -/
def certifiedDomain (z n : Nat) : Prop :=
  deformedFrontier z n

theorem certifiedMass_eq_smooth (z n : Nat) :
    certifiedMass z n = nuclearMassPackingShellPaired z n := rfl

/-- Decomposition into the alpha/closure part plus the heavy shell part. -/
theorem certifiedMass_decomp (z n : Nat) :
    certifiedMass z n =
      nuclearMassPackingAlpha z n + shellCorrectionPaired z n := rfl

theorem certifiedMass_domain {z n : Nat} (h : certifiedDomain z n) :
    deformedFrontier z n := h

theorem certifiedDomain_cm : certifiedDomain 96 148 := cm_at_frontier

theorem certifiedDomain_cf : ¬ certifiedDomain 98 154 := cf_beyond_frontier

theorem certifiedDomain_pb : certifiedDomain 82 126 := by
  unfold certifiedDomain deformedFrontier deformedProtonShell deformedNeutronShell
  decide

theorem certifiedDomain_u : certifiedDomain 92 146 := by
  unfold certifiedDomain deformedFrontier deformedProtonShell deformedNeutronShell
  decide

end PMAtoms
