import PMAtoms.BetaLattice
import PersistenceMechanics.ChannelMeasure
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Beta spectral channel measure

The finite beta spectral weights as a `ChannelMeasure`.
-/

noncomputable section
namespace PMAtoms

open PersistenceMechanics.ChannelCounting

/-- Beta spectral measure on the `n×n×n` mode set. -/
def betaChannelMeasure (n : Nat) : ChannelMeasure (Fin n × (Fin n × Fin n)) :=
  { weight := fun p =>
      betaSpectralWeight n (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) }

end PMAtoms
