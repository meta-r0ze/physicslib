import PMAtoms.CollectiveE8
import PMAtoms.NuclearShells
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Asymmetric fission with an E8 magic fragment

The observed asymmetric fission of actinides is represented by an `Sn-132`
fragment (`Z=50`, `N=82`), the double E8 closure, plus its complement.
-/

noncomputable section
namespace PMAtoms
open PMElementaryParticles PMHadrons

/-- `Sn-132`: `Z = magic50`, `N = magic82`. -/
def sn132 : Nuclide := ⟨magic50, magic82⟩

/-- The complementary fragment for a parent splitting off `Sn-132`. -/
def fissionComplement (p : Nuclide) : Nuclide :=
  ⟨p.Z - magic50, p.N - magic82⟩

theorem sn132_Z : sn132.Z = magic50 := rfl
theorem sn132_N : sn132.N = magic82 := rfl

theorem sn132_Z_eq : sn132.Z = 50 := by
  rw [sn132_Z, magic50_eq]

theorem sn132_N_eq : sn132.N = 82 := by
  rw [sn132_N, magic82_eq]

/-- Asymmetric fission channel with the E8 shell-weight barrier. -/
noncomputable def asymmetricFissionChannel (p : Nuclide) : CollectiveChannel :=
  fissionChannelE8 p sn132 (fissionComplement p)

theorem asymmetricFissionChannel_totalMass (p : Nuclide) :
    (asymmetricFissionChannel p).totalMass =
      nuclearMassPackingShellPaired sn132.Z sn132.N +
        nuclearMassPackingShellPaired (fissionComplement p).Z
          (fissionComplement p).N + fissionBarrier := rfl

/-- The magic fragment is a double E8 closure. -/
theorem sn132_double_magic :
    sn132.Z = magic50 ∧ sn132.N = magic82 :=
  ⟨sn132_Z, sn132_N⟩

end PMAtoms
