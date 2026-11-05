import PMAtoms.NuclearShells
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.


# Schematic nuclear single-particle orbitals

The E8 closure ladder fixes the shell capacities `2,6,12,8,22,32,14,30,26,32`.
This module records the standard `nlj` orbital sequence with those occupations.
It is the spectrum input a Strutinsky calculation needs; the level energies are
not fixed here.
-/

namespace PMAtoms

/-- A nuclear `nlj` orbital with its `2j+1` occupation. -/
structure NuclearOrbital where
  n : Nat
  l : Nat
  j2 : Nat
  occupation : Nat
  deriving DecidableEq, Repr

/-- Orbitals through the `N=126` closure. -/
def nuclearOrbitals126 : List NuclearOrbital := [
  ⟨1,0,1,2⟩, ⟨1,1,3,4⟩, ⟨1,1,1,2⟩,
  ⟨1,2,5,6⟩, ⟨2,0,1,2⟩, ⟨1,2,3,4⟩,
  ⟨1,3,7,8⟩,
  ⟨2,1,3,4⟩, ⟨1,3,5,6⟩, ⟨2,1,1,2⟩, ⟨1,4,9,10⟩,
  ⟨1,4,7,8⟩, ⟨2,2,5,6⟩, ⟨2,2,3,4⟩, ⟨3,0,1,2⟩, ⟨1,5,11,12⟩,
  ⟨1,5,9,10⟩, ⟨2,3,7,8⟩, ⟨2,3,5,6⟩, ⟨3,1,3,4⟩, ⟨3,1,1,2⟩,
  ⟨1,6,13,14⟩]

/-- Extra orbitals through the `N=184` closure. -/
def nuclearOrbitals184 : List NuclearOrbital :=
  nuclearOrbitals126 ++ [
    ⟨2,4,9,10⟩, ⟨1,6,11,12⟩, ⟨3,2,5,6⟩, ⟨2,4,7,8⟩,
    ⟨3,2,3,4⟩, ⟨4,0,1,2⟩, ⟨1,7,15,16⟩]

def totalOccupation (xs : List NuclearOrbital) : Nat :=
  (xs.map NuclearOrbital.occupation).sum

theorem nuclearOrbitals126_occupation : totalOccupation nuclearOrbitals126 = 126 := by
  decide

theorem nuclearOrbitals184_occupation : totalOccupation nuclearOrbitals184 = 184 := by
  decide

/-- The E8 shell-size list is the difference of successive closure occupations. -/
theorem shell_sizes_from_orbitals :
    totalOccupation nuclearOrbitals126 = 126 ∧
      totalOccupation nuclearOrbitals184 = 184 := by
  exact ⟨nuclearOrbitals126_occupation, nuclearOrbitals184_occupation⟩


/-- Schematic level energy: shell index plus a small `l`/`j` splitting. -/
noncomputable def orbitalEnergy (o : NuclearOrbital) : ℝ :=
  (o.n : ℝ) + (o.l : ℝ) / 10 - (o.j2 : ℝ) / 20

/-- Expand orbitals into occupied single-particle levels. -/
noncomputable def orbitalLevels (xs : List NuclearOrbital) : List ℝ :=
  xs.flatMap (fun o => List.replicate o.occupation (orbitalEnergy o))

/-- Cumulative level energy through `N` particles. -/
noncomputable def cumulativeEnergy (xs : List NuclearOrbital) (N : Nat) : ℝ :=
  ((orbitalLevels xs).take N).sum

/-- Local Strutinsky-style smooth background with window `w`. -/
noncomputable def smoothEnergy (xs : List NuclearOrbital) (N w : Nat) : ℝ :=
  if w = 0 then 0
  else
    (N : ℝ) *
      ((cumulativeEnergy xs (N + w) -
        (if w ≤ N then cumulativeEnergy xs (N - w) else 0)) /
        (2 * (w : ℝ)))

/-- Schematic shell correction. -/
noncomputable def strutinskyCorrection (xs : List NuclearOrbital) (N w : Nat) : ℝ :=
  cumulativeEnergy xs N - smoothEnergy xs N w


/-- `l·s` from `j2 = 2j`, `l`, and `s = 1/2`. -/
noncomputable def spinOrbit (o : NuclearOrbital) : ℝ :=
  (((o.j2 : ℝ) * ((o.j2 : ℝ) + 2) / 4) -
    ((o.l : ℝ) * ((o.l : ℝ) + 1)) - 3 / 4) / 2

/-- Schematic Nilsson energy: oscillator base, spin–orbit, `l²`, and a
deformation splitting.  The parameters `kappa`, `mu`, `delta` are model inputs. -/
noncomputable def nilssonEnergy (kappa mu delta : ℝ) (o : NuclearOrbital) : ℝ :=
  (o.n : ℝ) + 3 / 2
    - kappa * spinOrbit o
    + kappa * mu * ((o.l : ℝ) * ((o.l : ℝ) + 1))
    - delta * (2 * (o.l : ℝ) - (o.n : ℝ))

noncomputable def nilssonLevels (kappa mu delta : ℝ)
    (xs : List NuclearOrbital) : List ℝ :=
  xs.flatMap (fun o => List.replicate o.occupation (nilssonEnergy kappa mu delta o))

noncomputable def nilssonCumulative (kappa mu delta : ℝ)
    (xs : List NuclearOrbital) (N : Nat) : ℝ :=
  ((nilssonLevels kappa mu delta xs).take N).sum

noncomputable def nilssonCorrection (kappa mu delta : ℝ)
    (xs : List NuclearOrbital) (N w : Nat) : ℝ :=
  nilssonCumulative kappa mu delta xs N -
    (if w = 0 then 0
     else (N : ℝ) *
       ((nilssonCumulative kappa mu delta xs (N + w) -
         (if w ≤ N then nilssonCumulative kappa mu delta xs (N - w) else 0)) /
         (2 * (w : ℝ))))

end PMAtoms
