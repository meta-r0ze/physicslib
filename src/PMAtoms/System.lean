import PMAtoms.SystemTower
import PMAtoms.NuclearLedger
import PMAtoms.ElectronCloud
import PMAtoms.Particle

/-!
# The unified system type

One type spans the persistence ladder — elementary particle, nucleon, nuclide,
atom — so tables and downstream tools can be indexed by a single `System`, with
the level fixed by the constructor. Mass dispatches to the level ledger:

* particles and nucleons use the certified species masses (the six-pillar ledger);
* nuclides use the **certified nuclear ledger** `certifiedMass` (binding included);
* atoms add the electrons and the cloud binding to the certified nucleus.

So the atom-minus-nucleus gap is exactly the electron-plus-cloud contribution, and
the certified nuclide mass sits below the free lattice sum by the binding.
-/

noncomputable section
namespace PMAtoms

open PMElementaryParticles

/-- A system at any level of the persistence ladder. -/
inductive System where
  | particle (s : Species)
  | nucleon (n : Nucleon)
  | nuclide (n : Nuclide)
  | atom (a : AtomSystem)

namespace System

/-- The level of a system. -/
def level : System → Level
  | .particle _ => .particle
  | .nucleon _ => .nucleon
  | .nuclide _ => .nucleus
  | .atom _ => .atom

/-- Mass in `m_e` units. Nuclides and atoms use the **certified** nuclear ledger
(binding included); nucleons and particles use the certified species masses. -/
def mass : System → ℝ
  | .particle s => Species.mass s
  | .nucleon .proton => CompositeMasses.proton
  | .nucleon .neutron => CompositeMasses.neutron
  | .nuclide n => certifiedMass n.Z n.N
  | .atom a =>
      certifiedMass a.nucleus.Z a.nucleus.N + (a.electrons : ℝ) + a.cloud.massCorrectionME

/-- Electric charge. -/
def charge : System → ℚ
  | .particle s => Species.charge s
  | .nucleon n => Nucleon.charge n
  | .nuclide n => (n.charge : ℚ)
  | .atom a => (a.netCharge : ℚ)

/-- Baryon number. -/
def baryon : System → ℚ
  | .particle s => Species.baryon s
  | .nucleon n => Nucleon.baryon n
  | .nuclide n => (n.baryon : ℚ)
  | .atom a => (a.nucleus.baryon : ℚ)

/-- Lepton number. -/
def leptonNumber : System → ℚ
  | .particle s => Species.lepton s
  | .nucleon _ => 0
  | .nuclide _ => 0
  | .atom a => (a.electrons : ℚ)

/-- The nuclide mass is the certified ledger, by definition. -/
theorem mass_nuclide (n : Nuclide) :
    mass (.nuclide n) = certifiedMass n.Z n.N := rfl

/-- An atom's mass is its certified nucleus plus the electron and cloud contributions. -/
theorem mass_atom_decomp (a : AtomSystem) :
    mass (.atom a) =
      certifiedMass a.nucleus.Z a.nucleus.N + (a.electrons : ℝ) +
        a.cloud.massCorrectionME := rfl

/-- **The atom-minus-nucleus gap is the electron + cloud contribution.** The atom
level adds exactly its electrons and cloud binding to the certified nucleus. -/
theorem atom_sub_nucleus (a : AtomSystem) :
    mass (.atom a) - mass (.nuclide a.nucleus) =
      (a.electrons : ℝ) + a.cloud.massCorrectionME := by
  rw [mass_atom_decomp, mass_nuclide]; ring

/-- Free-constituent lattice sum minus the certified mass: the nuclear binding. -/
def binding (n : Nuclide) : ℝ := latticeSum n.Z n.N - certifiedMass n.Z n.N

/-- **The certified ledger is the free lattice sum minus the binding.** -/
theorem certifiedMass_eq_latticeSum_sub_binding (n : Nuclide) :
    certifiedMass n.Z n.N = latticeSum n.Z n.N - binding n := by
  unfold binding; ring

/-- A neutral atom has zero net charge. -/
theorem atom_neutral_net_zero (a : AtomSystem) (h : a.neutral) :
    charge (.atom a) = 0 := by
  have hc : a.netCharge = 0 := AtomSystem.neutral_net_zero a h
  show (a.netCharge : ℚ) = 0
  rw [hc]; norm_num

/-- The level of each constructor. -/
@[simp] theorem level_particle (s : Species) : level (.particle s) = .particle := rfl
@[simp] theorem level_nucleon (n : Nucleon) : level (.nucleon n) = .nucleon := rfl
@[simp] theorem level_nuclide (n : Nuclide) : level (.nuclide n) = .nucleus := rfl
@[simp] theorem level_atom (a : AtomSystem) : level (.atom a) = .atom := rfl

end System
end PMAtoms
