import PMAtoms.Shells
import PMAtoms.Nucleus
import PMAtoms.Hydrogen
import PMHadrons.CompositeMasses
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# A proper electron-cloud system

The cloud is a `Finset` of occupied spin-orbitals `(n, l, m, spin)`. A set
automatically enforces Pauli (occupation 0/1 per spin-orbital). Its energy is the
hydrogenic E8 readout `ε_n = −R∞/n²` from `Hydrogen` (R∞ from the certified α and
the supplied electron rest energy). Filling is variational: take the lowest-`n`
orbitals first, not a supplied Aufbau order.

The cloud is the lepton/charge sector; an atom is the combination
`nucleus + cloud`, constrained by charge neutrality.
-/

noncomputable section
namespace PMAtoms

/-- A spin-orbital: principal `n`, orbital `l`, magnetic `m`, spin up/down. -/
structure SpinOrbital where
  n : Nat
  l : Nat
  m : Int
  spin : Bool
  deriving DecidableEq, Repr

/-- The cloud state: a set of occupied spin-orbitals (Pauli by construction). -/
abbrev Cloud := Finset SpinOrbital

namespace Cloud

def electrons (C : Cloud) : Nat := C.card

def charge (C : Cloud) : Int := -(C.card : Int)

/-- Hydrogenic orbital energy in eV: `−R∞/n²` per electron. -/
def orbitalEnergyEV (o : SpinOrbital) : ℝ := -rydbergEV / (o.n : ℝ) ^ 2

/-- Total cloud binding energy in eV (negative). -/
def bindingEV (C : Cloud) : ℝ := C.sum (fun o => orbitalEnergyEV o)

theorem binding_nonpos (C : Cloud) : bindingEV C ≤ 0 := by
  unfold bindingEV
  apply Finset.sum_nonpos
  intro o _
  unfold orbitalEnergyEV
  have hR : 0 ≤ rydbergEV := by
    unfold rydbergEV rydbergEnergy electronMassEV PMSubstrate.SIUnits.electronMassEV
    positivity
  have hn : 0 ≤ (o.n : ℝ) ^ 2 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hR) hn

/-- Cloud mass correction in electron-mass units: `binding/c² / m_e`. -/
def massCorrectionME (C : Cloud) : ℝ := bindingEV C / electronMassEV

end Cloud

/-- The occupied-orbital list, ordered by `n` then `l` then `m` then spin.
This is the variational hydrogenic order (lowest `n` first). -/
def orbitalList : List SpinOrbital :=
  (List.range 4).flatMap (fun n =>
    (List.range (n + 1)).flatMap (fun l =>
      (List.range (2 * l + 1)).flatMap (fun m =>
        let mm : Int := (m : Int) - (l : Int)
        [⟨n + 1, l, mm, true⟩, ⟨n + 1, l, mm, false⟩])))

/-- Fill `Z` electrons into the lowest hydrogenic orbitals. -/
def fillCloud (z : Nat) : Cloud := (orbitalList.take z).toFinset

/-- The hydrogenic sum `Σ 1/n²` over the same occupied orbitals. -/
def cloudSum (z : ℕ) : ℚ :=
  ((orbitalList.take z).map (fun o => (1 : ℚ) / (o.n : ℚ) ^ 2)).sum

theorem orbitalList_nodup : orbitalList.Nodup := by
  decide

/-- The cloud binding energy is the certified Rydberg energy times the same
orbital sum. -/
theorem bindingEV_fillCloud (z : ℕ) :
    Cloud.bindingEV (fillCloud z) = -rydbergEV * (cloudSum z : ℝ) := by
  unfold Cloud.bindingEV fillCloud cloudSum Cloud.orbitalEnergyEV
  rw [List.sum_toFinset _ (List.Pairwise.take (i := z) orbitalList_nodup)]
  have hleft : (List.map (fun o => -rydbergEV / (o.n : ℝ) ^ 2)
        (List.take z orbitalList)).sum =
      -rydbergEV * (List.map (fun o => (1 : ℝ) / (o.n : ℝ) ^ 2)
        (List.take z orbitalList)).sum := by
    rw [show (fun o : SpinOrbital => -rydbergEV / (o.n : ℝ) ^ 2) =
        (fun o : SpinOrbital => -rydbergEV * (1 / (o.n : ℝ) ^ 2)) by
      funext o
      ring]
    exact List.sum_map_mul_left _ _ _
  have hcast : ∀ l : List SpinOrbital,
      (List.map (fun o => (1 : ℝ) / (o.n : ℝ) ^ 2) l).sum =
        ((List.map (fun o => (1 : ℚ) / (o.n : ℚ) ^ 2) l).sum : ℝ) := by
    intro l
    induction l with
    | nil => norm_num
    | cons o l ih =>
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih]
        push_cast
        ring
  rw [hleft, hcast (List.take z orbitalList)]

/-- The combined atom: nucleus (colour/baryon sector) + electron cloud
(lepton/charge sector). -/
structure AtomSystem where
  nucleus : Nuclide
  cloud : Cloud

namespace AtomSystem

def electrons (a : AtomSystem) : Nat := a.cloud.electrons

def netCharge (a : AtomSystem) : Int := a.nucleus.charge - (a.electrons : Int)

def neutral (a : AtomSystem) : Prop := a.electrons = a.nucleus.Z

theorem neutral_net_zero (a : AtomSystem) (h : a.neutral) : a.netCharge = 0 := by
  unfold netCharge neutral at *
  rw [h]
  simp [Nuclide.charge]

/-- Combined mass in `m_e` units: nucleons + electrons + cloud binding/c². -/
def massME (a : AtomSystem) : ℝ :=
  (a.nucleus.Z : ℝ) * PMHadrons.CompositeMasses.proton +
    (a.nucleus.N : ℝ) * PMHadrons.CompositeMasses.neutron +
    (a.electrons : ℝ) + a.cloud.massCorrectionME

end AtomSystem

end PMAtoms
