import PMAtoms.Shells
import PMAtoms.Aufbau
import PMAtoms.ElectronCloud
import E8PConstants.Format

/-!
# Periodic-table data and the electron configuration readout

Frozen comparison data (standard weights, isotope masses, element symbols) and the electron
configuration, read from `PMAtoms.Aufbau.configuration` (capacities `2(2ℓ+1)` proved in
`PMAtoms.Shells`; the fill order is a supplied input there). No mass model lives here: the
nuclear mass column of `--periodic-table` is `PMAtoms.certifiedMass` (`E8PConstants.Certified`).
-/

namespace E8PConstants

/-- `nℓ` label of a subshell. -/
def subshellLabel (nl : Nat × Nat) : String :=
  toString nl.1 ++ ["s", "p", "d", "f"].getD nl.2 "?"

/-- Electron configuration of `z` electrons, from `PMAtoms.Aufbau.configuration`. -/
def configuration (z : Nat) : String :=
  String.intercalate " "
    ((PMAtoms.Aufbau.configuration z).map (fun (nl, k) => subshellLabel nl ++ toString k))

/-- Electrons per principal shell `[K, L, M, N]`, from the same configuration. -/
def shellCounts (z : Nat) : List Nat :=
  (List.range 4).map (fun i =>
    ((PMAtoms.Aufbau.configuration z).filter (fun (nl, _) => nl.1 = i + 1)).foldl
      (fun acc (_, k) => acc + k) 0)

/-- Electron mass in atomic mass units (CODATA 2022), a unit conversion input. -/
def electronMassU : Rat := 548579909065 / 10^15

/-- Electron rest energy in MeV (CODATA 2022), a unit conversion input. -/
def electronMassMeV : Rat := 51099895069 / 10^11

/-- Hydrogenic cloud series `Σ 1/n²` over the first `z` spin-orbitals of
`PMAtoms.orbitalList` (the `ElectronCloud` filling; no screening). -/
def cloudSum (z : Nat) : Rat :=
  ((PMAtoms.orbitalList.take z).map
    (fun o => (1 : Rat) / ((o.n : Nat) : Rat) ^ 2)).sum

/-- Hydrogenic cloud binding in eV (`ElectronCloud.bindingEV` with the certified Rydberg bound). -/
def cloudEnergyRat (z : Nat) : Rat := -((bounds .rydbergEV).1) * cloudSum z

/-- Standard atomic weights (IUPAC, u) for Z = 1..20, frozen comparison data. -/
def standardWeightU : List Rat := [
  1.008, 4.002602, 6.94, 9.0121831, 10.81, 12.011, 14.007, 15.999,
  18.998403163, 20.1797, 22.98976928, 24.305, 26.9815385, 28.085,
  30.973761998, 32.06, 35.45, 39.948, 39.0983, 40.078]

/-- Standard mass number (rounded atomic weight) for Z = 1..20, used only to
pick the isotope `N = A - Z` compared in the tables. -/
def standardMassNumber : List Nat := [
  1, 4, 7, 9, 11, 12, 14, 16, 19, 20, 23, 24, 27, 28, 31, 32, 35, 40, 39, 40]

/-- Isotopic masses in u for the mass numbers used below (frozen comparison data). -/
def isotopeMassU : List ((Nat × Nat) × Rat) := [
  ((1,1), 1.00782503223), ((2,4), 4.00260325413), ((3,7), 7.0160034366),
  ((4,9), 9.012183065), ((5,11), 11.00930536), ((6,12), 12.0),
  ((7,14), 14.00307400443), ((8,16), 15.99491461957), ((9,19), 18.99840316273),
  ((10,20), 19.9924401762), ((11,23), 22.9897692820), ((12,24), 23.985041697),
  ((13,27), 26.98153853), ((14,28), 27.97692653465), ((15,31), 30.97376199842),
  ((16,32), 31.9720711744), ((17,35), 34.968852682), ((18,40), 39.9623831237),
  ((19,39), 38.9637064864), ((20,40), 39.962590863)]

def findIsotopeMass (z a : Nat) : Option Rat :=
  (isotopeMassU.find? (fun ((z', a'), _) => z' = z ∧ a' = a)).map (fun (_, m) => m)

/-- Symbols through krypton; a label table, not a derivation. -/
def symbols : List String := [
  "H","He","Li","Be","B","C","N","O","F","Ne",
  "Na","Mg","Al","Si","P","S","Cl","Ar","K","Ca",
  "Sc","Ti","V","Cr","Mn","Fe","Co","Ni","Cu","Zn",
  "Ga","Ge","As","Se","Br","Kr",
  "Rb","Sr","Y","Zr","Nb","Mo","Tc","Ru","Rh","Pd",
  "Ag","Cd","In","Sn","Sb","Te","I","Xe","Cs","Ba",
  "La","Ce","Pr","Nd","Pm","Sm","Eu","Gd","Tb","Dy",
  "Ho","Er","Tm","Yb","Lu","Hf","Ta","W","Re","Os",
  "Ir","Pt","Au","Hg","Tl","Pb","Bi","Po","At","Rn",
  "Fr","Ra","Ac","Th","Pa","U","Np","Pu","Am","Cm",
  "Bk","Cf"]

def symbol (z : Nat) : String := symbols.getD (z-1) "?"

/-- Extended frozen comparison masses (AME-style, u) for nuclei beyond Z=20. -/
def extendedIsotopeMassU : List ((Nat × Nat) × Rat) := [
  ((20,48), 47.9525228), ((26,56), 55.93493633), ((28,58), 57.93534241),
  ((28,62), 61.9283451), ((50,120), 119.9022016), ((54,132), 131.9041551),
  ((56,138), 137.9052472), ((60,142), 141.9077290), ((74,184), 183.9509312),
  ((79,197), 196.9665687), ((82,208), 207.9766525), ((92,238), 238.0507882),
  ((96,244), 244.0627526), ((98,252), 252.081626)]

theorem extendedIsotopeMassU_length : extendedIsotopeMassU.length = 14 := by decide

theorem standardWeightU_length : standardWeightU.length = 20 := by decide

theorem standardMassNumber_length : standardMassNumber.length = 20 := by decide

theorem isotopeMassU_length : isotopeMassU.length = 20 := by decide

theorem symbols_length : symbols.length = 98 := by decide

theorem shellCounts_length (z : Nat) : (shellCounts z).length = 4 := by
  simp [shellCounts]

end E8PConstants
