import PMAtoms.Shells
import PMAtoms.Aufbau
import PMAtoms.ElectronCloud
import PMAtoms.NuclearRegime
import E8PConstants.Format

/-!
# Periodic-table readout from the proved shell capacities

`PMAtoms.Shells` proves `orbitalCapacity l = 2(2l+1)` and `shellCapacity n = 2n²`.
This module fills the subshells in the supplied Aufbau order (a model input, not
derived) and prints the resulting electron configuration. The capacities are
Lean-proved; the order is the usual Madelung/experimental rule.
-/

namespace E8PConstants

structure Orbital where
  n : Nat
  l : Nat
  deriving Repr, BEq, DecidableEq

/-- Madelung/Aufbau order, read from `PMAtoms.Aufbau` (a model input there). -/
def aufbau : List Orbital :=
  PMAtoms.Aufbau.aufbau.map (fun nl => ⟨nl.1, nl.2⟩)

def orbitalLabel (o : Orbital) : String :=
  let shell := ["s","p","d","f"].getD o.l "?"
  toString o.n ++ shell

/-- Fill `z` electrons in the Aufbau order, returning `(orbital, occupation)`. -/
def fill : List Orbital → Nat → List (Orbital × Nat)
  | [], _ => []
  | o :: rest, z =>
      let cap := PMAtoms.orbitalCapacity o.l
      let taken := min z cap
      if taken = 0 then [] else (o, taken) :: fill rest (z - taken)

def configuration (z : Nat) : String :=
  let parts := (fill aufbau z).map (fun (o, k) => orbitalLabel o ++ toString k)
  String.intercalate " " parts

/-- Electron mass in atomic mass units (CODATA), a unit conversion input. -/
def electronMassU : Rat := 548579909065 / 10^15

/-- Leading E8 proton weight in u, from the certified `m_p/m_e`. -/
def protonMassU : Rat := (bounds .protonRatio).1 * electronMassU

/-- Leading E8 neutron weight in u, from the certified `m_n/m_e`. -/
def neutronMassU : Rat := (bounds .neutronRatio).1 * electronMassU

/-- Leading E8 weight of `Z` protons, `N` neutrons and `Z` electrons, in u.
The nuclear binding/link term is deliberately not included here. -/
def leadingWeightU (z n : Nat) : Rat :=
  (z : Rat) * protonMassU + (n : Rat) * neutronMassU + (z : Rat) * electronMassU

/-- Standard atomic weights (IUPAC, u) for Z = 1..20, frozen comparison data. -/
def standardWeightU : List Rat := [
  1.008, 4.002602, 6.94, 9.0121831, 10.81, 12.011, 14.007, 15.999,
  18.998403163, 20.1797, 22.98976928, 24.305, 26.9815385, 28.085,
  30.973761998, 32.06, 35.45, 39.948, 39.0983, 40.078]

/-- Standard mass number (rounded atomic weight) for Z = 1..20, used only to
pick the isotope `N = A - Z` for the E8 lattice weight. -/
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

/-- E8 toll per link in u (`Z_TOL = 167/14090240 m_e`). -/
def zTolU : Rat := (167 / 14090240 : Rat) * electronMassU

/-- E8 margin per link in u (`Z_MAR = 1/343914 m_e`). -/
def zMarU : Rat := (1 / 343914 : Rat) * electronMassU

/-- `πD` read from the certified CAP value: `CAP = πΔ`, so `CAP/Δ`. -/
def piOverD : Rat := 4 * (bounds .cap).1 / 43

/-- One inter-nucleon link carries map (`πD`), protocol (`1/D`), boundary (`σ/2`),
plus toll/margin. This is the link-layer six-pillar budget. -/
def linkUnitU : Rat := (piOverD + 1/4 + 5/2 + 1/167 + 2/43) * electronMassU + zTolU + zMarU

/-- Per-shell electron count `[K,L,M,N,...]` from the configuration. -/
def shellCounts (z : Nat) : List Nat :=
  let occ := fill aufbau z
  (List.range 4).map (fun i =>
    (occ.filter (fun (o, _) => o.n = i+1)).foldl (fun acc (_, k) => acc + k) 0)

/-- Links within a shell: a ring of `n` nucleons for `n ≥ 2`, none for a
singleton. This is the shell-resolved version of the `linkOverlap` row count. -/
def shellLinks (counts : List Nat) : Nat :=
  (counts.map (fun n => if n ≤ 1 then 0 else n)).sum

/-- Capacity-use score of one species: `Σ n_s(cap_s − n_s)`. -/
def shellMid (counts : List Nat) : Nat :=
  (counts.zip [2,8,18,32]).foldl (fun acc (n, c) => acc + n * (c - n)) 0

/-- Proton + neutron capacity-use score. -/
def midScore (z n : Nat) : Nat := shellMid (shellCounts z) + shellMid (shellCounts n)

/-- E8 link count for the mass: `linkOverlap` row sum 4, two endpoints, so
`A` effective links (none for a single nucleon). The Aufbau shell occupation is
display-only and does not enter the mass. -/
def linkCount (z n : Nat) : Rat :=
  if z + n ≤ 1 then 0 else ((z + n : Nat) : Rat)

/-- Hydrogen-cloud binding series `Σ 1/n²` over the filled orbitals. -/
def cloudSum (z : Nat) : Rat :=
  ((PMAtoms.orbitalList.take z).map
    (fun o => (1 : Rat) / ((o.n : Nat) : Rat) ^ 2)).sum

/-- Cloud binding energy in eV, using the certified Rydberg bound. -/
def cloudEnergyRat (z : Nat) : Rat := -((bounds .rydbergEV).1) * cloudSum z

/-- Cloud mass correction in u (binding is negative; 1 u = 931.494e6 eV). -/
def cloudMassU (z : Nat) : Rat := cloudEnergyRat z / 931494000

/-- Six-pillar nucleon sum minus the link budget plus the cloud binding/c². -/
def boundWeightU (z n : Nat) : Rat :=
  leadingWeightU z n - linkCount z n * linkUnitU + cloudMassU z

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

/-- Regime label for the certified-ledger boundary. -/
def regimeLabel (z n : Nat) : String :=
  match PMAtoms.regimeOf z n with
  | .light => "light"
  | .mid => "mid"
  | .deformedActinide => "deformed"
  | .beyondFrontier => "beyond"

def periodicTable (maxZ : Nat) : List String :=
  let header := "Z   Sym  configuration                  K  L  M  N  A  regime     m_E8(u)*  m_iso(u)  shell  cloud(eV)"
  let rows := (List.range maxZ).map (fun i =>
    let z := i+1
    let aExp := standardMassNumber.getD i (2*z)
    let n := aExp - z
    let w := boundWeightU z n
    let ws := fixedDecimal (lowerScaled w 6) 6
    let mexp := (findIsotopeMass z aExp).getD (standardWeightU.getD i 0)
    let mes := fixedDecimal (lowerScaled mexp 6) 6
    let counts := shellCounts z
    let shells := String.intercalate "  " (counts.map toString)
    s!"{z}  {symbol z}  {configuration z}  |  {shells}  {aExp}  {regimeLabel z n}  {ws}  {mes}  {midScore z n}  {fixedDecimal (lowerScaled (cloudEnergyRat z) 2) 2}")
  (header :: rows) ++ ["", "* m_E8 = Z m_p + N m_n + Z m_e minus the E8 link budget: A effective links from the substrate link spectrum 4,1,1 (row sum 4 / two endpoints), each carrying map πD + protocol 1/D + boundary σ/2 + PRO (1/167) + GOV (2/43) + toll/margin, all positive costs subtracted. m_iso = isotopic mass. The Aufbau shell column is display-only; `2l+1` is standard SO(3), not E8, and does not enter the mass. regime = smooth-ledger validity: `beyond` rows are post-frontier comparison data, not certified smooth-ledger fits."]


theorem aufbau_length : aufbau.length = 19 := by decide

theorem standardWeightU_length : standardWeightU.length = 20 := by decide

theorem standardMassNumber_length : standardMassNumber.length = 20 := by decide

theorem isotopeMassU_length : isotopeMassU.length = 20 := by decide

theorem symbols_length : symbols.length = 98 := by decide

theorem shellCounts_length (z : Nat) : (shellCounts z).length = 4 := by
  simp [shellCounts]

theorem periodicTable_length (maxZ : Nat) : (periodicTable maxZ).length = maxZ + 3 := by
  simp [periodicTable]


/-- Extended frozen comparison masses (AME-style, u) for nuclei beyond Z=20. -/
def extendedIsotopeMassU : List ((Nat × Nat) × Rat) := [
  ((20,48), 47.9525228), ((26,56), 55.93493633), ((28,58), 57.93534241),
  ((28,62), 61.9283451), ((50,120), 119.9022016), ((54,132), 131.9041551),
  ((56,138), 137.9052472), ((60,142), 141.9077290), ((74,184), 183.9509312),
  ((79,197), 196.9665687), ((82,208), 207.9766525), ((92,238), 238.0507882),
  ((96,244), 244.0627526), ((98,252), 252.081626)]

theorem extendedIsotopeMassU_length : extendedIsotopeMassU.length = 14 := by decide

end E8PConstants
