import PMAtoms.CertifiedEnclosure
import PMAtoms.ShellMass
import E8PConstants.Format
import E8PConstants.Periodic

/-!
# Certified nuclear-ledger readout

`certifiedMass` is noncomputable (`π`, `A^(2/3)`, `√`); `PMAtoms.certifiedMass_bounds`
gives a computable rational enclosure `[cmLo, cmHi]` for any nucleus in the
smooth-ledger domain. This module prints it in `m_e` and in `u`, beside the frozen
measured isotope masses — the comparison, never an input.

`e8p --certified` prints the standard/extended table; `e8p --certified=Z,N` prints
one nucleus.
-/

namespace E8PConstants
open PMAtoms

/-- The smooth-ledger domain of the certified enclosure: `A > 4` and inside the
deformed frontier. -/
def certifiedDomain (z n : Nat) : Bool := decide (4 < z + n) && PMAtoms.deformedFrontierB z n

/-- Certified `m_e` enclosure of the smooth nuclear ledger. -/
def certifiedME (z n : Nat) : Option (Rat × Rat) :=
  if certifiedDomain z n then some (cmLo z n 6, cmHi z n 6) else none

/-- Certified enclosure in atomic mass units (via the electron-mass unit input). -/
def certifiedU (z n : Nat) : Option (Rat × Rat) :=
  (certifiedME z n).map (fun p => (p.1 * electronMassU, p.2 * electronMassU))

/-- The **full** E8 nuclear mass (smooth certified ledger + the single-particle shell correction)
in atomic mass units, at Strutinsky window `w`. -/
def certifiedFullU (z n w : Nat) : Option (Rat × Rat) :=
  (certifiedME z n).map (fun p =>
    ((p.1 + shellMassLo z n w) * electronMassU, (p.2 + shellMassHi z n w) * electronMassU))

def regimeStr (z n : Nat) : String :=
  match PMAtoms.regimeOf z n with
  | .light => "light" | .mid => "mid"
  | .deformedActinide => "deformed" | .beyondFrontier => "beyond"

/-- Frozen measured isotope mass in `u` (comparison only). -/
def isoMass (z a : Nat) : Option Rat :=
  match findIsotopeMass z a with
  | some m => some m
  | none => (extendedIsotopeMassU.find? (fun ((z', a'), _) => z' = z ∧ a' = a)).map (fun (_, m) => m)

/-- `lo..hi` at `p` decimals. -/
def bracket (lo hi : Rat) (p : Nat) : String :=
  s!"{fixedDecimal (lowerScaled lo p) p}..{fixedDecimal (upperScaled hi p) p}"

def isoStr (z a : Nat) : String :=
  match isoMass z a with
  | some m => fixedDecimal (lowerScaled m 6) 6
  | none => "—"

def diffStr (z a : Nat) (midU : Rat) : String :=
  match isoMass z a with
  | some m => (if m - midU ≥ 0 then "+" else "") ++ fixedDecimal (lowerScaled (m - midU) 6) 6
  | none => "—"

def certifiedRow (z a : Nat) : String :=
  let n := a - z
  let meStr := match certifiedME z n with
    | some p => bracket p.1 p.2 4
    | none => "—"
  let uStr := match certifiedU z n with
    | some p => bracket p.1 p.2 6
    | none => "—"
  let dif := match certifiedU z n with
    | some p => diffStr z a ((p.1 + p.2) / 2)
    | none => "—"
  s!"{z}  {symbol z}  {a}  {n}  {meStr}  {uStr}  {isoStr z a}  {dif}  {regimeStr z n}"

/-- Standard isotopes (`Z = 1..maxZ`) plus the extended comparison set. -/
def certifiedNuclei (maxZ : Nat) : List (Nat × Nat) :=
  ((List.range maxZ).map (fun i => (i + 1, standardMassNumber.getD i (2 * (i + 1)))))
    ++ extendedIsotopeMassU.map (fun ((z, a), _) => (z, a))

def certifiedTable (maxZ : Nat) : List String :=
  let header :=
    "Z  Sym  A   N   certified(m_e)           certified(u)          m_iso(u)     Δ(u)        regime"
  let note :=
    "certified = proved rational enclosure of certifiedMass (E8 six-pillar ledger, m_e then u); " ++
    "m_iso = frozen measured isotope mass (comparison); Δ = m_iso − certified midpoint; " ++
    "— = outside the smooth-ledger domain."
  (header :: (certifiedNuclei maxZ).map (fun p => certifiedRow p.1 p.2)) ++ ["", note]

/-- One nucleus, with the interval in `m_e` and `u` and the comparison. -/
def certifiedNuclide (z n : Nat) : List String :=
  let a := z + n
  match certifiedME z n, certifiedU z n with
  | some p, some q =>
      [ s!"{symbol z}-{a}  Z={z} N={n}  regime={regimeStr z n}",
        s!"  certified m_e   {bracket p.1 p.2 4}",
        s!"  certified u     {bracket q.1 q.2 6}",
        s!"  m_iso u         {isoStr z a}",
        s!"  Δ u             {diffStr z a ((q.1 + q.2) / 2)}" ]
  | _, _ =>
      [ s!"{symbol z}-{a}  Z={z} N={n}",
        "  outside the smooth-ledger domain (or A ≤ 4): no certified enclosure" ]

end E8PConstants
