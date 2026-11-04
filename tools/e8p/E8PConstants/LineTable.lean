import E8PConstants.Periodic
import PMAtoms.NuclearLine

/-!
# Line/ring mass diagnostic

Uses the E8 line/ring counts and E8 link weights `pp = πD`, `pn = πD − σ/2`,
`nn = πD + σ/2`. This is a **diagnostic** column, not the certified mass: the
Coulomb/valley term is not yet included.
-/

namespace E8PConstants

/-- `πD` from the certified CAP value `CAP = πΔ`. -/
def piDU : Rat := 4 * (bounds .cap).1 / 43

def wppU : Rat := piDU * electronMassU
def wpnU : Rat := (piDU - 5/2) * electronMassU
def wnnU : Rat := (piDU + 5/2) * electronMassU

def lineBindingU (z n : Nat) : Rat :=
  let c := PMAtoms.lineCounts z n
  wppU * (c.1 : Rat) + wpnU * (c.2.1 : Rat) + wnnU * (c.2.2 : Rat)

/-- Free constituent sum minus the line/ring binding and the open-line end cost
(one `pn` link for `Z ≠ N`). -/
def lineMassU (z n : Nat) : Rat :=
  if z + n ≤ 1 then leadingWeightU z n
  else
    let endCost := if z = n then 0 else wpnU
    leadingWeightU z n - lineBindingU z n + endCost

def lineTable (maxZ : Nat) : List String :=
  let header := "Z   Sym  A   m_line(u)   m_iso(u)    res_line"
  let rows := (List.range maxZ).map (fun i =>
    let z := i+1
    let a := standardMassNumber.getD i (2*z)
    let n := a - z
    let m := lineMassU z n
    let iso := (findIsotopeMass z a).getD (standardWeightU.getD i 0)
    let res := m - iso
    s!"{z}  {symbol z}  {a}  {fixedDecimal (lowerScaled m 6) 6}  {fixedDecimal (lowerScaled iso 6) 6}  {fixedDecimal (lowerScaled res 6) 6}")
  (header :: rows) ++ ["", "* diagnostic: E8 line/ring counts + weights pp=piD, pn=piD-sigma/2, nn=piD+sigma/2; Coulomb/valley term not yet included."]

end E8PConstants
