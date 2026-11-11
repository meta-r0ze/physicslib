import PMAtoms.ShellGaps
import E8PConstants.Format

/-!
# `--shells`: the E8 Nilsson single-particle ladder

Reports `PMAtoms.nilssonE8CostQ` (E8 strengths `κ = 1/ν = 1/16`, `μ = χ/σ = 2/5`) on every
spherical orbital through `N = 7`, sorted. Nothing here is a separate model: the cost is the
`src/` function, and this file only enumerates orbitals, sorts them and reads off the gaps.
`PMAtoms.nilssonE8_gaps` proves the gap sizes after `20, 28, 40, 50, 82, 126`; that these
orbitals are the adjacent ones is the sort below.

The ladder is cut at the first `N = 8` orbital, since the `N = 8` shell is not enumerated past it.
-/

namespace E8PConstants.Shells
open PMAtoms

/-- Spherical orbitals of oscillator shell `N` (radial `n` from `1`, `j = l ± 1/2`). -/
def shellOrbitals (N : Nat) : List NuclearOrbital :=
  ((List.range (N + 1)).reverse.filter (fun l => (N - l) % 2 == 0)).flatMap fun l =>
    let n := (N - l) / 2 + 1
    if l == 0 then [⟨n, 0, 1, 2⟩] else [⟨n, l, 2 * l + 1, 2 * l + 2⟩, ⟨n, l, 2 * l - 1, 2 * l⟩]

/-- All orbitals through `N = 8`, sorted by the E8 Nilsson cost, cut at the first `N = 8`. -/
def ladder : List NuclearOrbital :=
  let all := (List.range 9).flatMap shellOrbitals
  (all.mergeSort fun a b => decide (nilssonE8CostQ a ≤ nilssonE8CostQ b)).takeWhile
    (fun o => hoShell o < 8)

/-- Each orbital with its cumulative fill and the gap to the next orbital (`none` for the last). -/
def ladderRows : List (NuclearOrbital × Nat × Option Rat) :=
  let rec go (acc : Nat) : List NuclearOrbital → List (NuclearOrbital × Nat × Option Rat)
    | [] => []
    | [o] => [(o, acc + o.occupation, none)]
    | o :: tl@(p :: _) =>
        (o, acc + o.occupation, some (nilssonE8CostQ p - nilssonE8CostQ o)) ::
          go (acc + o.occupation) tl
  go 0 ladder

def measuredMagic : List Nat := [2, 8, 20, 28, 50, 82, 126]

/-- Fills followed by the seven largest gaps, in increasing fill. -/
def largestGapFills (k : Nat) : List Nat :=
  let gaps := ladderRows.filterMap fun (_, fill, g) => g.map (fun g => (fill, g))
  let top := (gaps.mergeSort fun a b => decide (b.2 ≤ a.2)).take k
  (top.map Prod.fst).mergeSort (· ≤ ·)

private def lChar (l : Nat) : String :=
  match "spdfghijk".toList[l]? with
  | some c => c.toString
  | none => s!"[{l}]"

def orbitalLabel (o : NuclearOrbital) : String := s!"{o.n}{lChar o.l}{o.j2}/2"

private def padL (s : String) (w : Nat) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s
private def padR (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

def shellsTable : List String :=
  let closures := largestGapFills 7
  let header := s!"{padR "orbital" 9}{padL "N" 3}{padL "2j+1" 6}{padL "fill" 6}" ++
    s!"{padL "cost (ħω)" 12}{padL "gap to next" 14}  "
  let rows := ladderRows.map fun (o, fill, g) =>
    let gapStr := match g with
      | some q => s!"{fraction q} = {ratDecimal q 4}"
      | none => "—"
    let mark := if closures.contains fill then "  ◀ closure" else ""
    s!"{padR (orbitalLabel o) 9}{padL (toString (hoShell o)) 3}{padL (toString o.occupation) 6}" ++
      s!"{padL (toString fill) 6}{padL (ratDecimal (nilssonE8CostQ o) 4) 12}{padL gapStr 14}{mark}"
  ["E8 Nilsson single-particle ladder (PMAtoms.nilssonE8CostQ: κ = 1/ν = 1/16, μ = χ/σ = 2/5)",
   "cost = N + 3/2 − κ(2 l·s + μ(l(l+1) − N(N+3)/2)) in units of ħω(A) = χ·m_p/(Δ·A^{1/3})",
   "", header] ++ rows ++
  ["",
   s!"closures (fills before the 7 largest gaps): {closures}",
   s!"measured magic numbers:                       {measuredMagic}",
   (if closures == measuredMagic then "  same set" else "  sets differ"),
   "gap sizes after 20, 28, 40, 50, 82, 126 are proved in PMAtoms.nilssonE8_gaps; the adjacency is",
   "this sort. Ladder cut at the first N = 8 orbital."]

end E8PConstants.Shells
