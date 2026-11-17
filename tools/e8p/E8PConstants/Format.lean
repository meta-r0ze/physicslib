import E8PConstants.Experimental
import Lean.Data.Json

namespace E8PConstants

def scale (digits : Nat) : Rat := (10 ^ digits : Nat)
def lowerScaled (q : Rat) (digits : Nat) : Int := (q * scale digits).floor
def upperScaled (q : Rat) (digits : Nat) : Int := (q * scale digits).ceil

/-- Fixed-point formatting of an already rounded integer; handles negatives. -/
def fixedDecimal (n : Int) (digits : Nat) : String :=
  let s := 10 ^ digits
  let a := n.natAbs
  let sign := if n < 0 then "-" else ""
  let whole := toString (a / s)
  if digits = 0 then sign ++ whole else
    let tail := toString (a % s)
    sign ++ whole ++ "." ++ String.ofList (List.replicate (digits - tail.length) '0') ++ tail

def fraction (q : Rat) : String :=
  if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

/-- Midpoint of the certified enclosure (a display quantity). -/
def central (k : Key) : Rat := ((bounds k).1 + (bounds k).2) / 2

def diffRat (k : Key) (r : ExpRef) : Rat := central k - r.value
def sigmaRat (k : Key) (r : ExpRef) : Rat := diffRat k r / r.uncertainty

/-- A decimal rendering of an exact rational at `digits` places (truncated inward). -/
def ratDecimal (q : Rat) (digits : Nat) : String :=
  fixedDecimal (lowerScaled q digits) digits

/-- Keep tiny decay references and residuals visible instead of rounding them to zero.
Exact reference rationals remain available in JSON; this is display formatting only. -/
def comparisonNumber (q : Rat) : String :=
  let a := if q < 0 then -q else q
  if a = 0 then "0" else if a < 0.000001 then
    let e : Int := (List.range 81).foldl (fun acc i =>
      let e := Int.ofNat i - 80
      if (1 / (10 ^ (-e).toNat : Nat) : Rat) ≤ a then e else acc) (-80)
    let sign := if q < 0 then "-" else ""
    sign ++ ratDecimal (a * (10 ^ (-e).toNat : Nat)) 6 ++ "e" ++ toString e
  else ratDecimal q 12

def decayText (k : Key) : String :=
  match k.decayInfo with
  | none => ""
  | some d => s!"{d.observable}; {d.channel}; {d.correctionOrder}; {d.normalization}"

def decayJson (k : Key) : Lean.Json :=
  match k.decayInfo with
  | none => Lean.Json.null
  | some d => Lean.Json.mkObj [
      ("observable", .str d.observable), ("channel", .str d.channel),
      ("correction_order", .str d.correctionOrder), ("normalization", .str d.normalization)]

/-- Signed σ with two decimals. -/
def sigmaText (k : Key) (r : ExpRef) : String :=
  if r.uncertainty = 0 then "n/a"
  else
    let s := sigmaRat k r
    let body := fixedDecimal ((s * 100).floor) 2
    if s ≥ 0 then "+" ++ body else body

/-- Scored pulls only; a reference without a positive uncertainty cannot contribute. -/
def scoredSigmas (ks : List Key) : List Rat :=
  ks.flatMap fun k =>
    ((expRefs k).filter (fun r => scoredRef k r && r.uncertainty > 0)).map (sigmaRat k)

/-- A diagonal pull diagnostic, with no fitted parameters subtracted.
Alternative measurements and correlated observables remain separate comparisons. -/
structure AuditStats where
  comparisons : Nat := 0
  chiSquared : Rat := 0
  deriving Repr, BEq, DecidableEq

def AuditStats.ofSigmas (ss : List Rat) : AuditStats :=
  { comparisons := ss.length, chiSquared := ss.foldl (fun acc s => acc + s * s) 0 }

def AuditStats.reduced (s : AuditStats) : Option Rat :=
  if s.comparisons = 0 then none else some (s.chiSquared / s.comparisons)

def auditStats (ks : List Key) : AuditStats := AuditStats.ofSigmas (scoredSigmas ks)

def auditScoreText (label : String) (ks : List Key) : String :=
  let s := auditStats ks
  let reduced := match s.reduced with
    | some r => ratDecimal r 3
    | none => "n/a"
  s!"{label}: N = {s.comparisons}; χ² = {ratDecimal s.chiSquared 3}; reduced χ² = {reduced}"

/-- Group by the catalog's deriving-paper number, even when display sections combine papers. -/
def auditScoreLines (ks : List Key) : List String :=
  let papers := (ks.map Key.paper).eraseDups.mergeSort (· ≤ ·)
  papers.map (fun p => auditScoreText s!"Paper {p}" (ks.filter (fun k => k.paper = p))) ++
    [auditScoreText "All selected" ks]

def diffText (k : Key) (r : ExpRef) : String :=
  comparisonNumber (diffRat k r)

/-- Indexed list helper (Lean core has no `List.enum`). -/
def indexed (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

/-- Audit status glyph: within 1σ, within 2σ, else flag. -/
def statusGlyph (k : Key) (r : ExpRef) : String :=
  if !scoredRef k r then "·" else
  let a := let s := sigmaRat k r; if s ≥ 0 then s else -s
  if a ≤ 1 then "✓" else if a ≤ 2 then "~" else "!"

def expValueText (r : ExpRef) : String := comparisonNumber r.value
def expUncText (r : ExpRef) : String := comparisonNumber r.uncertainty

def comparisonJson (k : Key) (r : ExpRef) : Lean.Json :=
  Lean.Json.mkObj [
    ("value", .str (fraction r.value)), ("uncertainty", .str (fraction r.uncertainty)),
    ("citation", .str r.citation), ("uncertainty_note", .str (comparisonNote k)),
    ("diff", .str (diffText k r)),
    ("sigma", .str (sigmaText k r)),
    ("scored", Lean.toJson (scoredRef k r && r.uncertainty > 0))]

def rowJson (k : Key) (digits : Nat) : Lean.Json :=
  let (lo, hi) := bounds k
  let exp := match expRef k with
    | some r => comparisonJson k r
    | none => Lean.Json.null
  Lean.Json.mkObj [
    ("id", .str k.id), ("paper", .str (toString k.paper)), ("section", .str k.section),
    ("role", .str k.role), ("unit", .str k.unit),
    ("caveat", .str k.caveat), ("decay", decayJson k),
    ("inputs", .arr (k.inputs.map Lean.Json.str).toArray),
    ("theorem", .str k.theoremName), ("formula", .str k.formula),
    ("rational_lower", .str (fraction lo)), ("rational_upper", .str (fraction hi)),
    ("decimal_lower", .str (fixedDecimal (lowerScaled lo digits) digits)),
    ("decimal_upper", .str (fixedDecimal (upperScaled hi digits) digits)),
    ("kind", .str (if lo = hi then "exact_rational" else "certified_interval")),
    ("experimental", exp),
    ("comparisons", .arr ((expRefs k).map (comparisonJson k) |>.toArray))]

def reportJson (digits : Nat) (paper : Option Nat) (ks : List Key) : Lean.Json :=
  Lean.Json.mkObj [
    ("schema", .str "pm.e8p.v1"), ("digits", Lean.toJson digits),
    ("paper", match paper with | some p => Lean.toJson p | none => .str "all"),
    ("scope", .str "Conditional model values; supplied experimental inputs are labelled."),
    ("rounding", .str "Closed bounds rounded outward with exact rational arithmetic."),
    ("constants", .arr (ks.map (fun k => rowJson k digits)).toArray)]

def rowText (k : Key) (digits : Nat) : String :=
  let (lo, hi) := bounds k
  let text := s!"[{Key.paper k}] {k.id} [{k.unit}]: [{fixedDecimal (lowerScaled lo digits) digits}, {fixedDecimal (upperScaled hi digits) digits}]"
  let exact := if lo = hi then s!"  exact {fraction lo}" else ""
  let input := if k.role == "external_input" then "  [supplied input]" else
    if k.inputs.isEmpty then "" else s!"  [uses {String.intercalate ", " k.inputs}]"
  let exp := match expRef k with
    | some r => s!"  | exp {expValueText r} ± {expUncText r} ({r.citation}): diff {diffText k r}, σ {sigmaText k r}"
    | none => ""
  let caveat := if k.caveat.isEmpty then "" else s!"  [caveat: {k.caveat}]"
  let decay := if (decayText k).isEmpty then "" else s!"  [decay: {decayText k}]"
  let note := if (comparisonNote k).isEmpty then "" else s!"  [comparison: {comparisonNote k}]"
  text ++ exact ++ input ++ exp ++ caveat ++ decay ++ note

/-- One audit line (keys with an experimental reference only). -/
def auditText (k : Key) (digits : Nat) : Option String :=
  match expRef k with
  | none => none
  | some r =>
    let (lo, hi) := bounds k
    some s!"{k.id}: model [{fixedDecimal (lowerScaled lo digits) digits}, {fixedDecimal (upperScaled hi digits) digits}] [{k.unit}] vs exp {expValueText r} ± {expUncText r} ({r.citation}) → σ {sigmaText k r}"

/-- LaTeX line set for one key (value, formula, experiment, σ). -/
def latexRows (k : Key) (digits : Nat) : List String :=
  let lo := (bounds k).1
  let tag := k.id
  let val := fixedDecimal (lowerScaled lo digits) digits
  let base := [s!"%<*{tag}Val>{val}%</{tag}Val>", s!"%<*{tag}Eq>{Key.formula k}%</{tag}Eq>"] ++
    (match k.decayInfo with
     | none => []
     | some d => [s!"%<*{tag}Observable>{d.observable}%</{tag}Observable>",
                  s!"%<*{tag}CorrectionOrder>{d.correctionOrder}%</{tag}CorrectionOrder>"]) ++
    (if (comparisonNote k).isEmpty then [] else
      [s!"%<*{tag}ComparisonNote>{comparisonNote k}%</{tag}ComparisonNote>"])
  let refs := expRefs k
  match refs with
  | [] => base
  | r :: rest =>
    base ++ [
      s!"%<*{tag}ExperimentalVal>{expValueText r} ± {expUncText r}%</{tag}ExperimentalVal>",
      s!"%<*{tag}Diff>{diffText k r}%</{tag}Diff>",
      s!"%<*{tag}Sigma>{sigmaText k r}%</{tag}Sigma>"] ++
    (indexed rest).map (fun (i, q) =>
      let suf := toString (i + 2)
      s!"%<*{tag}ExperimentalVal{suf}>{expValueText q} ± {expUncText q}%</{tag}ExperimentalVal{suf}>\n" ++
      s!"%<*{tag}Diff{suf}>{diffText k q}%</{tag}Diff{suf}>\n" ++
      s!"%<*{tag}Sigma{suf}>{sigmaText k q}%</{tag}Sigma{suf}>")

/-- Friendly multi-line detail for one key. -/
def detailLines (k : Key) (digits : Nat) : List String :=
  let (lo, hi) := bounds k
  let head := s!"  {k.id}  —  {Key.formula k}"
  let val := s!"    value   = [{fixedDecimal (lowerScaled lo digits) digits}, {fixedDecimal (upperScaled hi digits) digits}] {k.unit}"
      ++ (if lo = hi then s!"  (exact {fraction lo})" else "")
  let thm := s!"    theorem = {k.theoremName}"
  let refs := expRefs k
  let base := [head, val, thm] ++
    (if (decayText k).isEmpty then [] else [s!"    decay   = {decayText k}"]) ++
    (if k.caveat.isEmpty then [] else [s!"    note    = {k.caveat}"]) ++
    (if (comparisonNote k).isEmpty then [] else [s!"    comparison = {comparisonNote k}"])
  if refs.isEmpty then base
  else
    let blocks := (indexed refs).map (fun (i, r) =>
      let label := if refs.length = 1 then "" else s!"[{i+1}]"
      [s!"    exp{label}  = {expValueText r} ± {expUncText r}  ({r.citation})",
       s!"    diff{label} = {diffText k r}",
       s!"    σ{label}    = {sigmaText k r}"])
    base ++ (blocks.foldr (· ++ ·) [])

/-- One audit block per reference. -/
def auditBlocks (k : Key) (digits : Nat) : List String :=
  let (lo, hi) := bounds k
  (expRefs k).map (fun r =>
    s!"  {statusGlyph k r} {k.id}: model [{fixedDecimal (lowerScaled lo digits) digits}, {fixedDecimal (upperScaled hi digits) digits}] {k.unit}\n" ++
    s!"      exp {expValueText r} ± {expUncText r} ({r.citation}); diff {diffText k r}; σ {sigmaText k r}" ++
    (if (decayText k).isEmpty then "" else s!"\n      decay: {decayText k}") ++
    (if k.caveat.isEmpty then "" else s!"\n      note: {k.caveat}") ++
    (if (comparisonNote k).isEmpty then "" else s!"\n      comparison: {comparisonNote k}"))

end E8PConstants
