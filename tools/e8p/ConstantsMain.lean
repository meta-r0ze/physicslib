import E8PConstants
import E8PConstants.Periodic
import E8PConstants.Nuclear
import E8PConstants.LineTable

open E8PConstants

private def usage : String :=
  "Usage: e8p [--paper=N] [--only=ID,...] [--json] [--latex] [--audit] [--digits N] [--periodic-table]\n" ++
  "  --paper=N     only values derived in Paper N (0 = substrate invariants)\n" ++
  "  --only=IDS    comma-separated ids (e.g. --only=wolf_rho,omega_ratio)\n" ++
  "  --json        machine-readable report (schema pm.e8p.v1)\n" ++
  "  --latex       %<*tag>...%</tag> blocks for the manuscript\n" ++
  "  --audit       compare each value with its experimental reference (σ), with status glyphs\n" ++
  "  --digits N    0..50 (default 18); more digits do not narrow the intervals\n" ++
  "  --periodic-table [N]  shell-capacity periodic table (default 20)\n" ++
  "  --nuclear       typed nuclear-graph diagnostic (H-3/He-3/He-4)\n" ++
  "  --line-table    line/ring mass diagnostic (E8 weights, Coulomb omitted)\n"

structure Opts where
  json : Bool := false
  latex : Bool := false
  audit : Bool := false
  periodic : Option Nat := none
  nuclear : Bool := false
  lineTable : Bool := false
  paper : Option Nat := none
  only : Option (List String) := none
  digits : Nat := 18

private def parsePaper (s : String) : Except String Nat :=
  match s.toNat? with
  | some p => if p ≤ 6 then .ok p else .error "unknown paper (0..6)"
  | none => .error "--paper requires an integer"

private def splitIds (s : String) : List String :=
  (s.splitOn ",").filter (fun x => x ≠ "")

private def parse : List String → Except String Opts
  | [] => .ok {}
  | "--json" :: rest => do let o ← parse rest; .ok { o with json := true }
  | "--latex" :: rest => do let o ← parse rest; .ok { o with latex := true }
  | "--audit" :: rest => do let o ← parse rest; .ok { o with audit := true }
  | "--nuclear" :: rest => do let o ← parse rest; .ok { o with nuclear := true }
  | "--line-table" :: rest => do let o ← parse rest; .ok { o with lineTable := true }
  | "--periodic-table" :: n :: rest =>
      match n.toNat? with
      | some k =>
          if k ≤ 118 then do let o ← parse rest; .ok { o with periodic := some k }
          else .error "--periodic-table N must be 1..118"
      | none => do let o ← parse (n :: rest); .ok { o with periodic := some 20 }
  | ["--periodic-table"] => .ok { periodic := some 20 }
  | "--digits" :: n :: rest =>
      match n.toNat? with
      | some d => if d ≤ 50 then do let o ← parse rest; .ok { o with digits := d }
        else .error "--digits must be 0..50"
      | none => .error "--digits requires an integer 0..50"
  | "--paper" :: n :: rest => do
      let p ← parsePaper n
      let o ← parse rest; .ok { o with paper := some p }
  | "--only" :: ids :: rest => do
      let o ← parse rest; .ok { o with only := some (splitIds ids) }
  | s :: rest =>
      if s.startsWith "--paper=" then do
        let p ← parsePaper (s.drop 8).toString
        let o ← parse rest; .ok { o with paper := some p }
      else if s.startsWith "--only=" then do
        let o ← parse rest; .ok { o with only := some (splitIds (s.drop 7).toString) }
      else if s.startsWith "--periodic-table=" then
        match (s.drop 17).toString.toNat? with
        | some k =>
            if k ≤ 118 then do let o ← parse rest; .ok { o with periodic := some k }
            else .error "--periodic-table N must be 1..118"
        | none => .error "--periodic-table requires an integer 1..118"
      else .error s!"Unknown or incomplete option: {s}"

private def absRat (q : Rat) : Rat := if q ≥ 0 then q else -q

private def keysFor (o : Opts) : List Key :=
  let ks := match o.paper with
    | some p => keys.filter (fun k => Key.paper k = p)
    | none => keys
  match o.only with
  | some ids => ks.filter (fun k => ids.contains k.id)
  | none => ks

private def sectionOrder : List String :=
  ["Substrate", "Constants", "Flavor", "Elementary Particles", "Atoms", "Cosmology"]

private def sections (ks : List Key) : List String :=
  sectionOrder.filter (fun s => ks.any (fun k => k.section = s))

/-- Print the selected keys grouped by paper, friendly detail per value. -/
private def printText (ks : List Key) (o : Opts) : IO Unit := do
  let out ← IO.getStdout
  if ks.isEmpty then
    out.putStrLn "e8p: no values match the filter."
    return
  out.putStrLn "e8p: certified enclosures of conditional model values, with experimental comparisons."
  out.putStrLn "Intervals are exact-rational roundings; 'supplied input' rows are not predictions.\n"
  for s in sections ks do
    out.putStrLn s
    for k in ks.filter (fun k => k.section = s) do
      for line in detailLines k o.digits do out.putStrLn line
    out.putStrLn ""

private def printAudit (ks : List Key) (o : Opts) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn "e8p audit — certified model vs experimental reference (display σ is exact rational)."
  out.putStrLn "glyph: ✓ |σ|≤1, ~ |σ|≤2, ! >2; intervals are the model's certified enclosure.\n"
  let mut withRef : List Key := []
  for s in sections ks do
    let group := ks.filter (fun k => k.section = s)
    let groupRefs := group.filter (fun k => !(expRefs k).isEmpty)
    if groupRefs.isEmpty then continue
    out.putStrLn s
    for k in groupRefs do
      for line in auditBlocks k o.digits do out.putStrLn line
      withRef := k :: withRef
    out.putStrLn ""
  let sigs := withRef.flatMap (fun k => (expRefs k).map (fun r => sigmaRat k r))
  let n := sigs.length
  let within (t : Rat) := (sigs.filter (fun s => absRat s ≤ t)).length
  out.putStrLn s!"{n} comparisons over {withRef.length} values:"
  out.putStrLn s!"  |σ| ≤ 1: {within 1}   |σ| ≤ 2: {within 2}   |σ| ≤ 3: {within 3}"
  let noRef := ks.filter (fun k => (expRefs k).isEmpty)
  if !noRef.isEmpty then
    out.putStrLn s!"  {noRef.length} values have no experimental reference (certified intervals only)."

def main (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    (← IO.getStdout).putStr usage
    return 0
  match parse args with
  | .error e =>
    (← IO.getStderr).putStrLn (e ++ "\n" ++ usage)
    return 2
  | .ok o =>
    let out ← IO.getStdout
    let ks := keysFor o
    if o.lineTable then
      for line in lineTable 20 do out.putStrLn line
    else if o.nuclear then
      for line in nuclearTable do out.putStrLn line
    else if let some n := o.periodic then
      for line in periodicTable n do out.putStrLn line
    else if o.json then
      out.putStrLn ((reportJson o.digits o.paper ks).compress)
    else if o.latex then
      for k in ks do
        for line in latexRows k o.digits do out.putStrLn line
    else if o.audit then
      printAudit ks o
    else
      printText ks o
    return 0
