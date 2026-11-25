import E8PConstants
import E8PConstants.PMAtoms.Periodic
import E8PConstants.PMAtoms.Nuclear
import E8PConstants.PMAtoms.Certified
import E8PConstants.PMAtoms.Shells
import E8PConstants.Summary
import PMElementaryParticles.Values

open E8PConstants

private def usage : String :=
  "Usage: e8p            every report below, in order (values, audit, summary, nuclear, shells, masses, periodic table)\n" ++
  "       e8p --values   the value list only (the other filters below also select one report)\n" ++
  "       e8p [--paper=N] [--only=ID,...] [--json] [--latex] [--audit] [--digits N] [--periodic-table]\n" ++
  "  --paper=N     only values derived in Paper N (0 = substrate invariants)\n" ++
  "  --only=IDS    comma-separated ids (e.g. --only=wolf_rho,omega_ratio)\n" ++
  "  --json        machine-readable report (schema pm.e8p.v1)\n" ++
  "  --latex       %<*tag>...%</tag> blocks for the manuscript\n" ++
  "  --audit       compare each value with its experimental reference (σ), with status glyphs and per-paper χ²\n" ++
  "  --digits N    0..50 (default 18); more digits do not narrow the intervals\n" ++
  "  --periodic-table [N]  configuration, Hund multiplicity, E8 nuclear mass vs measured (default 20)\n" ++
  "  --nuclear       typed nuclear-graph diagnostic (H-3/He-3/He-4)\n" ++
  "  --shells        E8 Nilsson single-particle ladder, gaps and closures vs the magic numbers\n" ++
  "  --ep-spine    EP program spine: generations, visible classes, programs (exact counts)\n" ++
  "  --summary       one Markdown page: scoreboard, every comparison by agreeing digits, tensions\n" ++
  "  --masses        E8 nuclear ledger masses vs measured: residual and z in ledger-scatter units\n" ++
  "  --masses=Z,N    one nucleus, with what each number is (--certified[=Z,N] is an alias)\n" ++
  "  --derivation NAME [--depth N] [--flat]  the repository constants NAME is proved from, down to\n" ++
  "                  the substrate (NAME: a key id, a Lean name or a unique suffix; Derivation.lean)\n" ++
  ""

structure Opts where
  json : Bool := false
  latex : Bool := false
  audit : Bool := false
  periodic : Option Nat := none
  nuclear : Bool := false
  shells : Bool := false
  summary : Bool := false
  values : Bool := false
  certified : Bool := false
  certifiedNuc : Option (Nat × Nat) := none
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
  | "--shells" :: rest => do let o ← parse rest; .ok { o with shells := true }
  | "--summary" :: rest => do let o ← parse rest; .ok { o with summary := true }
  | "--values" :: rest => do let o ← parse rest; .ok { o with values := true }
  | "--certified" :: rest => do let o ← parse rest; .ok { o with certified := true }
  | "--masses" :: rest => do let o ← parse rest; .ok { o with certified := true }
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
      else if s.startsWith "--certified=" || s.startsWith "--masses=" then
        match (s.drop (if s.startsWith "--masses=" then 9 else 12)).toString.splitOn "," with
        | [zs, ns] =>
            match zs.toNat?, ns.toNat? with
            | some z, some n => do let o ← parse rest; .ok { o with certifiedNuc := some (z, n) }
            | _, _ => .error "--masses=Z,N requires two integers"
        | _ => .error "--masses=Z,N requires two integers"
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
  ["Substrate", "Constants", "Flavor", "Elementary Particles", "Hadrons", "Atoms", "Cosmology"]

/-- The keys of one section, protocol masses first. -/
private def inSection (ks : List Key) (s : String) : List Key :=
  let g := ks.filter (fun k => k.section = s)
  g.filter (fun k => k.sectionRank = 0) ++ g.filter (fun k => k.sectionRank ≠ 0)

private def sections (ks : List Key) : List String :=
  sectionOrder.filter (fun s => ks.any (fun k => k.section = s))

/-- Print the selected keys grouped by paper, friendly detail per value. -/
private def printText (ks : List Key) (o : Opts) : IO Unit := do
  let out ← IO.getStdout
  if ks.isEmpty then
    out.putStrLn "e8p: no values match the filter."
    return
  out.putStrLn "e8p: proved enclosures of conditional model values, with experimental comparisons."
  out.putStrLn "Intervals are exact-rational roundings; 'supplied input' rows are not predictions.\n"
  for s in sections ks do
    out.putStrLn s
    for k in inSection ks s do
      for line in detailLines k o.digits do out.putStrLn line
    out.putStrLn ""

private def printAudit (ks : List Key) (o : Opts) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn "e8p audit — model value (proved enclosure) vs experimental reference (display σ is exact rational)."
  out.putStrLn "glyph: ✓ |σ|≤1, ~ |σ|≤2, ! >2, · shown for context and not scored; intervals are proved enclosures of the model value, not its uncertainty.\n"
  let mut withRef : List Key := []
  for s in sections ks do
    let group := inSection ks s
    let groupRefs := group.filter (fun k => !(expRefs k).isEmpty)
    if groupRefs.isEmpty then continue
    out.putStrLn s
    for k in groupRefs do
      for line in auditBlocks k o.digits do out.putStrLn line
      withRef := k :: withRef
    out.putStrLn ""
  let sigs := scoredSigmas withRef
  let context := withRef.foldl (fun acc k => acc + ((expRefs k).filter (fun r => !scoredRef k r)).length) 0
  let n := sigs.length
  let within (t : Rat) := (sigs.filter (fun s => absRat s ≤ t)).length
  out.putStrLn s!"{n} comparisons over {withRef.length} values:"
  out.putStrLn s!"  |σ| ≤ 1: {within 1}   |σ| ≤ 2: {within 2}   |σ| ≤ 3: {within 3}"
  out.putStrLn s!"  {context} context references not scored (·): uncorrected intermediates, the superseded Jarlskog proposal, CMB references for late-universe values."
  let noRef := ks.filter (fun k => (expRefs k).isEmpty)
  if !noRef.isEmpty then
    out.putStrLn s!"  {noRef.length} values have no experimental reference (proved intervals only)."
  out.putStrLn "\nχ² diagnostic by deriving paper (scored references only):"
  out.putStrLn "  χ² = Σ(pull²); reduced χ² = χ²/N; nominal dof = N, with no fitted parameters subtracted."
  out.putStrLn "  Correlated quantities and alternative measurements are counted separately; this is not an independent goodness-of-fit test."
  for line in auditScoreLines ks do out.putStrLn s!"  {line}"

/-- `--derivation` loads the library environment, which a compiled binary does not carry; it runs
`tools/e8p/Derivation.lean` through `lake env lean --run` from the repository root. -/
private def derivation (rest : List String) : IO UInt32 := do
  let root := (← IO.appDir) / ".." / ".." / ".."
  let child ← IO.Process.spawn {
    cmd := "lake", cwd := root.toString
    args := #["env", "lean", "--run", "tools/e8p/Derivation.lean"] ++ rest.toArray }
  child.wait

/-- The EP program spine, read from `PMElementaryParticles.Values`. These are exact counts
(theorems), not fitted values. The generation count is compared with data in the catalog row
`light_generations`. -/
private def printEPSpine : IO Unit := do
  let out ← IO.getStdout
  let gens := Fintype.card PMElementaryParticles.Values.Generation
  let visible := PMElementaryParticles.Values.visibleClasses.card
  let channels := PMElementaryParticles.Values.visibleChannels.card
  let programs := Fintype.card (PMElementaryParticles.Values.Generation × {k : Fin 6 // k ≠ 4})
  out.putStrLn "EP program spine (PMElementaryParticles.Values). Exact counts; no measured input."
  out.putStrLn s!"  generations (nonzero glue keys)              {gens}  [generation_card]"
  out.putStrLn  "  weak x colour classes of the 16 channels     6"
  out.putStrLn s!"  visible classes (total singlet is invisible) {visible}  [visibleClasses_card, invisible_iff]"
  out.putStrLn s!"  visible channels per generation              {channels}  [visible_channels_card]"
  out.putStrLn s!"  programs (generation x visible class)        {programs}  [programs_card]"
  out.putStrLn "  Each program meets the six pillars on the 43-site ring and keeps its generation"
  out.putStrLn "  and its label on every forward walk [spine_generations]."
  out.putStrLn "  The invisible class has no program [singlet_no_program]."
  out.putStrLn "  Masses: open (no readout from the ring to a mass yet)."
  out.putStrLn "  Compare: light_generations row (N_nu from the Z invisible width)."

/-- Plain `e8p`: every report, each under a heading, so one checked-in file holds everything. -/
private def printAll : IO Unit := do
  let out ← IO.getStdout
  let o : Opts := {}
  let head (t : String) : IO Unit := out.putStrLn s!"\n==================== {t} ====================\n"
  head "Values"; printText keys o
  head "Audit (e8p --audit)"; printAudit keys o
  head "Summary (e8p --summary)"; for l in Summary.summaryLines do out.putStrLn l
  head "Nuclear graph (e8p --nuclear)"; for l in nuclearTable do out.putStrLn l
  head "Shells (e8p --shells)"; for l in Shells.shellsTable do out.putStrLn l
  head "Nuclear masses (e8p --masses)"; for l in certifiedTable 20 do out.putStrLn l
  head "Periodic table (e8p --periodic-table 20)"; for l in periodicTable 20 do out.putStrLn l

def main (args : List String) : IO UInt32 := do
  if let some a := args.head? then
    if a == "--derivation" then return ← derivation args.tail
    if a.startsWith "--derivation=" then
      return ← derivation ((a.drop 13).toString :: args.tail)
  if args == ["--ep-spine"] then
    printEPSpine
    return 0
  if args == ["--help"] || args == ["-h"] then
    (← IO.getStdout).putStr usage
    return 0
  if args.isEmpty then
    printAll
    return 0
  match parse args with
  | .error e =>
    (← IO.getStderr).putStrLn (e ++ "\n" ++ usage)
    return 2
  | .ok o =>
    let out ← IO.getStdout
    let ks := keysFor o
    if o.nuclear then
      for line in nuclearTable do out.putStrLn line
    else if o.summary then
      for line in Summary.summaryLines do out.putStrLn line
    else if o.shells then
      for line in Shells.shellsTable do out.putStrLn line
    else if let some (z, n) := o.certifiedNuc then
      for line in certifiedNuclide z n do out.putStrLn line
    else if o.certified then
      for line in certifiedTable 20 do out.putStrLn line
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
