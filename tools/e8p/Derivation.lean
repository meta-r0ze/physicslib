import Lean
import E8PConstants.Catalog

/-!
# `e8p --derivation`: how a value or theorem is proved

Run as `lake env lean --run tools/e8p/Derivation.lean NAME [--depth N] [--flat]`
(`e8p --derivation NAME` delegates here). `NAME` is an e8p key id (`--only` ids, e.g. `muon_ratio`),
a full Lean name (`PMElementaryParticles.LeptonMasses.muon_value`), or a unique name suffix.

For a key or full name, the script first tries its most specific compiled module,
falling back to all libraries when needed; suffix lookup loads all libraries. It walks
the kernel terms: each constant's type and proof or body name the constants it uses. Only constants of this repository are shown; Mathlib
and Lean core are counted, not listed. Compiler auxiliaries (`_proof_`, `match_`, equation lemmas)
are looked through. Each constant is expanded once; a repeat is marked `↑`. The leaves are the
definitions and statements nothing else in the repository supports. The footer lists the axioms the
kernel needs (expected: `propext`, `Classical.choice`, `Quot.sound`) and the libraries crossed.
-/

open Lean

namespace E8PDerivation

/-- The repository libraries, in paper order. -/
def roots : List Name :=
  [`PersistenceMechanics, `PMSubstrate, `PMAction, `PMConstants, `PMFlavor,
    `PMElementaryParticles, `PMHadrons, `PMAtoms, `PMCosmology, `Classification, `CN1, `ELEM,
    `E8PConstants, `E8PConstantsProof]

def libOf (mod : Name) : Option Name := roots.find? (·.isPrefixOf mod)

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)

def isAux (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
    match n with
    | .str _ s => s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
        s == "eq_def" || s.startsWith "_" || s == "below" || s == "brecOn" || s == "casesOn" ||
        s == "recOn" || s == "noConfusion" || s == "noConfusionType" || s == "rec"
    | _ => false

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "AXIOM"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "structure/inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor" | .quotInfo _ => "quot"

def used (ci : ConstantInfo) : List Name :=
  ci.getUsedConstantsAsSet.toList

structure St where
  cache : Std.HashMap Name (Array Name) := {}
  external : NameSet := {}

/-- The repository constants that `n` uses directly, looking through auxiliaries. -/
partial def repoDeps (env : Environment) (n : Name) : StateM St (Array Name) := do
  if let some r := (← get).cache.get? n then return r
  modify fun s => { s with cache := s.cache.insert n #[] }
  let some ci := env.find? n | return #[]
  let mut out : Array Name := #[]
  for c in used ci do
    -- a structure and its constructor name each other; show the structure once
    if c == n || (ci matches .inductInfo _ && c.getPrefix == n) then continue
    match modOf env c >>= libOf with
    | some _ =>
        if isAux c then
          for d in ← repoDeps env c do
            if d != n && !out.contains d then out := out.push d
        else if !out.contains c then out := out.push c
    | none => modify fun s => { s with external := s.external.insert c }
  modify fun s => { s with cache := s.cache.insert n out }
  return out

def resolve (env : Environment) (arg : String) : Except String Name := do
  if let some k := E8PConstants.keys.find? (·.id == arg) then
    let t := (k.theoremName.splitOn " ").head!
    let n := t.toName
    if env.contains n then return n
    throw s!"key '{arg}' names '{k.theoremName}', which is not a constant"
  let n := arg.toName
  if env.contains n then return n
  let hits := env.constants.fold (init := #[]) fun acc c _ =>
    if !isAux c && (modOf env c >>= libOf).isSome &&
        (c.toString == arg || c.toString.endsWith ("." ++ arg)) then acc.push c else acc
  match hits.toList with
  | [h] => return h
  | [] => throw s!"no e8p key or repository constant matches '{arg}'"
  | hs => throw (s!"'{arg}' is ambiguous:\n" ++ "\n".intercalate (hs.map (fun h => s!"  {h}")))

/-- Prefer the most specific compiled module named by a key/full declaration.
A namespace need not be a module, so callers check resolution and retain the
whole-library fallback. Suffix lookup always searches the whole environment. -/
partial def moduleHint (n : Name) : IO (Option Name) := do
  if n == .anonymous then return none
  try
    let _ ← findOLean n
    return some n
  catch _ => moduleHint n.getPrefix

structure Opts where
  name : Option String := none
  depth : Nat := 1000
  flat : Bool := false

def parse : List String → Except String Opts
  | [] => .ok {}
  | "--flat" :: r => do let o ← parse r; .ok { o with flat := true }
  | "--depth" :: d :: r => do
      let some k := d.toNat? | .error "--depth needs a number"
      let o ← parse r; .ok { o with depth := k }
  | s :: r => do
      if s.startsWith "--depth=" then
        let some k := (s.drop 8).toString.toNat? | .error "--depth needs a number"
        let o ← parse r; .ok { o with depth := k }
      else if s.startsWith "--" then .error s!"unknown option {s}"
      else let o ← parse r; .ok { o with name := some s }

end E8PDerivation

open E8PDerivation in
unsafe def main (args : List String) : IO UInt32 := do
  let o ← match parse args with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  let some arg := o.name
    | IO.eprintln "usage: e8p --derivation NAME [--depth N] [--flat]"; return 2
  initSearchPath (← findSysroot)
  let mods := (roots.filter (fun r => ![`E8PConstantsProof, `CN1, `ELEM, `E8PConstants].contains r) ++ [`E8PConstants.Catalog]).map (fun r => ({ module := r } : Import))
  enableInitializersExecution
  let target := match E8PConstants.keys.find? (·.id == arg) with
    | some k => ((k.theoremName.splitOn " ").head!).toName
    | none => arg.toName
  let hint ← moduleHint target.getPrefix
  -- The imported environment lives until process exit. Marking it persistent
  -- avoids reference-count traffic and a costly final traversal of its objects.
  let load (ms : Array Import) := importModules ms {} (leakEnv := true) (loadExts := true)
  let env ← match hint with
    | none => load mods.toArray
    | some m => do
        let candidate ← load #[{ module := m }]
        match resolve candidate arg with
        | .ok _ => pure candidate
        | .error _ => load mods.toArray
  let root ← match resolve env arg with
    | .ok n => pure n
    | .error e => IO.eprintln e; return 1
  let out ← IO.getStdout
  let label (n : Name) : String :=
    let k := (env.find? n).map kind |>.getD "?"
    s!"{n}  [{k}, {(modOf env n).getD Name.anonymous}]"
  -- statement
  let ci := (env.find? root).get!
  let ctx : Core.Context := { fileName := "<derivation>", fileMap := default }
  let stmt ← (do
      let fmt ← (Meta.MetaM.run' (PrettyPrinter.ppExpr ci.type)).toIO ctx { env }
      pure (toString fmt.1)) <|> pure "(statement not printable)"
  out.putStrLn s!"Derivation of {label root}"
  out.putStrLn s!"statement: {stmt}\n"
  let (_, st) := (do
      -- breadth over everything reachable, to fill the cache
      let mut seen : NameSet := {}
      let mut todo := #[root]
      while h : todo.size > 0 do
        let n := todo.back
        todo := todo.pop
        if seen.contains n then continue
        seen := seen.insert n
        for d in ← repoDeps env n do todo := todo.push d
      pure ()).run ({} : St)
  let deps (n : Name) : Array Name := st.cache.getD n #[]
  -- reachable set
  let mut reach : NameSet := {}
  let mut todo := #[root]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if reach.contains n then continue
    reach := reach.insert n
    for d in deps n do todo := todo.push d
  if o.flat then
    let byLib := roots.filterMap fun r =>
      let ns := reach.toList.filter (fun n => (modOf env n).bind libOf == some r)
      if ns.isEmpty then none else some (r, ns)
    for (r, ns) in byLib do
      out.putStrLn s!"{r} ({ns.length})"
      for n in ns.toArray.qsort (·.toString < ·.toString) do
        out.putStrLn s!"  {label n}{if (deps n).isEmpty then "  (leaf)" else ""}"
  else
    let rec walk (fuel : Nat) (n : Name) (pre : String) (depth : Nat) :
        StateT NameSet IO Unit := do
      match fuel with
      | 0 => pure ()
      | fuel + 1 =>
        let ds := deps n
        for i in [:ds.size] do
          let d := ds[i]!
          let last := i + 1 == ds.size
          let branch := if last then "└─ " else "├─ "
          let seen := (← get).contains d
          if seen then
            out.putStrLn s!"{pre}{branch}{d}  ↑"
          else
            modify (·.insert d)
            let leaf := (deps d).isEmpty
            out.putStrLn s!"{pre}{branch}{label d}{if leaf then "  (leaf)" else ""}"
            if depth + 1 < o.depth then
              walk fuel d (pre ++ (if last then "   " else "│  ")) (depth + 1)
    out.putStrLn (label root)
    let _ ← (walk (reach.size + 1) root "" 0).run (({} : NameSet).insert root)
  -- footer
  -- Lean stores axiom dependencies in imported oleans; use its cached collector
  -- instead of recursively revisiting the entire Mathlib proof graph.
  let (axs, _) ← (Lean.collectAxioms root : CoreM (Array Name)).toIO ctx { env }
  let leaves := reach.toList.filter (fun n => (deps n).isEmpty)
  out.putStrLn ""
  out.putStrLn s!"{reach.size} repository constants; {leaves.length} leaves; {st.external.size} Mathlib/core constants used directly."
  let libs := roots.filterMap fun r =>
    let c := (reach.toList.filter (fun n => (modOf env n).bind libOf == some r)).length
    if c == 0 then none else some s!"{r} {c}"
  out.putStrLn s!"libraries: {", ".intercalate libs}"
  out.putStrLn s!"axioms: {", ".intercalate (axs.toList.map toString)}"
  let extra := axs.toList.filter (fun a => ![``propext, ``Classical.choice, ``Quot.sound].contains a)
  if !extra.isEmpty then out.putStrLn s!"NON-STANDARD AXIOMS: {extra}"
  out.flush
  return 0
