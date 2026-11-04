import PersistenceMechanics
import PMSubstrate
import PMAction
import PMConstants
import PMFlavor
import PMElementaryParticles
import PMAtoms
import PMCosmology
import Classification
import Lean

/-! Top-level strict axiom audit: every project declaration may depend only on
`propext`, `Classical.choice` and `Quot.sound`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let prefixes : List Name :=
    [`PersistenceMechanics, `PMSubstrate, `PMAction, `PMConstants,
     `PMFlavor, `PMElementaryParticles, `PMAtoms, `PMCosmology,
     `Classification, `CN1, `ELEM]
  let isProject (n : Name) : Bool := prefixes.any (fun p => p.isPrefixOf n)
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let fromProject := match env.getModuleIdxFor? name with
      | some idx => isProject env.allImportedModuleNames[idx.toNat]!
      | none => false
    if fromProject || isProject name then
      for dep in ← Lean.collectAxioms name do
        unless dep == ``propext || dep == ``Classical.choice || dep == ``Quot.sound do
          throwError "Unapproved axiom {dep} in {name}"
      checked := checked + 1
  if checked == 0 then
    throwError "No project declarations found"
  logInfo m!"Top-level strict axiom audit passed: {checked} declarations"
