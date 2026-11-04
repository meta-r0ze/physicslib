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

/-! Top-level dependency audit: a paper must not import a later paper. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let anyPrefix (ps : List Name) (n : Name) : Bool := ps.any (fun p => p.isPrefixOf n)
  let forbidden (mod dep : Name) : Bool :=
    if (`PMAction).isPrefixOf mod then
      anyPrefix [`PMConstants, `PMFlavor, `PMElementaryParticles, `PMAtoms, `PMCosmology] dep
    else if (`PMConstants).isPrefixOf mod then
      anyPrefix [`PMFlavor, `PMElementaryParticles, `PMAtoms, `PMCosmology] dep
    else if (`PMFlavor).isPrefixOf mod then
      anyPrefix [`PMElementaryParticles, `PMAtoms, `PMCosmology] dep
    else if (`PMElementaryParticles).isPrefixOf mod || (`PMAtoms).isPrefixOf mod then
      (`PMCosmology).isPrefixOf dep
    else if (`PMSubstrate).isPrefixOf mod then
      anyPrefix [`PMAction, `PMConstants, `PMFlavor, `PMElementaryParticles, `PMAtoms, `PMCosmology] dep
    else if (`PersistenceMechanics).isPrefixOf mod then
      anyPrefix [`PMSubstrate, `PMAction, `PMConstants, `PMFlavor, `PMElementaryParticles, `PMAtoms, `PMCosmology] dep
    else if (`Classification).isPrefixOf mod || (`CN1).isPrefixOf mod || (`ELEM).isPrefixOf mod then
      anyPrefix [`PersistenceMechanics, `PMSubstrate, `PMAction, `PMConstants, `PMFlavor,
        `PMElementaryParticles, `PMAtoms, `PMCosmology] dep
    else
      false
  let mut checked : Nat := 0
  for idx in List.range env.header.moduleData.size do
    let mod := env.header.modules[idx]!.module
    let data := env.header.moduleData[idx]!
    for imp in data.imports do
      checked := checked + 1
      if forbidden mod imp.module then
        throwError "Forbidden dependency: {mod} imports {imp.module}"
  if checked == 0 then
    throwError "No imports found"
  logInfo m!"Top-level dependency audit passed: {checked} direct imports checked"
