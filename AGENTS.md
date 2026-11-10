# AGENTS.md

## What this repo is

Lean 4 formalization of **Persistence Mechanics** applied to the vacuum. It
contains the paper-series libraries, their audits, and the `e8p` value tool.

The Lean source is the ground truth. The prose docs (`README.md`,
`src/*/OVERVIEW.md`, `src/*/REVIEW-AND-NEXT.md`, `tools/e8p/README`) are maps;
when they disagree with a theorem, the theorem wins.

Any new proofs are finding the values of the E8 substrate and *then* comparing it to
SM values. The tools/e8p contains experimental values.

When creating new proofs they should either prove out something on top of existing proofs
or show that something persists.  See the PersistenceMechanics.lean

The git repositories of the papers might be helpful if cloned for explaining more of the logic
behind the proofs.

## Layout

```text
src/PersistenceMechanics.lean + src/PersistenceMechanics/
src/PMSubstrate.lean         + src/PMSubstrate/
src/PMAction.lean            + src/PMAction/
src/PMConstants.lean         + src/PMConstants/
src/PMFlavor.lean            + src/PMFlavor/
src/PMElementaryParticles.lean + src/PMElementaryParticles/
src/PMHadrons.lean           + src/PMHadrons/
src/PMAtoms.lean             + src/PMAtoms/
src/PMCosmology.lean         + src/PMCosmology/

src/classification/          vendored class-number-one proof (Apache-2.0)
tools/e8p/                   E8-Persistence value CLI + reporter tests
src/AuditStrict.lean         standard-axiom audit
src/AuditDependencies.lean   paper import-boundary audit
```

Each paper library has its own `README.md`, `OVERVIEW.md` and
`REVIEW-AND-NEXT.md`. Read those before changing a module.

## Build and check

```sh
./build.sh                # build everything, run audits, run e8p checks
./build.sh build          # build only
./build.sh audit          # axiom + dependency audits only
./build.sh e8p            # build e8p + formatter/reporter checks
./build.sh PMAction       # one library
./build.sh src/PMAction/LatticeSiteAction.lean   # one file (OLean)
```

Fast inner loop while editing one proof. `lean` typechecks *without* writing
OLeans, so it is the quick "is my edit correct?" check; reach for `fast` only
when you actually need the compiled artifact:

```sh
./build.sh lean PMAtoms.TwoLedger   # typecheck one module (no OLean)
./build.sh lean                     # typecheck your changed/untracked .lean files
./build.sh lean PMAtoms             # typecheck a whole library (slower, one file at a time)
./build.sh fast PMAtoms.TwoLedger   # now actually build the OLean
./build.sh check src/PMAtoms/TwoLedger.lean
./build.sh watch src/PMAtoms/TwoLedger.lean
LEAN_JOBS=8 ./build.sh lean src/PMAtoms/TwoLedger.lean
```

`fast` builds only OLean artifacts (no C/ilean); `FAST_OLD=1` additionally
skips transitive dependency checks when imports are unchanged.

Under the hood this is one Lake package with one `.lake` cache. The e8p binary is
`.lake/build/bin/e8p`.

## Ground rules

- No `sorry`, `admit`, `axiom`, or `native_decide` in shipped proofs. Use
  `decide +kernel`.
- Shipped declarations may depend only on `propext`, `Classical.choice`, and
  `Quot.sound`. `src/AuditStrict.lean` enforces this.
- Preserve the paper dependency direction. `src/AuditDependencies.lean` rejects
  a paper importing a later paper.
- Do not edit `src/classification/` except for its license/provenance files; it
  is vendored Apache-2.0 code with its own `Audit.lean`.
- Do not put measured constants into theorem statements. Measured references
  belong in `tools/e8p/E8PConstants/Experimental.lean` or the falsifiable
  prediction ledger.
- When adding or changing a theorem, update the relevant `OVERVIEW.md` and
  `REVIEW-AND-NEXT.md`.
- Run `./build.sh` on the appropriate change before finishing.

## Finding things

- `source ~/.elan/env` if `lake` is not on `PATH`.
- `rg "theorem .*yang" src/PMAction`
- `#check PMAction.LatticeSiteAction.d4_yang_mills_action`
- `#print axioms ...`
- `lake env lean src/PMAction/Foo.lean`

## Scope reminder

The Yang–Mills branch is a test of persistence mechanics, not a construction of
quantum Yang–Mills. Its classical continuum limit and finite-volume Euclidean
setup are in scope; the Clay-level quantum program is not. See
`src/PMAction/OVERVIEW.md` and `src/PMAction/REVIEW-AND-NEXT.md`.
