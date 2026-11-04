# e8p — the E8-Persistence value tool

One Lean-compiled executable that reports every value the paper series has *proved*,
as exact-rational enclosures, and compares it with a frozen experimental reference.
It generalises the old per-paper Python calculators (and `pm-constants`): the model
values come from the actual Lean theorems, not from re-implemented floating point.

Binary: **`e8p`** (E8-Persistence). Directory: `e8p`.

## Usage

```
e8p [--paper=N] [--only=ID,...] [--json] [--latex] [--audit] [--digits N] [--periodic-table [N]] [--nuclear]

  --paper=N     only values derived in Paper N (0 = substrate invariants)
  --only=IDS    comma-separated ids (cheap debugging), e.g. --only=wolf_rho,omega_ratio
  --json      machine-readable report (schema pm.e8p.v1)
  --latex     %<*tag>...%</tag> blocks for the manuscript
  --audit     compare each value with its experimental reference (σ) + a summary
  --digits N  0..50 (default 18); more digits do not narrow the intervals
  --periodic-table [N]  shell-capacity periodic table (default 20 rows)
  --nuclear       typed nuclear-graph diagnostic (H-3/He-3/He-4)
```

Examples:
```
e8p                          # grouped, friendly detail: formula, value, theorem, exp, diff, σ
e8p --paper=0                # the five substrate invariants Δ, ν, σ, χ, D
e8p --paper=5                # elementary particles + atoms
e8p --audit                  # per-value σ with ✓ / ~ / ! status, grouped by paper
e8p --audit --only=wolf_rho  # debug a single value cheaply
e8p --latex                  # tags for \CatchFileBetweenTags
e8p --periodic-table 20      # shell configurations + E8 lattice weight vs standard weight
e8p --nuclear                # typed pp/pn/nn counts and tetrahedron closure
e8p --line-table             # line/ring mass diagnostic (E8 weights, Coulomb omitted)
e8p --json | jq .constants
```

## Architecture

- `E8PConstants/Catalog.lean` — computable `Key` catalog: exact rational `bounds`,
  unit, inputs, role, deriving-paper, theorem name, LaTeX formula. No `Real`
  evaluation.
- `E8PConstants/Experimental.lean` — frozen references (value, uncertainty, citation)
  as exact `Rat`, mirroring `PM-1-Arch/calculations/experimental_values.py`.
- `E8PConstants/Format.lean` — outward rounding, JSON, text, audit, LaTeX tags.
- `E8PConstantsProof.lean` — **certificates**: every catalog bound is proved against
  the named Lean definition (`catalog_sound`, `rounded_catalog_sound`). This is what
  makes the tool trustworthy; the runtime never evaluates a `Real`.
- `ConstantsMain.lean` — the CLI.

## Scripts

```
./check.sh    # lake build + kernel formatter fixtures + tests/constants_report.py
```

`tests/constants_report.py` independently re-checks the JSON/rounding/CLI, paper
filtering, audit, and LaTeX blocks; it does not duplicate any formula.

## Coverage and next work

See **[REVIEW-AND-NEXT.md](REVIEW-AND-NEXT.md)**. Current coverage: 98 values, matched against `PM-1-Arch/calculations/constants.txt`.
Paper 0: the substrate invariants `Δ, ν, σ, χ, D`, the derived loads
`L_intrinsic, L_embed, L_substrate, N, RM`, plus `N_c`, the GUT Weinberg angle and
the boundary-storage ratio. Paper 1: `alpha_inv`, `alpha`, and the six α⁻¹ pillars
`cap, map, protocol, governor, toll, margin`, plus `c_light`, `von_klitzing`,
the Planck-charge readouts and `planck_mass`. Paper 3: the partition/electroweak
constants, `alpha_G`, `beta_0`, `w_ratio`, the uncorrected W/Z masses, `g_weak`/`g_prime`
and `electron_closure`. Paper 4: CKM Jarlskog + geometric Jarlskog,
Cabibbo, the CKM `s13/s23/vcb`, Wolfenstein λ/A/ρ̄/η̄, three PMNS sines and
leptonic Jarlskog. Paper 5:
proton/neutron/muon/tau mass ratios, proton radius, pion and kaon masses, the six
quark masses, the pion-plus mass, and the tau lifetime. Paper 6: load, `H_late`, `S8`, propagated uncertainties, dark
ratio, both CP-to-baryon windows, and `z_eq`.

Caveat: the Paper 5 `*_mev` rows and `proton_radius` are enclosures of pull
theorems (the interval already contains the reference), so their audit `σ` is not
an independent prediction. The ratio rows (`proton_ratio`, `neutron_ratio`,
`muon_ratio`, `tau_ratio`) are direct value bounds and can be read at face value. The review
lists the values whose Lean theorems already exist (easy catalog additions), values
still needing interval proofs, and the Python scripts each addition lets us retire.

## Adding a value

1. Add a `Key` in `Catalog.lean` with `bounds`, `paper`, `theoremName`, `unit`, `formula`.
2. Add the reference in `Experimental.lean` (or leave `none`).
3. Add one case in `E8PConstantsProof.lean` (`value` + `catalog_sound`), using the
   existing bounds theorem.
4. Run `./check.sh`.

This is intentionally additive: a new Lean result becomes a reported, audited value by
adding its bound wherever it is proved.
