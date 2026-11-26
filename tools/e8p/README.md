# e8p — the E8-Persistence value tool

One Lean-compiled executable that reports every value the paper series has *proved*,
as exact-rational enclosures, and compares it with a frozen experimental reference.
It generalises the old per-paper Python calculators (and `pm-constants`): the model
values come from the actual Lean theorems, not from re-implemented floating point.

Binary: **`e8p`** (E8-Persistence). Directory: `e8p`.

## Usage

```
e8p            (no options) every report in one output: values, audit, summary, nuclear,
               shells, masses, periodic table; check this in to keep everything
e8p --values   the value list alone
e8p [--paper=N] [--only=ID,...] [--json] [--latex] [--audit] [--digits N] [--periodic-table [N]] [--nuclear] [--shells] [--summary] [--masses[=Z,N]]

  --paper=N     only values derived in Paper N (0 = substrate invariants)
  --only=IDS    comma-separated ids (cheap debugging), e.g. --only=wolf_rho,omega_ratio
  --json      machine-readable report (schema pm.e8p.v1)
  --latex     %<*tag>...%</tag> blocks for the manuscript
  --audit     compare each value with its experimental reference (σ), per-paper χ² and total
  --digits N  0..50 (default 18); more digits do not narrow the intervals
  --periodic-table [N]  configuration, Hund 2S+1, E8 nuclear mass vs measured (default 20 rows)
  --nuclear       typed nuclear-graph diagnostic (H-3/He-3/He-4)
  --summary       one Markdown page (scoreboard, comparisons by agreeing digits, tensions); `e8p --summary > PREDICTIONS.md`
  --shells        E8 Nilsson single-particle ladder (PMAtoms.nilssonE8CostQ), gaps, closures vs magic numbers
  --masses        E8 nuclear ledger masses vs measured: residual, z in ledger-scatter units, summary
  --masses=Z,N    one nucleus, with what each number is (--certified[=Z,N] is an alias)
  --derivation NAME [--depth N] [--flat]
                  how NAME is proved: the tree of repository constants it uses, down to the substrate
```

Examples:
```
e8p                          # everything: values, audit, summary, nuclear, shells, masses, periodic table
e8p --values                 # grouped, friendly detail: formula, value, theorem, exp, diff, σ
e8p --paper=0                # the five substrate invariants Δ, ν, σ, χ, D
e8p --paper=5                # elementary particles + atoms
e8p --audit                  # per-value σ with ✓ / ~ / ! status, grouped by paper
e8p --audit --only=wolf_rho  # debug a single value cheaply
e8p --latex                  # tags for \CatchFileBetweenTags
e8p --periodic-table 20      # configuration, Hund 2S+1, E8 nuclear mass (certifiedMass) vs measured
e8p --nuclear                # typed pp/pn/nn counts and tetrahedron closure
e8p --masses                 # all nuclei: residuals, z in scatter units, |z| ≤ 1/2/3 counts
e8p --masses=6,6             # C-12: E8 ledger mass, measured, E8 − measured, z
e8p --json | jq .constants
e8p --derivation muon_ratio            # proof tree of a reported value, by key id
e8p --derivation muon_value --depth 3  # by unique name suffix, three levels
e8p --derivation=PMAction.OtherWallStationary.economy_selects --flat   # grouped by library
```

`--derivation` reads the kernel terms of the compiled libraries, so it needs the `src` libraries
built; it runs `tools/e8p/Derivation.lean` with `lake env lean --run`. Key ids and full names
first load their most specific compiled module, with a full-library fallback; unique suffixes
search all libraries. Lean still loads the module's transitive imports. Axiom collection uses
Lean's cached imported-module data. `--depth` limits the displayed tree; the footer still covers
the full dependency closure. Without e8p it is
`lake env lean --run tools/e8p/Derivation.lean NAME`. The tree
lists only repository constants; each is expanded once and a repeat is marked `↑`. A `(leaf)` uses no
other repository constant: a substrate definition, a supplied number or a self-contained lemma, so
the leaves of a value are where its chain stops. The footer gives the axioms the kernel needs
(`propext`, `Classical.choice`, `Quot.sound`; anything else is flagged) and the libraries crossed.
Hypotheses of a conditional theorem appear in its printed statement.


`--audit` ends with χ² and reduced χ² for each selected deriving paper and for all
selected rows. It sums **unrounded** midpoint pulls squared over scored references with
positive uncertainties; `--paper` and `--only` apply before aggregation. The nominal
degrees of freedom are `N` scored references, with no fitted parameters subtracted, so
reduced χ² is χ²/N (`n/a` at N = 0). Context-only references contribute nothing.
Correlated quantities, repeated readouts and alternative measurements are counted
separately: this is a diagonal diagnostic, not an independent global goodness-of-fit test.
The JSON comparison field `scored` records the same inclusion rule.


## Decay comparisons

Decay rows identify their observable, channel, correction order and normalization.
Text/audit output and the summary show those conventions; JSON adds a nullable `decay`
object (`observable`, `channel`, `correction_order`, `normalization`) and each comparison
has an `uncertainty_note`. LaTeX includes optional `Observable`, `CorrectionOrder` and
`ComparisonNote` tags. These are additive fields in `pm.e8p.v1`; certified model bounds
and their source formulas are unchanged.

An inverse partial width is compared with `tau_total / branching_fraction`, not with
`tau_total`. The frozen PDG 2024 references use:

| Row | Matching reference |
|---|---|
| charged-pion muonic inverse width | `26.033 ns / 0.9998770` |
| charged-kaon muonic inverse width (`kaon_muonic_partial_lifetime_s`) | `12.380 ns / 0.6356` |
| neutral-pion two-photon inverse width | `8.43e-17 s / 0.98823` |
| kaon/pion muonic width ratio | pion inverse partial lifetime / kaon inverse partial lifetime |

Reference errors use first-order quadrature from the frozen lifetime and branching
errors, rounded up, assuming independent inputs where covariance is unavailable.
Sources: [charged-meson review](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-pseudoscalar-meson-decay-cons.pdf)
and [neutral-pion listing](https://pdg.lbl.gov/2024/listings/rpp2024-list-pi-zero.pdf).
The tau's existing `0.82 fs` comparison error already combines `0.5 fs` lifetime
measurement error and approximately `0.65 fs` propagated from its supplied `B_e`.
It is not an additional experimental lifetime uncertainty and is not added twice.

Small references, errors and residuals use scientific notation rather than printing
as zero. Arithmetic enclosures certify the stated approximation, not theoretical
uncertainty from omitted radiation or channels. The normalized kaon row reads
`PMHadrons.ChargedCurrentRate.kaonMuLifetimeSeconds`. Its partial reference
shares the same kaon inputs as the scored kaon/pion width ratio, so it is
shown for context. The raw finite-kaon row is a tree-level intermediate. The muon remains context-only because `G_F` is already scored;
its caveat identifies missing finite-mass one-loop radiation as well as higher orders.

## Layout

`E8PConstants/` mirrors `src/`: a file that compares or displays the values of `src/PMX/…` lives
in `E8PConstants/PMX/`. Only the reporter core sits at the top: `Catalog` (keys, bounds, theorem
names), `Experimental` (measured references), `Format` (text/JSON/LaTeX).

| folder | files | pairs with |
|---|---|---|
| `PMSubstrate/` | `ExperimentalComparison` (α⁻¹ against CODATA/Parker/Morel/Fan) | `src/PMSubstrate` |
| `PMConstants/` | `WeakMassPulls`, `ReadoutPulls`, `ScalarAccounting`, `HyperScope` | `src/PMConstants` |
| `PMElementaryParticles/` | `LeptonMassPulls`, `QuarkMassPulls`, `TauLifetimePulls` | `src/PMElementaryParticles` |
| `PMFlavor/` | `FlavourPulls`, `ExperimentalPulls` (values only from `PMFlavor.Values`); `CandidateTests` (candidate formulas against data, not reported values) | `src/PMFlavor` |
| `PMHadrons/` | `CompositeMassPulls` | `src/PMHadrons` |
| `PMAtoms/` | `Certified` (`--masses`), `Periodic` (`--periodic-table`), `Shells` (`--shells`), `Nuclear` (`--nuclear`), `E8TickUnit` | `src/PMAtoms`, `src/PMAtoms/Values.lean` |

Namespaces are unchanged (`E8PConstants.CompositeMassPulls`, …), so theorem names cited in the
catalog do not depend on the folder.
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
- `Derivation.lean` — the `--derivation` proof-tree walker (interpreted, loads the library environment).

## Scripts

```
./check.sh    # lake build + kernel formatter fixtures + tests/constants_report.py
```

`tests/constants_report.py` independently re-checks the JSON/rounding/CLI, paper
filtering, audit, and LaTeX blocks; it does not duplicate any formula.

## Coverage and next work

See **[TODO.md](TODO.md)**. Current coverage: 98 values, matched against `PM-1-Arch/calculations/constants.txt`.
Paper 0: the substrate invariants `Δ, ν, σ, χ, D`, the derived loads
`L_intrinsic, L_embed, L_substrate, N, RM`, plus `N_c`, the GUT Weinberg angle and
the boundary-storage ratio. Paper 1: `alpha_inv`, `alpha`, and the six α⁻¹ pillars
`cap, map, protocol, governor, toll, margin`, plus `c_light`, `von_klitzing`,
the Planck-charge readouts and `planck_mass`. Paper 3: the partition/electroweak
constants, `alpha_G`, `beta_0`, `w_ratio`, the uncorrected W/Z masses, `g_weak`/`g_prime`
and `electron_closure`. The closure row tests the geometry-repaired Yukawa against the
VEV ratio in electron units. Its gap/Yukawa reading is about 0.99973. The
`electron_yukawa` row gives the Yukawa fixed by exact closure. Paper 4: CKM Jarlskog + geometric Jarlskog,
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

## EP program spine

Run `e8p --ep-spine` for the EP program spine. It reads only `PMElementaryParticles.Values`.
It shows exact counts, not fitted values: 3 generations (the nonzero glue cosets), 5 visible
classes (the total singlet is invisible), 15 visible channels per generation, and 15 programs.
Each program meets the six pillars on the 43-site ring (`spine_generations`). Masses are open.
The generation count has a catalog row, `light_generations`, compared with `N_ν` from the Z
invisible width.
