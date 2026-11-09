# PMFlavor — open work (todo)

Checked mathematics and the downstream handoff are in [`OVERVIEW.md`](OVERVIEW.md).
This file is only what remains. Paper IV builds clean; run `./build.sh PMFlavor`
for current counts.

The flavour derivation (mixing formulas, angles, octants, CP magnitude, mass ratios,
breaking direction, the CP-sign branch) and the carrier-current objects are all
derived or E8-sourced; see `OVERVIEW.md`. Only the two inputs below remain.

## Open items

Two genuine inputs remain; both are non-derivable.

### 1. Wall anchor magnitude `δ`

`BreakingPhase` records `(δ, ε)` and `PhysicalWall = 0<δ ∧ 0<ε<2` (the `2` is `χ`);
`physicalWall_off_exceptional` keeps physical points off the exceptional curve, and
the curve/eigenvalue constants are E8 (`MixingMatrix.rootP/rootM_eq_substrate`,
`rootMInv_eq_substrate`: the block numerals `5,8,4,3` are `σ, Dχ, D, σ−χ`). The
breaking *direction* (lepton axis) and functional form are E8; the *magnitude* is a
model input — neither E8-forced nor persistence-selected (there is no cost
functional in `δ`). Anchors recorded: `TransferFlavor.unitWall` (`δ = ε = 1`) and
the E8 candidate `TransferFlavor.ckmWall` (`δ = ε = χ/ν`).

### 2. Absolute wall-mass scale

Both ratios are E8: `WallMassRatio.capacity_ratio_sq` (`256/441 = (ν/(ν+σ))²`),
`coupling_ratio` (`25/336 = σ²/(ν(ν+σ))`), `wall_coupling_ratio_substrate`. The
absolute mass scale and physical momentum are the usual external unit/anchor input
(like `m_e`), not derived. `WallImpedanceChoice` separates the capacity mass-ratio
impedance from the physical energy-ratio diagnostic.

## Modelling boundary

Realizing the E8 carrier-parity statistics and the reference-stabilizer mediator in
a physical interaction is a modelling boundary (like the Yang–Mills scope note), not
a missing theorem. Do not reopen cycle-weight scans and do not fit `V`.

## Verification

Run `./build.sh PMFlavor`. No Paper V–VI imports; permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
