# PMElementaryParticles — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).
This file is the open list only.

## Program classes

- **Neutrino mass without the singlet.** The removed class is the
  right-handed-neutrino-like channel. A neutrino mass must not need it
  (`NeutrinoContext`).

## Line and ring

- **Characterise the Margin ceiling on the 43-ring.** `RingSurvivors` proves
  the Toll floor and least Toll for every firing pattern, and one saturating
  (trapping) pattern. The exact set of patterns with utilization `1` is not
  stated. Do it only if a downstream result needs it.
- **Alone/together on the 43-ring.** Single-protocol survivors are restated on
  the 43-ring (`RingSurvivors`). The alone/together (several protocols on one
  ring) result is still the 3-ring computation.

## Composition and vacuum

- **Choose the vacuum.** Both candidate references are single-site states:
  lepton `+e₀` and the colour-symmetric state. The P4 shared-vacuum tables
  remain the comparison; no shared vacuum is valid for all four record classes.
- **Settle shared versus sector-local or composite placement.** The blocker is
  the vacuum/reference choice, not the line map: two D4 sectors and a stationary
  connected background are certified, but the record-class-to-sector assignment
  is not.
- **Reference identity.** `refRecord` is not proved equal to `SharedReference`
  or `ColourReference`. The blocking item is the E8/layout reference map from
  the finite record to a D4 minimal-vector class.
- **Multi-protocol composition.** Define the composite state for `k` protocols
  on one 43-ring from the nested-paper rules. Alone/together closure cannot be
  decided until that joint state exists.

## Generations and costs

- **Identify the generation register's stay/move step with one tick of the
  conjugate-spinor walk.** `KoideCosets.cospinor_walk_koide` proves that walk
  is Koide-fair (`8 : 4 : 4`), and it is the only coset whose local roots are
  pure stays and pure ring steps (`ClockPlaneProjection`). The step from the
  43-site ring to the three-generation register is not derived.
- **Derive the generation record premise (`KoideSelection.GenerationRecord`).**
  With it, Koide follows from `LawSelection` (compiled). Show the substrate
  records a protocol's generation as one bit (triality-symmetric or
  breaking) with the norm share as its law. The lepton sector then needs one
  more derived number, `m_μ/m_e` (equivalently the Fourier phase).
- **Derive the equal split (Koide).** `KoideSplit` proves `Q = 2/3` iff the
  generation-symmetric and symmetry-breaking parts of the amplitudes have
  equal norm, i.e. the record "generation-symmetric or not" is a fair coin
  (`koide_iff_fair`; measured leptons: share `0.499998`). Capacity partitioning
  does not select a split, and the clock ledger's fair flag is a different
  coin (`shiftFlag_at_koide`: `3/8`). Derive that the substrate records a
  protocol's generation as this one bit, with no preference between its
  outcomes. Then derive the remaining phase
  from the clock (the only triality breaker). Lead: the wire mass
  `D_R (δ_O + cyc κ_O)` has a circulant factor; a Hermitian circulant amplitude
  operator meets Koide iff its on-site and hopping parts have equal norm
  (`circulant_koide`: stay weight `a²` = move weight `2|b|²`).
  Tried and failed (do not retry): the clock ledger's fair flag (`3/8` at
  Koide, `shiftFlag_at_koide`); the angle between the two ring-step kinds in
  the clock-plane metric (`arccos(21/22) = 0.306` rad, not `0.222`); the
  local-root generation walk (stay 26, moves 16/8/16; `Q = 0.52`). The bare
  library wire `diag(1,α/2,α/2)(P − I)` gives `Q = 0.883` and a massless
  lightest mode. Comparison: the measured leptons need the circulant phase
  `δ ≈ 2/9 − 1.7×10⁻⁷`; `δ = 2/9` exactly is excluded by the muon.
- **Derive the feedback coefficient of each charged lepton.** Review result
  (no arithmetic error): the muon ledger has a feedback term `(χ+σ)·α/(1−α)`;
  the tau ledger has none, and nothing derives either choice. The tau is low by
  `0.36(18) m_e` (−2.0σ). A feedback `k·α/(1−α)` brings it within 1σ for any
  `k` in `(24.5, 73.5)`, so `Δ`, `Δ+σ`, `Δ+χ+σ` all fit and the data cannot select one.
  The muon's own rule, applied to the tau (`χ+σ`, or all its non-`Δ` invariants),
  gives only −1.7σ to −1.5σ. The muon's remaining miss is `1.1×10⁻⁵ m_e ≈ 0.21 α²`,
  the size of a second-order term. Both residuals need a rule from the cost
  derivation below, not a chosen coefficient.
  Pillar route (2026-11-23), result: the ledger corrections are not the
  `PMSubstrate.Impedance` pillars under any one sign rule. With the `α⁻¹` signs,
  Capacity, Map and the regulator have the wrong sign. With all signs reversed they
  match, but Toll and Margin then give −5.6σ, and Protocol + Governor at `baseline`
  (`0.05250`) differ from the muon feedback (`0.05146`) by `+226σ`. The fit of
  baseline Toll to the muon residual (+0.18σ) is therefore withdrawn as a lead.
  The ring pillars do not split generations either: the least-cost witness pays
  one registration per period for all 45 programs (`ProgramWitness.witness_total`).
  Open: the factor `Δⁿ` must come from how many independent 43-periods a program's
  record spans; derive that count per (generation, label) and test it on the
  declared tier sets.
  Result (2026-11-23, `tools/tier_count_check.py`): one program's data cannot give
  it. Every coset root pairs ±1 with every channel vector, and the split of silent
  and one-tick roots by that pairing depends on the generation only. The only
  label-dependent datum is the label's clock reading, a phase in `Z₄₃` that also
  depends on colour and is negated between up-type and down-type. So up-type
  `{0,2,3}` against down-type `{0,1,2}` needs data outside one program (weak partner
  or composite), or the declared up tier set is a premise to review.
  Pair step blocked (2026-11-23, `tools/placement_colour_check.py`): the channel
  placement is not colour- or weak-symmetric. Only the identity and the swap of
  colours 0 and 1 preserve the inner products of the 16 placed vectors; the weak
  flip does not (doublet members are placed as `v` and `−v`). So the charge-correct
  mass pair (right singlet minus left doublet member, same colour) has norm
  `4, 4, 12` over the three colours. In a weight placement both symmetries are
  Weyl reflections and preserve inner products.
- **Derive the gauge sector that carries the 16 channels (blocks the tier
  derivation).** The internal-D4 placement breaks colour and the weak flip, and
  no internal-D4 placement can keep them (`tools/placement_d4_nogo.py`). Persistence
  elimination (`tools/pm_sector_wall.py`, `pm_sector_charge.py`; readings in the
  docstring: symmetries by root reflections, channels as E8 roots, hypercharge as a
  direction in the sector, `active` as the wall bit, least rank, then fewest roots):
  internal D4 fails (no weak reflection commutes with colour); D4 + A1 passes only if
  the charge direction may leave the sector, so hypercharge needs its own direction;
  D5 (all 12) fails symmetries + walls. Rank 6 (`tools/pm_sector_rank6.py`, 140
  sectors): D4+2A1, D4+A2, D5+A1, D6 pass; E6 failed in the instance tested.
  Fewest roots selects D4+2A1 (internal D4 + two orthogonal spacetime A1: weak flip
  and charge direction); all 18 pass and differ only by the clock (both extra roots
  silent: 3; one silent, one clock-axis: 12; both clock-axis: 3). Time reading
  (`tools/pm_sector/`): gauge roots and the charge direction commute with time
  translation (orthogonal to the clock time vector `t`). Result: a unique sector
  (both extra roots clock-silent, charge direction orthogonal to `t`); the weak flip
  is always the same extra root. It hosts all three generations with one charge
  direction. Generation `(0,1)` is disjoint from the others; `(1,0)` and `(1,1)` must
  share their quark-doublet roots. Walls: `(1,0)` and `(1,1)` put their doublets in
  the vector coset `(0,1)`; `(0,1)` may use either spinor coset.
- **Up/down tier offset from the mass pairs (`tools/pm_sector/pairs.py`).** On the
  derived sector, charge conservation fixes the pairs (up: `T3 = +1/2` member; down,
  lepton: `−1/2`). In generations `(1,0)` and `(1,1)` the up transition is one root
  step and the down transition two, for every root choice; generation `(0,1)` is
  free. Declared tiers give up − down = `0, 1, 1`: a match if the clock generation is
  tier 0 and one fewer root step is one more power of `Δ`. Step → `Δ` rule
  (`tools/pm_sector/intermediates.py`): mass is the left ↔ right flip rate; at least
  Toll a root move fires with probability `1/Δ` per tick; intermediates of a
  multi-step transition are never channels except `u_R` on the down path, which
  changes charge; so no intermediate persists (Map, Conservation), all `k` steps
  fire in one tick, and the rate goes as `Δ^−k`. To formalize in Lean. Still to
  derive: the root choice in generation `(0,1)`, the lepton choice (declared lepton
  tiers equal down's, so two steps), and the generation tiers themselves (which
  of `(1,0)`, `(1,1)` is tier 1).
  Tried (2026-11-23), does not decide: Economy as fewest distinct transition
  records. Leptons can share the down record (`h_e = h_d`) only in generation
  `(0,1)`, which narrows its (up, down, lepton) steps to `(1,1,1)`, `(2,2,2)`,
  `(1,2,2)`, `(2,1,1)`; in `(1,0)` and `(1,1)` it is never possible, and up is never the
  conjugate of down (`h_u ≠ −h_d`) in any generation.
  Generation tiers, reduction (2026-11-23): a mass flip is a wall crossing by the
  generation's own coset roots (`GaugeSector.placement_walls`; `WallCrossing`). Flips pair
  with the time vector `0` or `±2` in the clock generation and `±1` in the other two;
  a neutral ring step pairs `2`. Tried and failed: "a state must sit on the tick
  lattice, so a half-step flip cannot complete alone". It makes the clock generation
  the heaviest; the up/down offsets need it lightest (top/bottom ≈ 41 needs distinct
  tiers in the heaviest generation). Next lead: the generation register (stay/move
  walk, `KoideCosets`, `KoideSelection`), which sets generation mass ratios without
  `Δ` powers.
- **`wallClass` versus the derived walls.** Labels now use `GaugeSector.wallKey`
  (`EPSector.sector_spine`). The cyclic `ControlledGluedRegister.wallClass` disagrees
  for generation 2 (doublets in `(1,0)`; the sector needs `(0,1)`) and is still used by
  the register modules. Decide whether to restate `wallClass` from the sector. Lean
  certificates for the eliminations are open.
- **Derive the step-to-cost rule for the coset signatures.** The certified
  signatures are vector `(7,7,2)`, spinor `(4,4,0)` and conjugate spinor
  `(4,4,8)` for forward, backward and silent wall crossings. A cost per period
  must use the one-tick count for the heavy-to-light step and may use silent
  steps only to split the two light generations.
  Constraint (checked 2026-11-23): step statistics on one 43-ring cannot give
  the hierarchy. Every coset has forward = backward, so a uniform walk has no
  drift. Its period cost scales with `1/p_move` (`7/8`, `1`, `1/2`): ratios at
  most `2`. A no-backtrack period scales as `p_fwd^43`: ratios `(8/7)^43 ≈ 312`
  and `(7/4)^43 ≈ 2.8×10¹⁰`, not powers of `Δ`. The ledgers need the leading
  power `Δⁿ` (point, line, area, volume), so the rule must give each program a
  whole number `n`. It cannot depend on the generation only: lepton and down
  tiers are `{0,1,2}` but up tiers are `{0,2,3}` (`TierLedger.tiersFor`). Test
  for a candidate rule: it reproduces these declared tier sets over all
  45 programs before any mass is compared.
- **Complete the charged lift.** The static selector supplies no inverse power
  of `Δ` for the offset. A native selection and firing law, the offset's
  scaling, and the existence of shared calibration remain open.

## Everything else still open

- **Elementary masses and widths.** Derive the assignment of invariant costs to
  lepton and quark tiers, the allowed transition histories and their rates.
  Connect the charged-current operator to the physical contact vertex and
  final-state readout; the blocker is the carrier-to-protocol contact and
  readout map.
- **Radiative stage 2.** This is not started. The blocker is the assembled
  diagram kernel, not an individual loop integral.
- **Legacy single-reference assumptions.** The heavy writer's single reference
  is not certified; the choice is conditional per label. The blocker is the
  background/vacuum choice above.
