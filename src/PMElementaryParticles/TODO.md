# PMElementaryParticles — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).
This file is the open list only.

## Program classes

- **Neutrino mass without the singlet.** The removed class is the
  right-handed-neutrino-like channel. A neutrino mass must not need it
  (`NeutrinoContext`).

## Line and ring

- **Finish replacing `sectorBasis`.** The old D4 coordinates disagree with the
  clock plane (slice roots change the reading by `0` or `±6`).
  `AlignedSectors.alignedSectorBasis` is the aligned placement and
  `ChannelPlacement` uses it. `PMSubstrate.Vacuum` and `PMSubstrate.Channels`
  still use `sectorBasis`; move them and recheck their results.
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
- **Derive the step-to-cost rule for the coset signatures.** The certified
  signatures are vector `(7,7,2)`, spinor `(4,4,0)` and conjugate spinor
  `(4,4,8)` for forward, backward and silent wall crossings. A cost per period
  must use the one-tick count for the heavy-to-light step and may use silent
  steps only to split the two light generations.
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
