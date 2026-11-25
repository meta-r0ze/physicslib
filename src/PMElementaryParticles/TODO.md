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

## Six pillars on a complete charged-lepton program

The existing `ProgramWitness.Pillars` theorem certifies the fifteen
one-site witnesses. A recurrence certificate for the occupied routes
needs the actual receiver, banks, controls and payload continuation.

| Pillar | Certificate for the ring witness | Remaining complete-program proof |
| --- | --- | --- |
| Capacity | The two record rings have at most 86 registrations per period. | Fit all mutually exclusive visits and stores, including fresh inputs and retained outputs. |
| Margin | Every differing record ring stays below 43 registrations per period. | Bound peak occupancy and usable slack during the joint execution. The banked receiver alone gives two flags. |
| Map | The record differs from its reference, and the class is visible. | Read the required packet and record at the next consumer and preserve the distinctions needed for renewal. |
| Protocol | The ring tick is reversible. | Prove closure of the joint update, with each bank back in its required state or explicitly handed off. |
| Toll | Every differing ring registers at least once. | Derive which complete-program visits are required and the capacity they claim. |
| Governor | At least one site does not fire. | Derive which guards and owning resources permit each complete-program transition. |

The restoring boundary test already forces both exchanges and an
occupied reload supply when the output stays in its own bank
(`RestoringExtraction.retains_output_and_restarts_iff`). Reusing the
output as that supply empties the output bank. Every repeat that keeps
the export outside an unreplenished supply consumes one occupied input.
This is a necessary finite-resource obligation on the banked route.

## Charged-lepton mass path

Derive the total capacity claims of one repeating occupied program at
each charged-lepton address, and then compare the ratios in e8p. The
tier ledger and measured references are comparison inputs. Address 0
has the direct insertion. Addresses 1 and 2 have the restoring route.

- `ProgramCapacity.receiver_claim` applies PMKAutomaton's sum to the
  occupied charged-lepton receiver and counts twice the capacity carried
  above the prepared reference. The restoring subtotals add the two
  typed bank comparisons and the class word under their supplied
  capacity prices. The direct and gapped words also have exact per-lane
  unit and double root counts.
- `RetainedReceiverCapacity` keeps the receiver's existing marker beside
  the typed carrier. At address 2 the marker distinguishes even equal
  carrier pairs. It arrives live at entry, on the record stream at exit,
  and remains on the extracted bank value. Counting occupied slots gives
  one unit at each comparison at both restoring addresses. Derive the
  physical placement and primitive capacity assigned to that marked
  slot in the complete E8 program. The occupied-slot count gives equal
  receiver contributions, so any separation in this count comes from
  other visits.
- `DirectWriterRenewal` sums the short decoder's return pulses and the
  inverse electric exposures on the actual returned charged-lepton
  bank. With one comparison per decoder pulse and completed electric
  kick, writing and uncomputing give three flags each. Booking the
  shared-current swaps raises the sum to `13/2`. A fresh clean seed adds
  one preparation flag. Derive the capacity assigned to those
  visits and admit the companion transport, the direct flip, and return
  of the payload to its next input. The decoder alone takes 52 root
  quarter-times for write and uncompute, or 79 with fresh preparation.
- Close the full visit list, including staging and any selected static
  operation. Derive the local claims and assign each booked visit once.

The following are the inputs of the conditional spectral model. Any use
as the program's mass readout requires a derivation from the same execution.

1. **Calibrate the common clock and the two kinds of operation
   (PMKAutomaton, then EP).** Start with an occupied direct flip and the
   equal-class gapped crossing. Derive their retained ports, principal
   pulse areas, elapsed ticks and coefficient conversions on the same
   clock. This supplies the flip-to-gap ratio that PMAction's
   `WallGapCalibration` leaves free. A completed permutation alone leaves
   phase winding open. Use an independently justified principal pulse
   or a native moving-probe trial with separately retained controls.
2. **Fix the three insertion rows and the stationary calibration (EP).**
   For each restoring address connect the selected output to an
   observable on its complete interval. Test the steady-current,
   alternating and isolated readouts against that interval. A booked
   bank preserves a payload and gives a typed comparison count, with
   native staging and controller admission still open. In parallel
   with this calibration, derive the address-2 static pulse from the
   matched selector and prove that a stationary calibration channel
   maintains the common detuning after the charged insertion.
3. **Read the spectrum and check the reduction (PMAction, then e8p).**
   The ordered Schur spectrum now supports independent restoring rates
   in the small-rate regime. Check the coherent generator and common
   crossing used by the Schur calculation, then bound and match the
   full rest modes using `WallSeesawAccuracy`. Compare the ordered
   ratios with e8p after the input rates and offset have been derived.

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

## Premises and the cross-wall mass (review 2026-11-23)

- **EP premise ledger.** List every premise EP rests on, one line each, with its
  status: proved in Lean from PM, named premise, or imported from the Standard Model
  (for example the hypercharge table in `PacketGaugeActions`, the lepton axis and the
  sign as doublet index in `CarrierRepresentation`, `TierLedger` tier sets, the
  `LeptonMasses`/`QuarkMasses` ledgers, κ_τ data in `FermionMassLaw`). Order the
  eliminations by layer, node and carrier level first.
  Seeds (review 2026-11-23). EP uses a Standard Model form where an earlier module
  has a PM or E8 reason; switch to the earlier module:
  * Masses: EP's generations sit in `PMAction.CompositeMass` and its full-wall spectral test.
    The direct generation is the glue key `(0,1)`. `MassInsertionTrace` certifies the prepared
    direct record, the mixed-rule distinction for the candidate restoring readout, and the
    serial timing bounds. The admitted pulse for each route is still needed.
    `LeptonMasses`, `QuarkMasses` and `TierLedger` remain comparison premises.
  No earlier reason, so named premises: the Koide modules (a data relation), the
  supplied QED coefficients, `B_e` and `α(m_τ)` in the lifetime modules.
- **Attach the charged-lepton insertion to a reachable trace.** The open receiver
  now routes a supplied occupied arrival to the short writer. The prepared writer's
  port 2 yields `(true, true)` and supplies the companion guard. Select the native
  occupied source, bank preparation and the writer's scheduled slots. Admit and time the
  inverse bank circuit after the guard's last use. It rebalances the occupied port
  using the opposite-wall label. For each restoring address, establish the incoming
  streams and the exit consumer on the physical trace. The adjacent exchange trace
  already restores the entry reference and delivers the same payload live at the
  exit for supplied arrivals and retained requests. A four-reflection word supplies
  the subsequent class shift on both restoring routes. Its separate serial execution
  inside the node visits exceeds a single period. Establish either the admitted
  longer schedule or a native integrated operation. Calibrate the shifted pulse port
  and its elapsed ticks in crossing-clock units. `RestoringPulseCalibration`
  gives the rate under a steady floating-node current match and gives both
  insertion-to-crossing rate ratios for a supplied alternating cycle with a
  retained center. The isolated geometric exchange pair gives its own exit
  weight. `LocalController.restoring_marker_live` gives the native joint guard event
  for an isolated marker. `mass_from_scheduled_steady_pulses` carries both booked
  restoring durations into separate Schur rows. The closed marker ring
  (`RestoringRingHistory`) has exact 86-tick recurrence for successful histories.
  `IsolatedExcitation.occupied_restoring_history` makes this seed the existing
  occupied EP receiver encoding with supplied requests. At unit hazard the initial
  two visits and the full receiver cycle give opposite comparisons with the steady
  two-leg coefficient under both tested seed priors. `rate_ratio_of_history_current`
  turns a matched live-exit share into the principal area rate at supplied durations.
  The reversible tick-two bank swap retains the typed payload and feeds the
  class-shift word (`banked_exit_then_class_shift`). The receiver comparisons are
  counted exactly for this itinerary, and a fresh bank restores the phase-zero seed.
  The staged native doublet swap has an exact clocked half-pulse, and the serial
  extraction, class-word and reload windows fit for quarter-times of at most
  seven ticks with concurrent axis pulses, or three ticks with four serial
  pulses per bank operation. The signed modes have a faithful four-doublet
  encoding. Supply the physical retained axis and stage the full glued
  carrier, derive the root trial and staging visits, and use the resulting
  rates and static offset. See the [charged-lepton trace](MassInsertionTrace.lean).
  The fifteen indexed least-Toll witnesses give one flag each when run once
  and billed separately. The two-site restoring projection gives no live
  exits, and feeding the same request to both root phases always returns the
  input. A successful closed marker saturates the 43-registration Margin
  threshold on a differing record ring. The banked receiver gets two flags
  in that period. `OccupiedBankedRestoring` now attaches the typed
  extraction, class shift and fresh reload to the occupied charged-lepton
  channels for a successful booked history. The bank pair comparisons
  distinguish the restoring addresses, and the class word has an exact
  unit-step ledger by axis. Replaying the successful receiver guards gives
  a returning bank-root trial on a single probe. Determine the physical
  reference and fresh banks, stage both glued coordinates and derive the
  schedule's bank-root trial opportunities with separately retained phase
  controls. Read those endpoints before normalizing a weight.
- **Cross-wall mass from the detuning law.** The mass is the information between the
  two walls. Derive the detuning a left–right pair puts across the boundary and read
  it through `PMAction.DetuningMass` and `FermionMassLaw` law A (`δ² = y v`). Do not use
  Standard Model Yukawa matrices, Dirac flip rates or Higgs-doublet quantum numbers.
- **Tier counting (untested).** If each tier adds a record on a site distinct from those
  already used (records do not merge), the counts are falling factorials `Δ`,
  `Δ(Δ−1)`, `Δ(Δ−1)(Δ−2)`, not `Δⁿ`. Derive the count at node level before comparing.
