# PMElementaryParticles — open work

[OVERVIEW](OVERVIEW.md) records checked results. **[Premise]** marks a
physical identification or update rule still to be derived from the E8
substrate. **[Calculation]** marks work within a specified model.

None of these items blocks the downstream libraries: PMHadrons and later use the tier-ledger masses
(`QuarkMasses`, `LeptonMasses`), the E8 `G_F` and `α`, and the supplied lepton QED
(`MuonQEDLoops`). The tau's `B_e` without a supplied value is PMHadrons' "tau inclusive hadronic
factor" item.

**Common blocker.** Two items (heavy-label weight, lightest masses) and
PMFlavor item 2 wait on one object from PMAction: the native law
that fires a conditioned coherent pulse. The conversion from a Toll to a wire
amplitude is now derived (`PMAction.TollAmplitude`: `exp(−T/2)` with `T` in
expected registrations). What is still open is the schedule: which
comparisons act on which labels, at which steps and how often
([PMAction extensions](../PMAction/REVIEW-AND-NEXT.md#extensions)). The
radiative factor does not depend on it.

## The protocol readout (first)

The species masses reported by e8p currently use the tier assignments in
`QuarkMasses` and `LeptonMasses`. Derive the wire-to-species readout and use
the recorded mass ratios to check it.

- **Heavy-label weight. [Premise]** Derive a native, label-sensitive upkeep
  rule and derive which heavy-wire flip amplitudes it changes and by how much.
  The rule must distinguish the two weak partners differently in the lepton
  and colour sectors. Use the
  [toll constraints](OVERVIEW.md#protocol-toll-constraints) to screen
  candidates. [PMAction](../PMAction/REVIEW-AND-NEXT.md#extensions) owns
  pulse selection and timing.
  Derive a reference-conditioned repair history or joint response on
  the four colour orbits. The Toll constraints give the affine bound
  for sums of static hypercharge comparisons against a fixed reference.
  PMAction supplies the selected repair schedule and the conversion
  from Toll to wire amplitude. Test the resulting protocol weights
  against the recorded ladder.
  The static bound excludes an affine conversion only, and the derived
  conversion is not affine. On the static flags it admits the charged
  order and any ratio (`ProtocolToll.survival_ladder`, `doubling_iff`;
  steps `π/2` and `3π/2` as a witness, not a schedule). Each static
  step is fixed by its down flag `d`, and adds `16d(d − d₋)(d − d₊)` to
  `T_e − T_u`, `d∓ = (5 ∓ √5)/8` (`step_charged_span`). No single step
  orders the three charged labels (`single_step_no_order`), and a
  schedule with every `d` in `[d₋, d₊]` gives `T_e ≤ T_u`
  (`window_no_ladder`). The window's ends are the vacancy preparation's
  steps (`fifth_root_steps`) and the charged selector's `½` is inside, so
  the steps selected so far cannot order the labels in any counts. A
  native step with `d < d₋` or `d > d₊` (a fraction of the static period
  `3π` below `1/5`, or between `2/5` and `3/5`) is needed. The doublet
  position supplies both: a weak gate that treats the partners
  differently must export it (`RefreshMap.asymmetric_gate_records`), and
  the static comparisons that read it exactly are the full readout
  (`d = 1`, step `3π/2`; `full_readout`) and the lepton-only readout
  (`d = ¼`, step `π/2`, below the window; `lepton_readout_iff`,
  `quarter_below_window`). `n_L` lepton and `n_Q` full readouts give
  `T_e − T_d = ¾n_L` and `T_d − T_u = n_Q − ½n_L`, so the ladder holds
  exactly when `n_L > 0` and `n_Q > ½n_L`. Still to derive: the counts
  per heavy-wire flip, and why these readouts are charged to the heavy
  label. The event table is derived for one charged-current event
  (`EventRequirements`): one doublet bit, and own-event accounting ties
  `e` with `d` (`own_event_tolls`). A persisting massive label sits on
  both walls with equal weight, and its flag is the mean of its two slot
  flags (`massive_flag`, from `PMAction.DiagonalReadout.state_flag`). The
  full readout reads both bits at once (`full_reads_both`), so under
  Economy one full readout per cycle serves every event; it gives
  `T_e = T_d = ¾` and `T_u = T_ν = ¼` per readout (`full_massive`). So the
  doublet readouts split up from down (`T_d − T_u = ½` per readout) but
  never the electron from down. That split needs a mechanism that tells
  the lepton sector from the colour sector, and with `s = exp(−T/2)` it
  must reach some generations' flips and not others. A Toll paid equally
  by all three generations scales the wire's mass by one factor and
  cancels from every ratio (`uniform_weight_cancels`), so generation-blind
  upkeep (the colour refresh, the doublet readouts as computed) cannot
  give the heavy-label weight in either direction. The native generation
  difference: on the reference wall the heavy generation's carrier never
  touches the reference class, and the two light ones pass through the
  reference node (`PMAction.ReferenceClassHop`). A Toll on the node legs
  raises the effective heavy weight by `exp(T/2)` (`node_toll_raises_heavy`),
  the opposite sign to a Toll on the heavy flip. On the node path a
  colour cost gives the right electron–down order and the doublet
  readouts the wrong up–down order. Both paths are label-blind as the
  library stands: the direct insertion is a certain in-cycle event, and
  the node legs have one price because Closure gives every crossing one
  price (`PMConstants.HandoffAdmittance.closure_one_price`). That theorem
  assumes no internal label distinguishes the carried signal. A glued
  root carries the protocol label through the node, so for protocol
  labels the hypothesis is not given: the open step is the node-leg
  price of a label-carrying crossing. One candidate checked: comparing the
  crossing label's hypercharge with the lepton-doublet reference
  (both walls, `DiagonalReadout`) gives `T_e < T_d < T_u` on the node
  path, with `(T_u − T_d)/(T_d − T_e) = 6` for small steps, falling to
  `4.5` at `t = 1` and `2.7` at `π/2`. Comparison only: the diagnostics
  need about `1.1–1.5`.
  Framing check: a protocol-dependent detuning cannot replace the weight.
  On the bare derived wire (`s = 1`, `k = α/2`), `m₂/m₃ ≤ √(3/2) k = 0.00447`
  for every complex detuning, with the maximum at the cube roots
  (`tools/detuning_bound_check.py`, numerical). So the protocols must
  differ in the ratio of heavy to node coupling, as this item assumes.
  (Comparison only: at resonance up needs `s ≈ 0.7–1.2`, close to the bare
  wire, while electron and down need the heavy flip suppressed, `s ≈ 0.09`
  and `0.26`: a Toll on the heavy flip, largest for the electron.)
  The flip itself cannot supply it. In the glued register a wall step
  keeps the class and leaves the label untouched
  (`GluedRegister.wallStep_class`), and the crossing is one automorphism
  for every label (`crossing_walls`, `crossing_word_glued`). So the
  native wire operations give every protocol the same wire. A
  protocol-dependent heavy weight needs a gate that reads the label, and
  by `CoherentGate.unequal_needs_orthogonal` (stated for weak partners;
  the same overlap argument applies to other labels), overlapping wire
  outputs require orthogonal exported records.
  `HeavyFlipControl` gives a finite generation-addressed gate with
  a supplied sector and position record. `HeavyFlipRecords` excludes
  shared auxiliary-only hypercharge comparison schedules on a massive
  label as exact quark-position writers. The active slots have equal
  charge, so their common contribution bounds the auxiliary outcome gap
  by `½`. The full and lepton-only comparisons also leave electron
  and down with nonzero record overlap on either fixed wall. The paired
  flag budget has the charged ladder, with exact gap ratio
  `2/(3+√3) ≈ 0.423`, but fails as an exact record writer.
  The signed-axis predicates can write both bits exactly if their
  diagonal phase controls are supplied. With the reference-axis and
  negative-position flags and one required visit per bit the Tolls are
  `2, 1, 0, 1` for `e, d, u, ν`. The charged weights are ordered.
  Comparison only: the gap ratio is 1 versus about 1.1–1.5.
  Open: derive the native record couplings and preparation, the physical
  registration polarity and pricing, and the per-flip firing law. The
  direct address comes from the reference wall, so the coupling of any
  resulting Toll to the other wall also requires a derivation.
  First cadence tested: each sector reads its own doublet bit
  once per its static hypercharge period, at the half period. Leptons
  return at `π`, quarks at `3π`; over `3π` the lepton readouts are `π/2`
  and `5π/2` (both `d = ¼`) and `3π/2` (`d = 1`), and the quark readout is
  `3π/2`. If coinciding readouts merge (Economy), `n_L = 2`, `n_Q = 1`
  and `T_d = T_u`: no ladder. If they stay separate, `n_L = n_Q = 2` and
  the ratio `(T_d − T_u)/(T_e − T_d)` is `2/3`. (Comparison only: `2/3`
  is below every diagnostic value in `tools/heavy_toll_targets.py`, so
  this cadence is disfavoured either way.)
  The open
  substrate question is the schedule: which comparisons the wire's repair
  applies to each label, derived from that repair. Compare its weights
  with the recorded ladder only afterwards, in e8p. One structural
  consequence to keep in view: any Toll linear in the static hypercharge
  gives `(T_d − T_u)/(T_e − T_d) = 3/2` with no free parameter
  (comparison diagnostic: `tools/heavy_toll_targets.py`).

- **Lightest masses. [Premise]** For the charged states, derive a
  native law that admits and fires a charge-selective coherent flip.
  Derive its pulse area and whether the same real detuning is held by
  a stationary calibration channel shared across charged protocols.
  [Charged insertion](OVERVIEW.md#charged-insertion-on-the-static-wall)
  gives selectors and the exact lift for the candidate on the static
  vector-class leg. A protocol-blind pulse area with the selector's unit
  amplitude inserts the same `ε` for each charged protocol, so on the
  substrate the protocols differ only if the area or amplitude depends on
  the protocol. Under the derived conversion that is a protocol-dependent
  Toll, `ε ∝ exp(−T/2)`, from the same schedule as the heavy-label
  weight. (Comparison only: the offsets matched to recorded ratios differ
  by about `50×` across protocols.) Derive the physical placement and use the selected
  generator to determine the light-pair mass-basis rotations in
  [PMFlavor](../PMFlavor/REVIEW-AND-NEXT.md#open-work).
  Compare the candidate's singular values directly with the recorded mass
  ratios. The [uniform-to-local check](OVERVIEW.md#lifting-the-resonant-zero)
  gives the determinant conversion and its spectral limits.
  For neutrinos, derive native admission of the phase gates and coherent
  branch mixer in `PMAction.BranchGateBoundary`, and route the retained
  occupied branch onto the static light wall. Use the
  [vacancy preparation](OVERVIEW.md#static-vacancy-and-neutral-light-modes)
  as the candidate circuit for the vacancy-truncated model. For a Dirac
  mass, derive the native update that uses the reference scalar link to
  populate the static neutral partner. Derive neutral flips and crossings
  that split the masses. For diagonal flips, the
  [paired Schur block](OVERVIEW.md#equal-class-gapped-crossing) requires
  unequal magnitudes of the three reverse-cycle weights.

## Other open work

- **Radiative factor. [Certificate]** The substrate's own order-`α`
  correction is derived numerically from the diagrams
  (`tools/muon_radiative_derivation.py`): the conserved wall vertex
  (`PMAction.SpinorVertex`, `Z₁ = Z₂` on the substrate), continuum photon
  modes, the virtual vertex and both self-energies, and real emission at
  fixed neutrino-pair invariant, with explicit ultraviolet, infrared and
  collinear regulators. The total is independent of each regulator and
  reproduces the inclusive kernel pointwise (`z = 0.1 … 0.9`, to `10⁻⁴`
  relative at `m_e = 3·10⁻⁴`), so its integral is `π² − 25/4`
  (`tools/muon_radiative_certificate.py`). Remaining: formal verification
  in Lean. State the assembled kernel and the cancellation of the
  regulator logs (stage 2), then the Feynman-parameter integrals
  (stage 3). Until then `MuonLifetimeCorrected` keeps the factor as a
  certified input, and the higher-order terms (`MuonQEDLoops`) stay
  supplied.
