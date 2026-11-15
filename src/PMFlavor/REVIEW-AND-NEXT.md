# PMFlavor — open work

Closed results and retired routes are in [OVERVIEW](OVERVIEW.md); what flavour is here and the terms
(wire, label state, protocol, event, `J`, `U`) are in [README](README.md).

**Purpose and rule.** PMFlavor finds `J`, the label-change amplitudes of one charged-current event,
for carriers off and on the reference axis. The observed matrices are `U_uᴴ J U_d`; `U` belongs to the
wire (PMAction) and the protocols (PMElementaryParticles). Every number comes from E8 structure or a
narrowly stated premise; data are only the final test (e8p). Do not fit integers or parameters to
data, and do not frame work as fitting Standard Model sectors.

**Status of each entry of `J`** (e8p readout names in brackets).

| Label change | Off the axis | On the axis |
|---|---|---|
| class `0`, `2 → 1`, in-cycle | `π/14` [`s₁₂`]: share candidate (`HalfTurnAperture`), readout rule derived (`ConductionRule`) | the same rule gives `π/10`; e8p prints `1/(2φ) = sin(π/10)` [`sin²θ₁₂`] (decision pending) |
| class `2`, `1 → 0`, node, reference wall | no derived amplitude; the library's rules are excluded (`TransferAmplitude`) [`\|V_cb\|`, printed `(π+χ)/(α⁻¹−Dπ)`] | no construction [`sin²θ₂₃`, printed `(1+π/(ν+σ))/χ`] |
| class `1`, `0 → 2`, node, other wall | `1/(2α⁻¹+π)`: two-leg series path derived; boundary `π` a premise [`s₁₃`] | `3/α⁻¹`: one leg into three outlets, candidate (`ReactorConductance`) [`sin²θ₁₃`] |
| phase | none in the library [`δ = arctan(σ/χ)` printed] | derived from the angles (`ReferenceFlavour`) [`δ_PMNS`] |
| loss | `q² = 515/516`, derived under one premise (`DressingEvent`) | — |

## Plan

1. **`J` as the event operator** (`EventTransfer`). Done: `J κ` with the three changes at the
   classes `GenerationCurrent` fixes, one direction per event; the actual weak refresh
   (`CarrierActions.weak`) moves only vector-class carriers of the reference's sector
   (`refresh_moves_reference`, `refresh_fixes_other`), so it supplies the in-cycle entry and the node
   entries need the node; the completion `A = N − Nᴴ` is skew-Hermitian, carries `κ` forward and `−κ̄`
   in reverse, and `1 + A` is unitary to second order (`first_order_unitary`). Second order
   (`second_order_unitary`, `corner_split`): unitarity forces the Hermitian part `A²/2`; exponential,
   Cayley and polar all have it and first differ at third order (`A³` coefficient `1/6`, `1/4`, `1/2`;
   about `κ₀³/12 ≈ 1·10⁻³` on the in-cycle entry, near the `|V_us|` error). Open: the
   free skew part, the order of the changes inside one event. It splits the two-step product `κ̄₀κ̄₂`
   between the class-`1` entry and its reverse as `w, 1 − w̄` (`corner_split`): `w = ½` for any power
   series in `A` (exponential, Cayley, `TransferGenerator`); `w = 0` for premise FC, forward
   composition (`forward_completion`, `forward_two_step`, `forward_corner`: the second-order term is
   two forward changes of the same event plus the Hermitian depletion, no reverse-reverse route);
   `w = 1` the reverse order. FC reads `reverse_zero` as a statement about all routes inside an
   event; derive that from the refresh (it acts on one wall, one way round the cycle) or keep FC as
   the named premise.
   **Test (recorded).** With `κ₁ = TransferAmplitude.jump = 0.003606` and `U = 1` (item 6), Stewart's
   relation on the two corners (real `w`) gives `|κ₁|² = (1 − w)|V_ub|² + w|V_td|² − w(1 − w)|V_us V_cb|²`.
   PDG (`|V_ub| = 3.82 ± 0.20`, `|V_td| = 8.6 ± 0.2` ×10⁻³, `|V_us| = 0.2243 ± 0.0008`,
   `|V_cb| = 0.0408 ± 0.0014`): `w = 0` needs `0.00382 ± 0.00020` (1.1σ, survives); `w = ½` needs
   `0.00483 ± 0.00025` (4.9σ, excluded together with the jump); `w = 1` needs `0.00860` (25σ,
   excluded). So the jump and any power-series completion cannot both hold. This excludes pairs;
   it does not derive FC.
2. **The amplitude of each entry.**
   - In-cycle: the share `π/N` rests on the aperture premises (`HalfTurnAperture`); derive them or
     state them as the one premise of this entry.
   - Other-wall node change: the series path is derived; derive the boundary `π`.
   - Reference-wall node change: the library's rules give `1`, `≈ 1.98`, `≈ 23.7` times the other-wall
     change; the readout needs about `10`. Derive what the reference's wall changes in the amplitude
     (the refresh acts on that wall). `VcbEnvelope`'s `env 1 / env (Δ − D)` reaches the value but has no
     schedule basis: exhibit the schedule or retire the form.
3. **One readout rule on the axis (decision pending).** `ConductionRule`: with the node readout and no
   further function, the on-axis in-cycle change gives probability `π/10`; e8p prints `1/(2φ)`. Switch
   e8p to `π/10` (changes `PMNS.lean`, `PMNSIntervals`, `FlavourInvariants`, e8p pulls and catalog), or
   derive the sine. Falsification: JUNO's full precision separates the two.
4. **Label changes on the axis.** The reference-wall node change reads as `sin²θ₂₃ ≈ 0.5` (large); the
   other-wall one as `3α` (small). `TransferGraph.inCycle_iff` is derived from displacements of
   off-axis states; re-derive the in-cycle / node split for states on axis `0`. `Theta23Wall`: a wall
   factor common to both readouts cancels, so this change needs an asymmetric factor.
5. **Phases.** No source in the library (OVERVIEW, "Where a CP phase can sit"); a sourceless holonomy
   is flat (`FlatPersistence`). `J` is one-directional per event (`EventTransfer.reverse_zero`); ask
   whether the event's orientation (`GenerationWeak.relative_orientation`) gives a phase other than
   `0` or `π`. State any premise narrowly; test it by the triangle angle and `J` it predicts.
   The only rephasing invariant of `J` is the cycle product `κ₀κ₁κ₂` (`EventTransfer.cycle_invariant`):
   the phase to find is the holonomy `Φ` of the directed 3-cycle. Under FC and `U = 1`, `fc_corner` and
   the PDG sizes (as in item 1) need `Φ = 70 ± 5°`; a flat holonomy gives `|V_td| = 0.0053` or `0.0130`
   against `0.0086 ± 0.0002`, excluded (recorded). So with FC either the cycle carries a non-flat
   holonomy or `U ≠ 1` supplies the phase (item 6).
   E8 candidates for a phase, and their status (all from structure already in the library):
   - `0` or `π`: glue arithmetic (the three classes are a neutral triple,
     `PMSubstrate.E8Invariants.neutral_distinct_classes`, so the cycle carries no net glue) and the
     refresh's spinor lift (`CPQuarterTurn.two_plane_lift_sq`, `±1`). Flat: excluded under FC, `U = 1`.
   - `π/2`: a single-plane half-turn lifts to a quarter turn (`plane_lift_sq`); the refresh is not one
     (`CPQuarterTurn`). Not supplied; also `4σ` from `70 ± 5°`.
   - `2π/3`: the triality rotation of the three classes (`ChannelSymmetry.class_to_vector`); no
     mechanism in the library gives the event its character. Not supplied; `10σ` from `70 ± 5°`.
   - The zero-energy node phase: real denominator (`TickPlacement.node_denominator_real`). Closed.
   - A wall-side leg phase (`LinkFlux.flux_cyclic`, flux `ū⁶`): open, size not fixed.
   With everything real (`κ`, `U_u`, `U_d`), the observed matrix is real and has no CP violation, so
   one of these must be complex. The tests above assume `U = 1`; item 6 decides how far they hold.
6. **The size of `U`.** Needs the other wall's detuning `δ_O` (PMAction REVIEW) and which protocol uses
   which carriers (PMElementaryParticles). With `δ_O` dominant the rotation is small; bound it.
   `PMAction.ReferenceWallRotation`: on the reference's wall (the event's wall) the rotation between
   label states `i`, `j` is about `|dᵢ/dⱼ| · |κ_O/δ_O|`, the mass ratio times the other wall's
   carrier-to-detuning ratio, whatever `δ_O` is; no suppression for comparable `|dᵢ|`. Open: that the
   event reads the reference-wall side (premise), and the sizes per protocol (EP). Then redo the item 1
   and item 5 tests with this `U`.
7. **Dressing outlets.** `DressingEvent.event_law_spatial` works on axis labels only. Open: whether the
   event's loss realizes that law and the row-to-outlet identification; the on-axis node change's three
   outlets (`ReactorConductance`) and the dressing's three (`DressingChannels`) should be one count.
8. **`TransferGenerator`** (zero-energy scattering `S(K)`): keep as a candidate amplitude rule for `J`'s
   node entries or retire; its equal-lead-width premise is not derived. As a completion it is a power
   series in one generator, so it is the `w = ½` case of item 1.

## Transfer selection

- **Conditional on `e^{−iHt}`.** `ReferenceSelection`, `RelativeFrameCost`, `TransferWorkLaw`,
  `TransferAmount`, `SpectralGapOrder` and `ChordBranch` run on `PMAction.FlavourEvolution`; they become
  unconditional when PMAction shows the substrate update acts on wall modes as `e^{−iHt}`.

## Cleanup

- Rename `FlavourPulls` (now only `weak_mixing_shared`) and `FlavourPostulates` (defines `φ`, `pi_b`,
  `sqrt5_b` in the `FlavourPulls` namespace), and the `Flavour…` transfer-selection modules. Replace
  "generation" by "label state" in docstrings as they are touched. `TransferGraph.mode`: rename to the
  in-cycle / reference-wall / other-wall changes, keeping conduction / promotion / jump as the candidate
  reading.

Working notes: there is no Lean toolchain in the device shell; ask Kate for `./build.sh fast
PMFlavor.X`. Avoid `simp` on a transposed matrix literal or a product of three literals; name the
intermediate literal and use `rfl` (`LinkKronComparison.Lcg_eq_transpose`). Numerical scans belong
outside Lean and are labelled external. When editing these files by slicing between two anchors, check
that nothing between them is lost.
