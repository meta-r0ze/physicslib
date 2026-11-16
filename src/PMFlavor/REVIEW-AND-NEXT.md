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
| class `0`, `2 → 1`, in-cycle | `π/14` [`s₁₂`]: share candidate (`HalfTurnAperture`), readout rule derived (`ConductionRule`); **no source:** the refresh keeps the label (item 0) | the same rule gives `π/10`; e8p prints `1/(2φ) = sin(π/10)` [`sin²θ₁₂`] (decision pending) |
| class `2`, `1 → 0`, node, reference wall | no derived amplitude; the library's rules are excluded (`TransferAmplitude`) [`\|V_cb\|`, printed `(π+χ)/(α⁻¹−Dπ)`] | no construction [`sin²θ₂₃`, printed `(1+π/(ν+σ))/χ`] |
| class `1`, `0 → 2`, node, other wall | `1/(2α⁻¹+π)`: two-leg series path derived; boundary `π` a premise [`s₁₃`] | `3/α⁻¹`: one leg into three outlets, candidate (`ReactorConductance`) [`sin²θ₁₃`] |
| phase | none in the library [`δ = arctan(σ/χ)` printed] | derived from the angles (`ReferenceFlavour`) [`δ_PMNS`] |
| loss | `q² = 515/516`, derived under one premise (`DressingEvent`) | — |

## The chain behind each value in `Values` (2026-11-16)

What e8p prints is `PMFlavor.Values`. Each number's derivation status, so a comparison is read with
its chain in view (`CKM` docstring: the four CKM forms are supplied model formulas whose numerals are
derived invariants, `FlavourInvariants`):

| Value | Formula | Status | Where |
|---|---|---|---|
| `s₁₂` (`cabibbo`, `vus`) | `π/(ν−χ) = π/14` | share candidate; aperture premises; readout rule derived. No event source for the in-cycle change (`RefreshLabel`) | `HalfTurnAperture`, `ConductionRule` |
| `s₁₃` (`vub`) | `1/(χα⁻¹+π)` | two-leg series path derived; boundary `π` a premise; names consistent with the wire (`PMAction.WireMass`) | `VubSeriesPath`, `TransferAmplitude.jump` |
| `\|V_cb\|` | `(π+χ)/(α⁻¹−Dπ)` | supplied; no derived amplitude (library rules excluded) | `CKM`, `VcbEnvelope` (unbased) |
| `δ` | `arctan(σ/χ)` | supplied; no phase source in the library (item 5) | `CKM`, `CPPhases` |
| `A`, `ρ̄`, `η̄`, `J`, `sin 2β`, `γ` | from the four above | exact consequences (barred `ρ̄`, `η̄`: `WolfensteinBar.zbar_eq`) | `Wolfenstein`, `WolfensteinBar`, `TriangleAngles`, `TriangleGamma` |
| `q² = 515/516` | dressing | derived under one premise | `DressingEvent` |
| `sin²θ₁₂` | `1/(2φ)` | on-axis rule gives `π/10`; decision pending (item 3) | `PMNS`, `ConductionRule` |
| `sin²θ₂₃` | `(1+π/21)/2` | no construction (item 4) | `PMNS` |
| `sin²θ₁₃` | `3/α⁻¹` | candidate: one leg into three outlets | `ReactorConductance` |

So the close CKM numbers rest on two derived paths (`s₁₃`, the consequences) and on supplied forms
(`|V_cb|`, `δ`) and candidates (`s₁₂`, PMNS). The wire (PMAction) does not yet produce them: with the
derived carrier placement its singular values fail the up and lepton mass ratios for every `δ_O` and
cycle phase (PMElementaryParticles REVIEW, "Protocol readout"). Presenting the numbers needs this table
next to them.

## Plan

0. **The in-cycle entry, and the generation names (2026-11-16).**
   - *No source in the event.* `RefreshLabel.refresh_keeps_label`: the weak refresh is the doublet
     exchange and keeps the label, so it does not make the class-`0` change. `J κ` keeps `κ₀` free.
   - *Names.* The other wall's carriers in the mass are placed by glue arithmetic on single-wall modes
     (`PMAction.WireMass.single_wall_class`). With that placement the wire's masses give label `2` the
     lightest, `1` the middle, `0` the heavy: `TransferGraph`'s naming, so `Values.vub = s₁₃` (the jump)
     and e8p stand. (A brief detour, 2026-11-16, read the reverse names from the withdrawn
     `GenerationCurrent` placement; `GenerationNames` is retired.)
   - *What the derived placement gives the CKM is open.* The vector carrier now joins the heavy label to
     label `1`, so `U` has heavy–light rotations (`0.14` for down at its light ratio) and no GST 1–2
     rotation. Whether the wire's stated inputs are forced by persistence comes first (PMAction
     REVIEW); the CKM numerics wait for that.
1. **`J` as the event operator** (`EventTransfer`). Done: `J κ` with the three changes at the
   classes `GenerationCurrent` fixes, one direction per event; the actual weak refresh
   (`CarrierActions.weak`) moves only vector-class carriers of the reference's sector
   (`refresh_moves_reference`, `refresh_fixes_other`) by their sign: it keeps the label
   (`RefreshLabel`), so neither the in-cycle entry nor the node entries come from it; the completion `A = N − Nᴴ` is skew-Hermitian, carries `κ` forward and `−κ̄`
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
   it does not derive FC. Valid only for `ε = |κ_O/δ_O| ≲ 0.04` (item 6).
2. **The amplitude of each entry.**
   - In-cycle: the share `π/N` rests on the aperture premises (`HalfTurnAperture`); derive them or
     state them as the one premise of this entry.
   - Other-wall node change: the series path is derived; derive the boundary `π`.
   - Reference-wall node change. With the corrected bookkeeping `U`'s 2–3 rotations are `≲ 4·10⁻⁴`
     ("Redone" below), so `|V_cb|` is this entry and it needs `≈ 10.7×` the other-wall change
     (`|V_cb|/|V_ub|`); `CandidateTests.promo_rules_excluded` stands. (A short-lived reprieve for
     Closure's ratio `1` with a 2–3 rotation `≈ 0.03` rested on the old bookkeeping; withdrawn.)
     No derived amplitude; `VcbEnvelope` stays unbased.
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
   holonomy or `U ≠ 1` supplies the phase (item 6; `U ≈ 1` needs `ε ≲ 0.04`).
   **Per-protocol cycle phase (2026-11, corrected wire, numerical).** A common label-cycle phase `Φ`
   for up and down gives `|V_us| = θ_d − θ_u = 0.178`; a relative `Φ_d − Φ_u = ±90°` gives `0.2218` (checked 2026-11 with normalized left singular
   vectors of the full 3×3 wire: `0.2219`; the quarter turn may sit on label 1 or 2, not 0)
   (data `0.2243`). So the Cabibbo combination asks for a quarter turn between the two protocols'
   cycle phases (compare `CPQuarterTurn`). Candidate source: a phase proportional to the right-handed
   hypercharge on the other wall's carriers, `Φ_p = 3 Y_R θ₀`, gives `Φ_u − Φ_d = 6θ₀` (`Y_R`: `4/3`,
   `−2/3`); `θ₀ = 15°` for the quarter turn. Prediction with no further number: leptons have the same
   `Y_R` difference (`ν` `0`, `e` `−2`), so `Φ_ν − Φ_e` is also `90°`. Open: a source for `θ₀` (the
   hypercharge holonomy needs one, `PMAction.FlatPersistence`), and the neutrino-side `U` to test it.
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
   carrier-to-detuning ratio, whatever `δ_O` is; no suppression for comparable `|dᵢ|`. The event reads
   that side (`ReferenceWallRotation`: rows of the light mass are the reference's wall, the wall
   `(1 − Γ)/2` selects). Open: the sizes per protocol (EP).
   **How far the item 1 and 5 tests hold (numerical, outside Lean).** With `ε = |κ_O/δ_O|` and the
   label states' mass ratios as `|dᵢ/dⱼ|` (protocol data, EP), the first-order corrections to the two
   corners are about `κ₀ · (m₂/m₃)_d · ε ≈ 0.005 ε` (class-`1` corner, through the down-type 2–3 rotation)
   and `κ₂ · (m₁/m₂)_d · ε ≈ 0.002 ε` (its reverse); the up-type rotations add `< 0.001 ε`. Against
   `|V_ub|`'s error `0.0002`, the tests are tests only for `ε ≲ 0.04`. So: either the other wall is
   strongly detuned (`|δ_O| ≳ 25 |κ_O|`), or `U` is part of the corner values and the FC and phase
   conclusions are open. This makes `ε` the next number to derive (PMAction, `δ_O`). PMAction's REVIEW (`δ_O` item) adds: in the library's
   normalization `ε = r/(2|δ_O|)` in hop units, `U = 1` needs a crossing link `|y| ≫ 12`, and with the
   symmetric light amplitudes the light block of `U` is near `45°` at large `δ_O`; the wire itself
   splits the light pair when `δ_O` is a few spinor flips, but there `U ≠ 1` (heavy–light `O(0.1–1)`;
   PMAction REVIEW, corrected). So the item 1 and 5 tests are conditional on both. On the full two-wall Hamiltonian
   (PMAction REVIEW) `U ≈ 1` needs the other wall's detuning near the hop scale, which moves the heavy
   label off its walls unless the vector carrier's rate is small.
   **Corrected bookkeeping (2026-11):** the heavy–light rotations are `≲ 4·10⁻⁴`, which meets the
   `ε ≲ 0.04` condition; so the item 1 and 5 tests hold for the 2–3 and 1–3 parts of `U`. The 1–2 part
   is not small (`√(m₁/m₂)`), see item 0. (The earlier exclusion of a common `U` at every `δ_O` and the
   `45°` light block used the old assignment; withdrawn.)
7. **Dressing outlets.** `DressingEvent.event_law_spatial` works on axis labels only. Open: whether the
   event's loss realizes that law and the row-to-outlet identification; the on-axis node change's three
   outlets (`ReactorConductance`) and the dressing's three (`DressingChannels`) should be one count.
8. **`TransferGenerator`** (zero-energy scattering `S(K)`): keep as a candidate amplitude rule for `J`'s
   node entries or retire; its equal-lead-width premise is not derived. As a completion it is a power
   series in one generator, so it is the `w = ½` case of item 1.

## Audit: which conclusions assumed `U = 1` (2026-11, updated 2026-11-16)

*The update below used the withdrawn placement; with the derived one, `U`'s heavy–light rotations are
not small and this audit is open again (item 0).*

An audit with free 2–3 rotations (`θ_u ≈ −0.034`) found the data no longer selected FC, Closure's ratio
`1` survived and `θ₂₃` could come from `U`. That rested on the old bookkeeping. On the corrected wire
`U` is block-diagonal to `4·10⁻⁴`: the `U = 1` conclusions of items 1, 2, 5 stand for the 2–3 and 1–3
entries, and the 1–2 entry is `U`'s (item 0). Item 3 (PMNS readout) keeps the caveat for the lepton
`U`s; for item 4 the light block reaches `45°` only as `δ → ∞` (`δ(1 − t²) = t`).

## What the data say about `U` (empirical relations among measured values, 2026-11)

Used as targets for structure, not as fits. Quark ratios from FLAG (scale-free within QCD).

1. **Mixing tracks mass ratios.** CKM angles are small and hierarchical where quark masses are
   strongly hierarchical; PMNS angles are large where neutrino masses are mildly hierarchical
   (`m₂/m₃ ≳ 0.17` from `Δm²₂₁/Δm²₃₁ ≈ 0.03`). This is the signature of mixing dominated by persistence
   rotations whose size is set by mass ratios: supports the `U`-first reading above. The wire's own
   near-degenerate pair rotating by `45°` is the same pattern at the degenerate end.
2. **Cabibbo from the down masses.** `|V_us| = 0.2243 ± 0.0008` and `√(m_d/m_s) = 0.2239` (`m_s/m_d ≈ 19.95`):
   equal within `0.5σ`; also `|V_td/V_ts| ≈ 0.21` against `0.224` (about `2σ`). The 1–2 mixing behaves like
   a down-protocol rotation of size `√(m_d/m_s)`: a light block `[[0, √(m_d m_s)], [√(m_d m_s), m_s]]`
   (a zero in the lightest diagonal entry). Rotations of size `√(mass ratio)` come from the
   vector carrier on the light pair in the linear (coherent) reading (`PMAction.LightPairTexture`;
   the squared reading `WallOffset` breaks it). Open tension:
   PMFlavor's in-cycle entry `κ₀ = π/N` also lands on `0.224`; both cannot add fully. Either they are
   the same object seen twice (the in-cycle change is the down protocol's 1–2 rotation), or one is
   small. Deciding this is a sharp test of the reading.
3. **The 2–3 mixing is below the square-root rule.** `|V_cb| = 0.041` against `√(m_s/m_b) ≈ 0.15` and
   `√(m_c/m_t) ≈ 0.087`; `|V_ub/V_cb| ≈ 0.093` against `√(m_u/m_c) ≈ 0.045`. So the 2–3 block is not a
   texture zero of the same kind; the fit with Closure's node changes wants `≈ 0.034` mostly in the up
   protocol, about `0.4 √(m_c/m_t)`.
4. **CP.** Jarlskog `≈ 3.1·10⁻⁵`; triangle angle `α ≈ 90°` (`CPQuarterTurn`), `γ ≈ 66°`; the label-cycle
   phase at the best fits is `70–80°`.
5. **Leptons.** No charged-lepton square-root relation appears (`√(m_e/m_μ) = 0.07`,
   `√(m_μ/m_τ) = 0.24` against PMNS sines `0.15, 0.55, 0.75`); the large angles point to the neutrino
   protocol's near-degenerate states.

**Withdrawn placement (2026-11-16), kept as history:** **Found (2026-11):** with the other wall's vector carrier on the light pair, as `GenerationCurrent`
and `GenerationWeak` require (PMAction REVIEW, bookkeeping item), relation 2 follows exactly at
leading order: `PMAction.LightPairTexture` gives `tan θ₁₂ = √(m₁/m₂)` per protocol. Numerically,
fixing `δ_O` by `m_d/m_s` (with `k/K = α/2`) gives `m_s/m_b = 0.0163` against `0.0185`. The tension
with `κ₀` stands: the same vector carrier makes the in-cycle label change in `J` and the 1–2 rotation
in `U_d`; counting both doubles `|V_us|`. Next: decide whether `J`'s in-cycle entry is the event-level
view of the same carrier (then `U` carries it and `J`'s in-cycle entry is not added), and redo the
item 1, 2, 5 numerics with the corrected `U`.

**Redone with the corrected bookkeeping (2026-11, numerical, `k/K = α/2`; that placement is withdrawn, item 0).**
- Per protocol, fixing `δ_O` by the lightest ratio: down `u = δ_O/k_f = 64.6`, `sin θ₁₂ = 0.218`
  (`tan θ₁₂ = t = 0.224`, the GST value; earlier drafts labelled the sine as the tangent), predicted `m_s/m_b = 0.0163` (data `0.0185`); charged leptons `u = 18.8`,
  `sin θ₁₂ = 0.068` (`0.0695`), predicted `m_μ/m_τ = 0.053` (data `0.0595`); up `u = 11.2`,
  `sin θ₁₂ = 0.041` (`0.045`), predicted `m_c/m_t = 0.089` (data `0.0074`, off by `12×`; at one scale `0.0037`, off by `23×`; see the
  EP REVIEW for the candidate that up's heavy label is undetuned, giving `0.98×`). Down and
  leptons land within about `10%` on their second ratio with no further number; up does not.
- The heavy–light (2–3) rotations are `≲ 4·10⁻⁴`: `|V_cb|` cannot come from `U`, so it is `J`'s
  reference-wall node change after all, and the `×10.7` of item 2 returns (the `U = 1` audit's
  reprieve for Closure's ratio `1` rested on the old bookkeeping).
- A common `U` (same for up and down) leaves `|V_us| = κ₀` exactly and gives `|V_ub|` contamination
  `0.0008` (`u = 30`) to `0.009` (`u = 100`): no longer excluded at every `δ_O`.
- Double count, checked with the per-protocol `U_u` (`u = 11.2`), `U_d` (`u = 64.6`), real: without
  `κ₀`, `|V_us| = θ_d − θ_u = 0.178` (`χ² ≈ 3300`); with `κ₀ = π/14` and a free phase, best `0.240`
  (`χ² ≈ 370`). GST's `|V_us| ≈ √(θ_d² + θ_u²) = 0.222` needs a relative phase near `90°` between the
  two protocols' 1–2 rotations, i.e. complex `U`: the label-cycle phase `Φ` per protocol
  (`PMAction.ReferenceWallRotation.det_M`; it leaves `|U|` unchanged but sets these phases). So: no
  separate `κ₀` in `J` (the in-cycle change is `U`'s), and a per-protocol cycle phase, is the reading
  the data point to; it is a candidate until `Φ` per protocol is derived.

Checked and dropped: a texture from letting `δ_O` act only on the vector-class label (spinor carriers
never cross under `β`, `PMAction.NativeDetuning.beta_crossings`) decouples the light pair entirely
(no 1–2 rotation), so it does not give relation 2.

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
