# PMElementaryParticles — open work

Done results are in [OVERVIEW](OVERVIEW.md). The wire (one light-mass form shared by every protocol)
is PMAction's; label changes are PMFlavor's.

## The protocol readout (first)

The derived wire and its readout are in OVERVIEW ("Protocol readout"): at the resonance `m₁ = 0` and
`m₂/m₃ = √(3/2) k` for every protocol (`k/K = α/2`, `PMAction.ReferenceNode`). Until the readout is
derived, e8p's masses are the `QuarkMasses`/`LeptonMasses` tier ledgers (declared; their e8p caveats
say so). The tier ladder (`TierLedger`) is the same question in the paper's form. Mixing is not a wire
effect (OVERVIEW); its source is PMFlavor's charged-current transfer readout.

- **Heavy-label weight.** Derive the heavy (label-`v`) state's upkeep per protocol,
  `s_e : s_d : s_u ≈ 1 : 3 : 13`. A charge-dependent upkeep `s ∝ e^{a Y_R}` (`Y_R = −2, −2/3, 4/3`)
  fits down and up with one `a ≈ 0.74–0.82` (OVERVIEW); derive the upkeep and `a` (the library has no
  such cost yet). If the neutrino shares the wire (its lightest mass then exactly zero, allowed by the
  data), its ratio `√(Δm²₂₁/Δm²₃₁) ≈ 0.17` needs `s_ν ≈ 0.030` against `s_e ≈ 0.087`, `s_d ≈ 0.26`,
  `s_u ≈ 1.14` (`k = α/2`): the order `ν < e < d < u` is not the order of `Y_R` or `Q` (which puts `ν`
  between `d` and `u`), so a toll linear in signed charge fails with the neutrino included. Steps
  `ν → e → d` are each a factor `≈ 3`; `d → u` is `≈ 4.4`.
- **Lightest masses.** The lightest state is exactly massless on the full wire at the resonance
  (`PMAction.ExactZeroMode`) for every weight, so `m_e`, `m_u`, `m_d` need a source outside the wire
  (the protocol register) or a reason the flip sits off the resonance. The offsets the data would need
  (OVERVIEW) follow no single law in the weight or charge.
- **Protocol register and coupling.** Which E8 structure carries protocol identity, and how a protocol
  couples to the wire. Read as a persistence system, the register is the protocol's Capacity and Map,
  and its requirements follow from the pillars: Capacity, `16` channels (`32` light components) per
  generation; Map, the label unchanged by wall terms; Protocol, the label carried by the same transport
  events as the particle; Governor, the label changed only by gauge and weak events; Toll, its upkeep,
  which is the heavy-label weight above; Margin, robustness to class phases. PMAction's constraints:
  colour is a separate factor, not the carrier axes (`PMAction.ColourRegister`); a factor can be built
  from disjoint banks (`PMAction.IndependentRegisters`). Excluded: the reference class's even sector as
  the label. It satisfies Map but not Protocol: the completed wall action vanishes on the even sector at
  every momentum (`PMAction.CarrierVacuumEvolution.even_inert`, `PMAction.EvenComplement`), so an even
  label does not move and is left behind by its particle. Remaining candidates: the occupation register
  of `PMConstants.CarrierRepresentation` (needs a transport that moves the occupied carrier with the
  Dirac amplitude), or a label carried by the transported unit itself (the two-wall carrier pair,
  `PMFlavor.OrientationDoublet`'s orientation as the doublet). The heavy-label weight, the partner
  difference and the lightest masses enter here.

  Second brainstorm (`tools/register_transport_check.py`; tests: count, `1 + 3`, doublet sign, Map,
  Protocol (moves with the particle), separate from the Dirac generators). Killed: the other wall's
  even modes (count `16`, does not move); the other wall's full carriers (its odd half is the wall); a
  displacement of the local reference record (not stationary); the hop's auxiliary root axis as the
  label (`2e_j = (e_j+e_k)+(e_j−e_k)` needs `k ≠ j`, so no fixed label serves every direction, and the
  in-slice hops never use the reference axis); the orientation doublet with no colour source (count).
  Survive: (i) the vector carriers (axis `×` sign, `8 × 4 = 32`) as an occupation register moved by the
  same shift as the particle, its E8 bank open; (ii) the E8 glued roots read as generation `×` protocol
  `×` wire: `240 = 48` pure `+ 192` glued, and each glue class's `64` glued roots are `8` carriers of one
  `D₄` (the protocol, changed only by that `D₄`'s roots: gauge) `⊗ 8` of the other (the wire, moved by
  its own roots). Three glue classes give three generations, and reading each class's protocol carriers
  in the vector frame by triality is `CarrierRepresentation`'s premise. (ii) supplies (i)'s bank, but it
  uses the two `D₄` factors as protocol and wire, while the library uses them as the two walls
  (`PMAction.CarrierVacuumSector`); with one `D₄` for the wire, a class gives `8 × 2 = 16` light
  components. The decisive question for (ii): where the two walls live if both `D₄` factors are taken. Tried: the
  walls as the two chiral halves of the wire's odd sector (killed: `4` components, no gapped partners,
  so the two-wall mass mechanism is lost); the walls as the generation's two glue classes, the particle a
  superposition of glued roots of class `b` (one wall) and `c` (the other) (count `8 × 2 × 2 = 32`,
  three unordered class pairs give three generations as in `PMAction.GenerationWalls`, and both walls'
  protocol carriers read in the vector frame by triality is `CarrierRepresentation`'s "both domain-wall
  sectors" premise; open: a single-wall shift changes a wall's class, so the walls need a label besides
  their class).

## Other open work

- **Final channels.** `PMAction.NativeExternal` makes `AmplitudeTrace`'s spinors the native wall
  eigenmodes and its bilinears the native charged current. Identify which protocol channels are the
  final states of each decay (and so the first row's external states).
- **Radiative factor.** `MuonLifetimeCorrected` supplies the one-loop QED factor; derive it as the soft
  photon dressing of the charged daughter.
- **First-row deficit as leakage** (`0.0016 ± 0.0007`). `PMAction.WallCurrentWeights`: the full
  charged projector keeps a gapped component, so total gapped weight is not a row deficit; the row
  needs the external-state and final-channel readout (Final channels above).
  `PMAction.WallGapCalibration`: the library admits every flip-to-gap ratio, so the size waits on the
  absolute event clock (PMAction REVIEW, extensions).
