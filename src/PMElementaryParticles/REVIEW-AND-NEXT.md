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
  label does not move and is left behind by its particle.

  Candidate reading (OVERVIEW, "Protocol register"; `GluedRegister`): each wall is a glue class read
  through one `D₄` factor, amplitude in that factor and the protocol label in the other. It passes
  capacity, Map, Protocol, doublet and a native crossing, and its gauge orbits are the four base
  protocols. Open on it: (1) the Toll: the wire and the crossing are label-blind, so the heavy-label
  weight has to be a cost on the four orbits; the data ask for `ν < e < d < u` with steps `≈ 3, 3, 4.4`,
  which no product of a lepton/colour factor and a sign factor gives (it forces `s_d/s_u = s_e/s_ν`).
  Narrowed (`tools/toll_forms_check.py`): colour leaves two linear invariants on the label (`x₀` and
  `x₁ + x₂ + x₃`, in the vector or a spinor frame), and no monotone function of any combination of them
  gives the order (`0` of `3600` directions), because weak partners are antipodes and the order needs
  the sign to favour `ν` over `e` but `d` over `u`. Sign-blind (even) invariants tie the partners. So
  the Toll needs an odd part whose sign reverses between lepton and colour labels, plus an even
  lepton/colour part: an odd `×` even coupling, which a single label reading does not supply (a fit
  with `x₀`, `S`, `S²` takes four numbers for four). The crossing adds no label holonomy (triality
  cubes to the identity). Hint, not a result: in effective node coupling, `k_eff/(α/2) = (m₂/m₃)/(√(3/2)
  α/2)` is `0.81–0.94` for up, `4.3–4.9` for down, `13` for the electron and `38` for the neutrino:
  the up protocol sits at the bare wire, and the others need more amplitude through the node. Node
  admittances cannot supply that (`PMAction.ReferenceNodeBoundary`: a load only lowers the coupling
  below `α/2`), so the per-protocol factor is a weight on the heavy label, not a node effect. Shape of
  the targets: `s_u : s_d : s_e : s_ν` is a geometric ladder, step ratio `3.2–3.4` across the quark-mass
  ranges, `rms` log residual `0.07–0.16` (`α^{−1/4} = 3.42` and `3` both fit; the data do not separate
  them). The ladder index `0, 1, 2, 3` for `u, d, e, ν` is the reflected-binary reading of the two
  label bits (lepton, down): an odd `×` even form, as the exclusions above require. Wanted: a mechanism
  that charges one equal step per rung (a chain `u –weak– d –axis– e –weak– ν` with no `u–ν` edge).
  Candidate (vector frame, colour `i`): the weak flip is the antipode, and a shift by the root
  `r = eᵢ − e₀` maps `d → e` and `ν → u` and nothing else to a label. The four labels then form one
  directed cycle `u → d → e → ν → u` (weak, `+r`, weak, `+r`), and the ladder index is the number of
  events from `u` along it. Choices this leaves open, each to be derived or the candidate dropped: why
  the shift runs `+r` only (an orientation), why `u` is the base (it sits at the bare wire), and the
  cost per event (`3.2–3.4`). Tested and not supported: taking the lepton (reference) axis as the
  clock axis, forward root events (`PMAction.SliceHop`) give an orientation, but with every root
  allowed `d` reaches `u` through another colour and `e` reaches `u` in one forward event, so the chain
  collapses (`tools/toll_forms_check.py` 7); the cycle needs one root per colour, which nothing
  selects. Sector-response counts (`PMConstants.ReferenceEconomy.servedCount`) tie `u` and `d`, as any
  even quantity must. Readout check (`tools/readout_placement_check.py`): the ladder is not an artifact of putting
  the weight on both walls. On the reference wall only the weights are `0.026, 0.075, 0.22, 1.2`, the
  same shape; the weight on the other wall only, or a scaled detuning, reaches `u` alone and is
  excluded; scaling the node amplitude is excluded above; breaking the other wall's class-blindness in
  one cycle leg lifts the lightest mass (`m₁/m₃ ≈ 2·10⁻³`) but not to the data (`e` `2.9·10⁻⁴`, `u`
  `1.3·10⁻⁵`). The ladder is in the data: `m₂/m₃` for `ν, e, d, u` step by `2.9, 3.0, 5.3`, and the
  readout passes it through. So the Toll question is placement-independent: why those `m₂/m₃`.
  (2) the lightest masses. Killed on the way (git history has the details):
  the reference class's even sector, the other wall's even modes or full carriers, a displaced
  reference record, the hop's auxiliary axis, the orientation doublet alone, the walls as the wire's
  chiral halves, the walls labelled by class alone, and the even half of the other factor as the label
  (no doublet).

## Other open work

- **Radiative factor.** `MuonLifetimeCorrected` supplies the one-loop QED factor; derive it as the soft
  photon dressing of the charged daughter.
- **First-row deficit as leakage** (`0.0016 ± 0.0007`). `PMAction.WallCurrentWeights`: the full
  charged projector keeps a gapped component, so total gapped weight is not a row deficit. The final
  labels are now fixed (`FinalChannels`); what the row still needs is which wire mode of the daughter
  label is external: the charged current's image on the light eigenmodes against its image on the
  gapped ones (`ExternalStates.persistent_on_shell` makes only persisting eigenmodes external).
  `PMAction.WallGapCalibration`: the library admits every flip-to-gap ratio, so the size waits on the
  absolute event clock (PMAction REVIEW, extensions).
