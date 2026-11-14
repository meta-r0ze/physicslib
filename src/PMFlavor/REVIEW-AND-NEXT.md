# PMFlavor — open work

Status of the mixing forms (derivations in OVERVIEW, "Where the mixing comes from"): `|V_ub|` is
derived (`VubSeriesPath`, `KronSeries`); the reactor `sin²θ₁₃ = 3α` is constructed
(`ReactorConductance`); the CKM dressing `515/516` is derived (`DressingEvent`,
`DressingInheritance`). What remains:

Shared frame for all items (`LinkKronComparison`): flavour lives on the generation–class incidence
graph, three generation vertices and three class vertices, two legs per class. The quark mixings
are Kron reductions of it (per-class node crossings). The eigenvector link `B Bᵀ` is retired for
quarks (`LinkKronComparison`) and leptons (`LinkHierarchy`), so every remaining item is to be solved
on the network. Suggested order: the leg phases, then `|V_cb|`, then the aperture, then `θ₂₃`. Each
"Suggested attack" below is a candidate route with its test, not a result.

* **The in-cycle mixings** (`HalfTurnMixing`, `HalfTurnAperture`, candidate): `s₁₂ = π/14` and
  `sin²θ₁₂ = π/10`. Derived: the channel counts, `π` as Barbier's half-turn measure, the equal share
  (Closure's label-blind pricing, `equal_share_from_closure`, which assumes invariance under every
  permutation; the physical type-preserving symmetries keep the vector and spinor channels in
  separate orbits, so the equality across orbits rests on label-blindness, not symmetry), the
  amplitude/probability rule (`KronSeries`, Landauer). Remaining premise: the
  transfer crosses the refresh through its half-turn of directions (aperture) rather than along it.
  Test: split the half-turn into two arcs with fixed generation terminals; an aperture adds them in
  parallel, a length in series. This needs the directional contributions to be separately
  addressable, which the endpoint map `v ↦ −v` (`WeakUniform`) alone does not supply.
  `π/10` differs from the draft's `1/(2φ)` by `0.005`; JUNO's full precision resolves it.
  Suggested attack:
  * Put the in-cycle pair on the incidence network. The vector class vertex has two legs like the
    others, so the convention that gave `|V_ub|` (mixing amplitude = Kron-reduced coupling,
    `two_leg_from_incidence`) gives `s₁₂ = g_v/2` for a vector leg `g_v`. Check whether
    `HalfTurnMixing`'s equal share is this `g_v/2` with no extra factor. If the `2` has to be put
    in or taken out by hand, either the aperture reading or the amplitude convention is wrong, and
    `|V_ub|` (data-fixed `m = 2`) says which.
  * The separately addressable directions the parallel/series test needs may be the `6`
    axis-free vector displacements (`ExchangeAxis.vector_free`): they are distinct carrier
    displacements with the same generation terminals. Build the six-edge network between the two
    generations, show whether Conservation makes them parallel edges (aperture) or a chain
    (length), and compare with the `14` and `10` of `π/14`, `π/10`. Falsifier: a count other than
    the ones `HalfTurnMixing` derives.
* **`|V_cb|`** (`VcbEnvelope`, candidate formula): `env 1 / env (Δ − D)`, or the unit-source
  divider `env 1 / (env 1 + env (Δ − D))`; the data do not separate them, and the unit drive is
  singled out among simple drives. The supporting reading (`D` refresh ticks per cycle, `Δ − D`
  free) is not supported by the library: rows are assigned whole (`RequirementRows`, no clock-slot
  variable) and weak reaches all `43` clock addresses (`WeakLocality`). Next: trace a weak-wall
  input through the actual refresh with its generation label (`ExchangeChirality`), find the first
  operation that changes the label and the source and sink terminals, then Kron-reduce; the same
  convention on the spectator side must recover `VubSeriesPath`. If the weak update acts within
  each generation, the drive is the inter-wall link's and refresh placement does not fix `|V_cb|`.
  Suggested attack:
  * Settled (`ThirdGenerationMixing`): two real conserving sectors share `(1, 1, 1)` and their
    third row and column are `(1, 0, 0)` exactly (`zero_mode_unmixed`); that is the data's leading
    order, so `|V_ub|`, `|V_cb|` are first-order effects of what lifts the zero mode differently in
    the two sectors, `⟨v_k, P w⟩/λ_k`, not couplings read off directly. Next: identify `P`. Two
    candidates in the library: a flux (`LinkFlux`) and a non-conserving leak. Test each against
    the gaps `in_cycle_spectrum` gives (`3α/2` for the node-class generation, `a + α/2` for the
    in-cycle pair): `VubSeriesPath`'s `1/(2α⁻¹ + π)` must come out as `⟨v_k, P w⟩/λ_k` with
    `P` built from the same legs and boundary, and the same `P` must give `|V_cb|`. If the
    required `P` has no library source, the amplitude-is-admittance premise of `VubSeriesPath` is
    the error; record it.
  * Status (numerical, `tools/flavour_link_fits.py`, recorded in OVERVIEW): the eigenvector
    reading is excluded for quarks (`χ² ≈ 1040`, from `m_s/m_d`), seesaw or exact masses. The
    transfer reading survives: masses generation-diagonal, `V = e^{−iK}` (or Cayley) with `K` the
    fluxed incidence network; it needs a flux of `43°`–`49°` and `|K₁₃| ≈ 0.0045`. Do not match
    the flux to a fraction of `π`; it moves by several degrees with the generator form.
  * Done: the generator is Cayley (`TransferGenerator`, equal leads), and `VubSeriesPath`'s series
    path fails the scale-free ratio test (`4.7σ`), so it is not structural in this reading.
  * Next, in order:
    1. The flux: with the Cayley generator it is `49.1 ± 1.1°` (PDG 2024). Closed: the in-wall
       kinetic hop (`PMAction.WallHopPhase`: a quarter turn that cancels in `t₁t̄₂`). Left: the
       node-crossing hops (time-axis component, `PMAction/REVIEW-AND-NEXT.md`) or a background
       holonomy around the loop. A wall-side leg phase would give `6θ` (`LinkFlux`), i.e.
       `θ ≈ 8.2°`; but `LinkFlux`'s legs carry `GenerationWalls`' wall sides, which describe the
       inter-wall crossing, not the charged-current transfer (a single-wall shift on the weak wall),
       so that model may not apply to the CKM. Closed: the node crossing's own phase. The odd-sector
       phase of the refresh is continuous in time (`PMAction.Machine.OddCarrierPhase`), but it is the
       same in both directions, and in the zero-energy reduction it is a real denominator
       (`TickPlacement.node_denominator_real`), so it never enters the flux. What is left: leg
       phases that differ between the two legs at a class vertex, or a background holonomy around
       the loop. In the transfer reading both legs of a crossing are on the weak wall (a single-wall
       shift), so class- or generation-only leg phases cancel or are gauge
       (`LinkFlux.class_phase_cancels`). The next question is therefore whether the weak wall's
       transfer loop encloses a substrate holonomy (a gauge background on the generation–class
       hexagon). Found: the library's gauge fields live on spatial links only, and
       `PMAction.FlatPersistence` prices any loop holonomy `e^{iΦ}` by a flag probability
       `sin²(Φ/2)` per readout, minimized by `Φ = 0`. So, if the generation loop is priced like a
       transport loop (`CommonResponse`), persistence sets the CKM flux to zero unless the loop has a
       source, and the data (`Φ ≈ 49°`, `J ≠ 0`) say it has one. The library has no such source
       now; this is the missing ingredient for the CKM phase. The only CP-odd structure in the
       library is the cyclic wall orientation (`PMConstants.GenerationWalls.side`; its two
       conventions are exchanged by the wall swap, which conjugates the flux, `LinkFlux`). Next:
       treat that orientation as the source and find the least-cost holonomy with it present
       (the analogue of a field with a mean source in `FlatPersistence`); if the minimum is `0` or
       `π`, the orientation is not a source and the CKM phase has no origin in the library; record
       that. Correction (numerical): a real network does give `J ≠ 0` through the scattering's `i`;
       what fails without a flux is the magnitudes (`|V_ub|` on three vertices). Tried: separate up
       and down generation vertices sharing the class vertices (six leads), real legs: best
       `χ² ≈ 440`, and the down-to-up block keeps only `80%` of each row, because up generations
       couple to each other through the class vertices. But the charged current is generation-universal with
       isospin a separate factor (`FlavourCurrent`: the same raising on every generation), so the
       transfer acts on generation space alone: three leads, one per generation, the `d → u` label
       factored out. That is `TransferGenerator`'s three-vertex network, with one loop and one
       flux. Separate up and down loops (candidate "two sectors sharing legs") have no place in
       it, and the six-lead networks model a different object; candidate closed. The source
       question stands for the single loop: the cyclic wall orientation, or a `Z₃` twist from the
       cyclic generation order (a competition between offsets `0` and `2π/3` has its minimum strictly
       between them; any competition among offsets `0` and `π` only has minima at `0` or `π`).
       **Status: the library has no source for the CKM phase.** Searched: no `Z₃` phase exists in
       PMSubstrate, PMConstants, PMAction or PMFlavor; the loop readout (`PMAction.CommonResponse`,
       flag `(1 − Re⟨φ, Uφ⟩)/2`) compares the transported amplitude with its own untransported
       reference, so every readout's preferred offset is `0`, and an offset other than `0` would
       need the reference to return rotated after one generation loop, which nothing in the
       library does (the loop returns each generation to itself with the same native label, and
       `GenerationWalls.side` is a labelling, not a phase). Closed sources: in-wall kinetic hops
       (`PMAction.WallHopPhase`), class- or generation-only leg phases (`LinkFlux`), the node's
       own odd-sector phase (`TickPlacement`), two sector loops (one loop on generation space).
       The supplied `δ = arctan(σ/χ)` (`FlavourInvariants`) has no mechanism behind it. What would
       supply one: a loop readout whose reference is rotated by the generation cycle, i.e. a
       generation-space holonomy that persistence cannot remove. Look for it in the refresh
       schedule over the `43` clock addresses (does one full clock cycle permute the generations
       or rotate their reference phases?) before anything else. The same flux must also give `J`, which is now an output, not an input: the
       fit uses `J`, so refit with `|V_us|, |V_cb|, |V_ub|` only and check `J` and `α` as
       predictions of a derived flux.
    2. The couplings: the data give the scale-free `K₂₃/K₁₂ = 0.183` and `K₁₃/K₁₂ = 0.0185`. The
       network (`kronLink`: per-class two legs) must produce these from leg values; the
       in-cycle candidate `π/14` (`HalfTurnMixing`) is now a statement about the scaled coupling
       `2K₁₂/γ` (first order of `−(1 − iK/γ)(1 + iK/γ)⁻¹`), not `|V_us|`; they differ by under `1%`.
    3. The generation-diagonal mass. Done (`InterWallDiagonal`, `MassInsertion`): the equal-class
       crossing gives no diagonal; a diagonal mass needs an insertion of the generation's label
       class; the label-`v` generation has the only in-cycle insertion and the only two
       node-crossing mixings; the data put it heaviest, so the insertion acts directly, not through
       `δ²/σ(Y)`. Next:
       * Closed (`MassInsertion.light_pair_degenerate`): the insertions in the on-site slot with the
         equal-class link, reduced as in `WallSeesaw`, give a degenerate light pair for every
         parameter choice (ratio below `1.52` numerically, data at least `16.8`). So the light
         masses do not come from inverting a link; what survives is a direct zero-mode-to-zero-mode
         term carrying the label class (generation-diagonal), the transfer reading's premise.
         Not derived yet: `PMAction.ZeroModeCoupling` locates the direct term as the off-Wilson
         part of the inter-sector hop, `(r − 1)`, a common factor; the class dependence is the node
         passage, not a class-dependent `r` (`TickPlacement`).
       * Split of the two light generations: both insertions are spinor (node-crossing); what
         separates them is the `s`/`c` asymmetry (`ExchangeChirality`: one node class sits on the
         weak wall). Derive which insertion is on the weak wall and whether that costs a further
         factor; the data need ratios `207` (μ/e), `about 20` (s/d), `about 500` (c/u).
       * Size: the light insertions cross the node. Whether that is one leg (amplitude `√α`) or two
         (`α`) is the same question `NodeElimination` answers for mixing; apply its rule, do not
         fit. `TickPlacement` closes the discrete-time route to any other class factor, so this
         rule is now the whole class dependence at leading order. Applied (leading order, no
         fit): quarks two legs, heavy/middle `≈ α⁻¹ = 137`; leptons one leg, `≈ α^{−1/2} = 11.7`.
         Data: `m_t/m_c` `136` (`m_t` pole over `m_c(m_c)`) to `271` (both at `M_Z`), `m_b/m_s ≈ 54`,
         `m_τ/m_μ = 16.8`. The up-quark ratio agrees only at one scale choice, and the down-quark
         and lepton ratios miss by `2.5×` and `1.4×`. So the leg rule alone does not give the
         heavy/middle ratios; an up/down asymmetry and a lepton correction are needed, or the rule
         is wrong for masses. Recorded as not supported; do not tune it. Data ratios of the heavy to the middle generation are `16.8` (τ/μ), about `50`
         (b/s) and `130`–`270` (t/c, scale-dependent), so no single power of `α` fits all; record
         that rather than choosing.

Working notes for the next session: there is no Lean toolchain in the device shell, so write
proofs to be deterministic and ask Kate for `./build.sh fast PMFlavor`. Avoid `simp` on a
transposed matrix literal or a product of three literals; name the intermediate literal and use
`rfl` for literal identities (`LinkKronComparison.Lcg_eq_transpose`, `Lgc_mul_inv`). Numerical
scans belong outside Lean and are labelled as such here.

