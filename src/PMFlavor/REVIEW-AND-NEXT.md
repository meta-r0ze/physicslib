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
       `θ ≈ 8.2°`; find the substrate source from structure first and compare after. The same flux must also give `J`, which is now an output, not an input: the
       fit uses `J`, so refit with `|V_us|, |V_cb|, |V_ub|` only and check `J` and `α` as
       predictions of a derived flux.
    2. The couplings: the data give the scale-free `K₂₃/K₁₂ = 0.183` and `K₁₃/K₁₂ = 0.0185`. The
       network (`kronLink`: per-class two legs) must produce these from leg values; the
       in-cycle candidate `π/14` (`HalfTurnMixing`) is now a statement about the scaled coupling
       `2K₁₂/γ` (first order of `−(1 − iK/γ)(1 + iK/γ)⁻¹`), not `|V_us|`; they differ by under `1%`.
    3. The generation-diagonal mass. `InterWallDiagonal`: the E₈ gluing makes the inter-wall link
       zero on the generation diagonal, and a traceless link cannot carry any charged hierarchy.
       So the masses need a diagonal term the equal-class crossing cannot give. Candidates, each
       to be derived, not chosen: (a) a composite, an equal-class crossing followed by a
       single-wall carrier shift by the generation label (the class difference `b + c = m`), which
       is second order and so naturally small; (b) a flavour-dependent on-site term (the
       library's `δβ ⊗ 1` is flavour-blind, `WallExchange`). Test: the composite gives diagonal
       entries of order (crossing) × (carrier amplitude); check whether the carrier amplitudes
       already in the library (node admittance `α` for spinor classes, the in-cycle unit for the
       vector class) give hierarchies of the observed size, with the third generation (the one
       whose label is the vector class) distinct. This also decides between the readings: if the
       diagonal comes from (a), masses and mixing share the carrier amplitudes.

Working notes for the next session: there is no Lean toolchain in the device shell, so write
proofs to be deterministic and ask Kate for `./build.sh fast PMFlavor`. Avoid `simp` on a
transposed matrix literal or a product of three literals; name the intermediate literal and use
`rfl` for literal identities (`LinkKronComparison.Lcg_eq_transpose`, `Lgc_mul_inv`). Numerical
scans belong outside Lean and are labelled as such here.

