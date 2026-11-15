# PMFlavor — open work

Closed tests and retired routes are recorded in [OVERVIEW](OVERVIEW.md). Names used here: `Y_gap` is
the inter-wall link of `PMAction.WallSeesaw`; `M_direct` a term joining the two light modes directly;
`K_cc` the charged-current transfer network of `TransferGenerator`. The CKM entries are `S_ij` of that
transfer, not `K_ij`.

Status. Per-species fits to measured masses and CKM magnitudes were removed (2026-11-14): they fit
the Standard Model with wire-shaped parts rather than deriving what the substrate gives. What the
wire has derived: the light-mass form `M = D_R (δ_O + cyc κ_O)` (`ReferenceWallMass`) and the
charged-current couplings `K₁₃ = K₂₃` (OVERVIEW). One number is open, `δ_O/K` (PMAction). What
"mixing" is in PM terms, a transfer between protocols over the wire, is not yet derived. The items
below that compare candidate formulas with CKM or PMNS data are to be reviewed module by module:
does each number come from structure, with data only as the test afterwards?

* **The in-cycle mixings** (`HalfTurnMixing`, `HalfTurnAperture`, candidate): `s₁₂ = π/14` and
  `sin²θ₁₂ = π/10`. Premises, listed in `HalfTurnAperture`: cross-orbit label-blindness (the
  physical type-preserving symmetries keep vector and spinor channels in separate orbits), the
  conductance normalization (the channels carry the whole half-turn measure), and the aperture
  reading. In the transfer reading `π/14` is a statement about the scaled coupling `2K₁₂/γ`, which
  differs from `|V_us|` by under `1%`. Tests: split the half-turn into two arcs with fixed generation
  terminals (an aperture adds them in parallel, a length in series); the six axis-free vector
  displacements (`ExchangeAxis.vector_free`) are a candidate for the separately addressable
  directions. JUNO's full precision separates `π/10` from the draft's `1/(2φ)`.
* **The couplings of `K_cc`** (transfer reading). With the wire's couplings `K₁₃ = K₂₃` (both spinor
  edges through the node). The network (`kronLink`: two legs per class) must give the couplings from
  leg values. A microscopic derivation of the generation leads (and their equal widths) would be
  PMAction work.
* **`|V_cb|`** (`VcbEnvelope`, candidate formula): `env 1 / env (Δ − D)` or the unit-source divider;
  the data do not separate them. The supporting tick reading has no schedule basis
  (`RequirementRows` assigns sectors to rows, no service-time map; reachability of all `43`
  addresses does not fix a schedule). To derive the denominator, exhibit the schedule and count its
  unused ticks; separately identify the drive or the terminals. In the transfer reading `|V_cb|` is
  `|S₂₃|`, and its generator entry `K₂₃` is fixed by the ratio above.
* **The CKM phase.** In the mass reading the wire's amplitudes are real (`DomainWall`'s hop,
  `CarrierFlip`'s `κ = −t/2`), so `U_uᴴ U_d` is real orthogonal and `J = 0`: the phase still has no
  source, in either reading. The transfer `S(K_cc)` needs a flux on its single generation loop to fit the
  magnitudes (`49.1 ± 1.1°`, external fit). `FlatPersistence` makes a sourceless holonomy flat, and
  the library has no source: every candidate searched is closed (OVERVIEW, "Where a CP phase can
  sit"). The supplied `δ = arctan(σ/χ)` has no mechanism. A new premise would have to give a
  generation-space holonomy with an offset other than `0` or `π`; state it narrowly and test it by
  predicting `J` and the triangle angle `α` from a refit on the three magnitudes, not by matching
  `49°`. Targets: `α = π/2` would give `δ = 67.7°` in the library's convention
  (`CPQuarterTurn.quadrature_pythagoras`; HFLAV `α = 84.1 (+4.5/−3.8)°`), equivalently
  `|V_td| = 0.00858` (data `0.0086 ± 0.0002`). The sign is the wall-naming convention (`LinkFlux`,
  `ReferenceFlavour.column2_difference_conj`).
* **`θ₂₃`** (the lepton `s`/`c` parity breaking). No construction yet, and the data do not fix the
  octant: NuFIT 6.0 normal ordering gives `sin²θ₂₃ = 0.561` without the Super-Kamiokande atmospheric
  data and `0.470` with it, so the draft's upper-octant `0.5748` (`PMNSGeometry.atmos_upper_octant`)
  is at risk. `Theta23Wall`: the asymmetry `(W_μ − W_τ)/(W_μ + W_τ) = 2 sin²θ₂₃ − 1` (NuFIT `+0.122`
  or `−0.060`), and a wall factor common to both readouts cancels (`common_wall_cancels`), so a
  construction must supply a `μ`–`τ`-asymmetric generation factor or wall overlaps correlated with the
  readout (`wall_only`). On the incidence graph `μ` and `τ` reach the reference through different
  class vertices (`s` and `c`); the factor may be the same `s`/`c` vertex difference the `|V_cb|`
  item needs. Test against both NuFIT values.
* **The wire's own mixing.** The row index of `M` is the reference's wall, which is the weak wall
  (`PMAction.ChiralityConvention.weak_acts_on_reference`), so the weak current sees `M`'s left
  rotation. With `k/K = α/2` (`NodeAmplitude`) the rotation depends only on `δ_O/K`; once PMAction
  fixes it, the wire's eigenvalues and left rotation have no free number. Open: compute them as a
  function of `δ_O/K` (in Lean where exact, otherwise a scan labelled external), then how each
  protocol reads them (PMElementaryParticles). Data enter only as the test of the result.
* **Dressing outlets** (owned here; `PMConstants.FlavourDressing` consumes it).
  `DressingEvent.event_law_spatial` works on `Fin 4` axis labels only (no position or hop), so the
  outlet count needs no site move. Open: whether the actual CKM loss realizes that event law (zero
  rate on the time label, equal rate-weighted shares on the three spatial labels) and the
  row-to-outlet identification. Carrier space and the lattice share axis labels only; a carrier label
  change is not a site move (`PMConstants.WeakLocality`, `hL`).

Working notes for the next session: there is no Lean toolchain in the device shell, so write proofs
to be deterministic and ask Kate for `./build.sh fast PMFlavor`. Avoid `simp` on a transposed matrix
literal or a product of three literals; name the intermediate literal and use `rfl` for literal
identities (`LinkKronComparison.Lcg_eq_transpose`, `Lgc_mul_inv`). Numerical scans belong outside
Lean and are labelled as external; do not fit measured masses or mixings to set parameters. When editing these files by
slicing between two anchors, check that nothing between them is lost (two items were dropped this
way once and recovered from `a80311f`).
