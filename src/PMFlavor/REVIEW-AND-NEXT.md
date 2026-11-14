# PMFlavor — open work

Closed tests and retired routes are recorded in [OVERVIEW](OVERVIEW.md). Names used here: `Y_gap` is
the inter-wall link of `PMAction.WallSeesaw`; `M_direct` a term joining the two light modes directly;
`K_cc` the charged-current transfer network of `TransferGenerator`. The CKM entries are `S_ij` of that
transfer, not `K_ij`.

Working reading (candidate, with its premises): masses are generation-diagonal and the CKM is the
zero-energy scattering transfer `S(K_cc)` on generation space, three leads of equal width. The two
premises, zero-energy scattering on generation leads and equal lead widths, are this folder's own
model assumptions (`TransferGenerator`); a microscopic lead derivation, if pursued, belongs to
PMAction.

* **The in-cycle mixings** (`HalfTurnMixing`, `HalfTurnAperture`, candidate): `s₁₂ = π/14` and
  `sin²θ₁₂ = π/10`. Premises, listed in `HalfTurnAperture`: cross-orbit label-blindness (the
  physical type-preserving symmetries keep vector and spinor channels in separate orbits), the
  conductance normalization (the channels carry the whole half-turn measure), and the aperture
  reading. In the transfer reading `π/14` is a statement about the scaled coupling `2K₁₂/γ`, which
  differs from `|V_us|` by under `1%`. Tests: split the half-turn into two arcs with fixed generation
  terminals (an aperture adds them in parallel, a length in series); the six axis-free vector
  displacements (`ExchangeAxis.vector_free`) are a candidate for the separately addressable
  directions. JUNO's full precision separates `π/10` from the draft's `1/(2φ)`.
* **The couplings of `K_cc`.** The data (external fit, conditional on the two premises) give the
  scale-free ratios `K₁₃/K₁₂ = 0.0185 ± 0.0005` and `K₂₃/K₁₂ = 0.183`. The network (`kronLink`: two
  legs per class) must produce them from leg values. `VubSeriesPath`'s path admittance is a candidate
  for `K₁₃`; its ratio to `π/14` is `0.0161`, `4.7σ` low, so as a statement about `K₁₃` it fails;
  its agreement with `|S₁₃| = |V_ub|` is not explained by the path.
* **`|V_cb|`** (`VcbEnvelope`, candidate formula): `env 1 / env (Δ − D)` or the unit-source divider;
  the data do not separate them. The supporting tick reading has no schedule basis
  (`RequirementRows` assigns sectors to rows, no service-time map; reachability of all `43`
  addresses does not fix a schedule). To derive the denominator, exhibit the schedule and count its
  unused ticks; separately identify the drive or the terminals. In the transfer reading `|V_cb|` is
  `|S₂₃|`, and its generator entry `K₂₃` is fixed by the ratio above.
* **The CKM phase.** The transfer `S(K_cc)` needs a flux on its single generation loop to fit the
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
* **The masses.** Settled upstream (OVERVIEW; `CyclicSeesaw`, `PMConstants.GenerationMass`): the
  seesaw on the one-directional crossing gives three equal masses, so the hierarchy is the composite
  diagonal term (crossing plus a carrier of the label class), with one heavy generation (label `v`,
  the weakly mixed one) and two light. Open: its sizes. The node-passage rule (`NodeElimination`:
  quarks two legs, `≈ α⁻¹`; leptons one leg, `≈ α^{−1/2}`) does not match the heavy/middle ratios
  (`m_t/m_c` `136`–`271`, scale-dependent; `m_b/m_s ≈ 54`; `m_τ/m_μ = 16.8`); not supported, do not
  tune. The node amplitude must fit these and the `|V_ub|`, `|V_cb|` suppression together
  (`PMAction/REVIEW-AND-NEXT.md`, generation sector). The light-pair split (`207`, about `20`, about
  `500`) needs the `s`/`c` asymmetry. `ReferenceWallMass` (with `PMAction.ReferenceDetuning`): `M = D_R (δ_O + cyc κ_O)`, so the masses
  are the reference-wall carriers and the light ratio is `κ_R(s)/κ_O(s)`; the earlier equal-carrier
  exclusion assumed equal `δ` on both walls and does not apply. Masses and mixing together
  (`tools/reference_wall_mixing_scan.py`): carriers shared by up and down are disfavoured (misses up
  to `2.8×`); per-sector carriers fit within `30%` with 6 parameters for 7 numbers, no test. What
  makes it a test: derive the carriers (PMAction node-passage cost per wall), or derive why up and
  down carriers differ. Test from `CompositeMass`: `M` keeps the cyclic `δ²/y` term,
  which mixes generations at relative size `δ/κ`; once `κ` is derived that mixing is a CKM
  prediction, not a fit. Its premise holds for a Wilson-form carrier (`PMAction.CarrierFlip`), so the
  mass ratios are the carrier amplitude ratios.
* **Dressing outlets.** `DressingEvent.event_law_spatial` works on axis labels only (no site move);
  open is whether the actual CKM loss realizes that event law and the row-to-outlet identification
  (`PMConstants/REVIEW-AND-NEXT.md`).

Working notes for the next session: there is no Lean toolchain in the device shell, so write proofs
to be deterministic and ask Kate for `./build.sh fast PMFlavor`. Avoid `simp` on a transposed matrix
literal or a product of three literals; name the intermediate literal and use `rfl` for literal
identities (`LinkKronComparison.Lcg_eq_transpose`, `Lgc_mul_inv`). Numerical scans belong outside
Lean (`tools/flavour_link_fits.py`) and are labelled as external fits. When editing these files by
slicing between two anchors, check that nothing between them is lost (two items were dropped this
way once and recovered from `a80311f`).
