# PMHadrons — open work

## 0. One template for π, K, n — the neutron gap — H

`DecayInstantiation` puts the three semileptonic decays in one `DecayChannel` template:
`|V|²` in map (PMFlavor), no Governor (a Governor only restricts; PMAtoms' beta channel has
none), and one shared margin `R = (32/33)/|V_ud|² ≈ 1.0211` fixed by the pion.

* pion unchanged (`pionChannelCKM_rate`), `−2.8σ`;
* kaon gets the same `R` (`kaonChannelCKM_rate`): +1.28%, the `f_K` tension;
* neutron: `τ = τ_exact · 33/32 = 948.69–948.70 s` (`neutronLifetimeUnifiedSeconds_bounds`,
  e8p `neutron_lifetime_unified_s`), +8.0%. The old `877.15 s` row used `41/43` as a Governor
  above one (`neutronCorrected_governor_gt_one`) and is now shown unscored.

The neutron's +8.0% equals, to 0.01%, what it has and the mesons do not: Coulomb on the outgoing
electron (1.032), `g_A` (1.034; E8 `5/4` vs `1.2754`), low-energy radiative (1.018), times
spectral-vs-continuum (0.994). The three, worked:

1. **`R` — done as the running of the contact** (`ShortDistanceRunning`). With E8 `α`, the E8
   carrier charges, the E8 tree-level `m_Z` and the E8 proton,
   `R = 1 + (3α/4π)(1+2Q̄) ln(m_Z²/m_p²) ∈ (1.021178, 1.021180)` (`runningFactor_bounds`); the
   pion's assigned `32/33` gives `R ∈ (1.021111, 1.021131)`; they agree to `< 7×10⁻⁵`
   (`runningFactor_sub_shared`). So `32/33 = |V_ud|²·R` is the running, not a free margin. The
   one-loop coefficient `(3/4π)(1+2Q̄)` is the standard result (same status as
   `RunningCoefficients`' spin/orbital inputs).
2. **Coulomb — the cube's own Green function gives ~1%, not ~3%** (floating point, outside Lean).
   With `PMAtoms.LatticeCharge3`'s exact Green function as the proton's potential on the
   `3×3×3` cube, `H = L − κα G(·, centre)`: the open-mode weight fraction moves by only
   0.13–0.19% (all modes shift together), and the open mode's density at the proton rises by
   0.8% (`κ = 4π`) to 1.1% (`κ = 4π√2`, the non-relativistic link `a = 1/(√2 m_e)`). The SM's
   3.2% comes from the continuum electron at low velocity; on three sites per side the electron
   is spread over the cube. So the lattice Coulomb as built supplies about a third of the gap;
   the unit link `κ` is itself a choice to settle.
3. **`g_A` — step 1 done, step 2 open.** `g_A` = how much of a carrier spin flip survives as a
   nucleon spin flip = (count) × (motion reduction).
   * **Count** (`AxialCount`): three carriers (one per colour, `σ − χ = 3`), one spin bit each
     (`leg_state_binary`), the `u/d` doublet (`PMAction.ChargedCurrent`), symmetric in
     spin ⊗ label because the three-colour singlet is antisymmetric. Exact computation on the 64
     states: vector `1`, axial `5/3` (`axial_ratio`), and `5/3 = σ/(σ − χ)`
     (`axial_ratio_eq_invariants`).
   * **Reduction** (tried, not settled; floating point): PMAction's Wilson carrier at its Wilson
     point `r = 1`, confined to the `3×3×3` cube (hard edge, or a domain-wall mass outside on a
     `7³` lattice — both converge), gives `⟨Σ_z⟩ = 0.893`, so `g_A = 1.488` (+16.7%); a massless
     continuum carrier (bag model) gives `0.65` (`g_A = 1.09`). The measurement needs `0.765`.
     At `r = 1` the Wilson term is a mass of `≈ 0.88` against `≈ 1.2` kinetic at the cube's
     momentum `π/4`, so the carrier is only half relativistic. `r` is fixed by `DomainWall`, not
     tuned. The physical light carrier is PMAction's chiral zero mode, which has no finite-region
     form yet (see PMAction `REVIEW-AND-NEXT`).
   * **Reduction** (what it is): the carriers are confined and moving, so part of their spin is
     orbital. On the substrate this is the lowest confined Dirac mode on the neutron's own
     `3×3×3` cube (`PMAction.Dirac`, `ConcreteFermion`; `cube_interior_iff`): the fraction of its
     density in the spin-carrying component. The measurement needs `1.2754/(5/3) = 0.765`; the
     cube's number is the answer either way.
   * `NeutronRate.gA = σ/D = 5/4` stays the assigned value until step 2 replaces it.

Net: with `R` from the running, the neutron stands at +8.0%, of which the lattice Coulomb can
account for ~1% and the rest is `g_A` (~3.4%) plus the low-energy radiative part (~1.8%) plus
the Coulomb shortfall (~2%).

## 1. Decay margins — what the substrate number is, and what it matches — H

Each channel has one substrate number on its rate. Read from the substrate side, then matched to
the SM factors it lines up with (comparison, floating point, outside Lean):

| channel | substrate factor on the rate | SM bundle it matches | match |
|---|---|---|---|
| π⁺ → μ⁺ν | `(Δ+ν+σ)/(Δ+ν+σ+χ) = 32/33` (`E8Margin.pionMargin`) | `|V_ud|²·S_EW`, `S_EW = 1 + (2α/π) ln(m_Z/m_p)` | `0.96975` with E8 `|V_ud|`, `α`, `m_p`, uncorrected `m_Z` (6×10⁻⁵); `0.96831` with measured `|V_ud|` (0.14%) |
| n → p e ν̄ | `Δ/(Δ−χ) = 43/41` (`neutronMarginFactor`, applied as lifetime × 41/43) | `|V_ud|²·(1+3g_A²)/(1+3·(5/4)²)·⟨F_Coulomb⟩·(1+RC)` relative to the spectral `1/(3P)` | `1.0468` against `1.0488` (0.2%) |
| K⁺ → μ⁺ν | none; `|V_us|² = (π/14)² c₁₃²` written explicitly | `|V_us|²·S_EW` | the `S_EW` part has no substrate factor; the kaon's +3.5% is that plus the `f_K` tension |

So the two margins pointing in opposite directions is not a contradiction: each is one substrate
number standing for a different SM bundle. The pion's is dominated by `|V_ud|²` (down); the
neutron's by Coulomb attraction and the radiative correction (up). The K/π ratio
(`KaonPionRatio`) confirms the pion bundle contains `|V_ud|²`.

Open, from the substrate side:

- **41/43 already has a substrate reading: the Governor.** `PMAtoms.PersistenceComplex` proves
  `phaseMargin_eq_one_add_governor` (`41/43 = 1 + governorTerm = 1 − χ/Δ`) and
  `neutronMarginFactor_eq_phaseFraction`: it is the fraction of the `Δ` clock phases that survive a
  boundary gap `χ` (`survivingPhases`, `Δ−χ = 41`). The same Governor rule is the alpha
  suppression, `alphaPhaseFraction gap = 1 − gap/Δ`, and there it **multiplies the rate**
  (`AlphaPersistence`: `alphaCapacity · alphaPhaseFraction`), as `E8Margin.phaseCorrected` does.
  The neutron divides its rate by it (lifetime × 41/43). So the reading is settled; the neutron is
  the one use that applies it the other way, and it is the use that matches 878 s.
- **32/33 has no reading yet.** Why the two-body meson channel loses `χ` over the
  `Δ+ν+σ = 64` slots.
- **`E8Margin` disagrees with the neutron's use.** `phaseCorrected w = (41/43)·w` and
  `phaseCorrectedLifetime τ = τ/(41/43)` lower the rate; `neutronLifetimeCorrected = (41/43)·τ`
  raises it. One reading has to be chosen and the other definition changed.
- **The kaon channel's factor.** On the pion's pattern the kaon would carry `|V_us|²` times the
  substrate counterpart of `S_EW`; the substrate supplies `|V_us|²` but not that counterpart.
- The SM side's `g_A`: `NeutronRate.gA = σ/D = 5/4` against `1.2754`; on the spectral route `g_A`
  does not appear separately.

## 2. Beta cube rule — C/H

With the `3×3×3` cube only the lowest mode is open for any cutoff in `[6−3√2, 6−2√2) m_e`, so
`τ_n` does not depend on `m_n − m_p` there; below `6−3√2 = 1.757 m_e` no mode opens (tritium,
C-14 would not decay). Nuclear beta decay needs a rule for the cube (`≥ 5×5×5` for tritium).

## 3. Canonical values — done

`PMHadrons.Values` exports the nucleon and meson masses, decay constants, the corrected
lifetimes, the K/π ratio, `neutronMarginFactor` and the Toll/Governor emission names, for
`PMAtoms` and `e8p`. e8p still cites the defining modules; re-point its hadron rows next.

`PMFlavor.Values` is the single source for `vud`, `vus`, `vub`, `vcb`, `q2`, `vudDressed`,
`jarlskog`, `jarlskogGeo` and their bounds. Pointed at it: `KaonWidth.vusE8` and
`PMElementaryParticles.CarrierAmplitude.vud` (now abbreviations), `KaonPionRatio`,
`PMCosmology.Primordial`, and the e8p CKM rows. `PMFlavor.FlavourPulls` no longer keeps its own
`αinv`/`s12`/`s13`/`vus`/`vcb` copies. `PMCosmology.Tensions` takes `α⁻¹` from
`PMSubstrate.geometricIndex` instead of `PMFlavor.CKM`. `NeutronPrediction.neutronMarginFactor` is
`PMSubstrate.E8Margin.phaseMargin`.

## 4. The emission space (f_π, f_K) — C

`EmissionSpace` makes the pion's count a set: `pionEmission = cone ⊔ survivingPhases`
(Margin's `Δ²` one-cycle cone plus the Governor's `Δ − χ` boundary survivors), `|Ω_π| = 1890`.
The kaon needs the same rule plus what its line carrier (`σ`-direction register) does to the set.
Five simple rules are tabulated in the module; none reaches FLAG's `fK/fπ = 1.1934(19)`
(`|Ω_K| ≈ 1581–1586`). The assigned `Δ² − ν²` is the cone with its first `ν` slices removed, but
without the survivors the pion keeps. The missing premise: how a direction-holding carrier
restricts the cone. The cone is one spatial direction; a `σ`-direction carrier probably needs the
cone in more directions. This is the `f_K` tension's source (f_k_mev −3.8σ and the K/π ratio
−5.6σ are the same gap).
