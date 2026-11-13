# PMHadrons — open work

## 0. One template for π, K, n — the neutron gap — H

`DecayInstantiation` puts the three semileptonic decays in one `DecayChannel` template:
`|V|²` in map (PMFlavor), no Governor (a Governor only restricts; PMAtoms' beta channel has
none), and one shared margin `R = (32/33)/|V_ud|² ≈ 1.0211` fixed by the pion.

* pion unchanged (`pionChannelCKM_rate`), `−2.8σ`;
* kaon gets the same `R` (`kaonChannelCKM_rate`): +1.28%, the `f_K` tension;
* neutron: `τ = τ_exact · 33/32 = 948.69–948.70 s` before the neutron-only factors
  (`neutronLifetimeUnifiedSeconds_bounds`; e8p `neutron_lifetime_unified_s`), +8.0% against
  the measured value. The candidate `NeutronCorrection` applies the four factors and gives
  `878.50–878.52 s` (`neutronCorrectedLifetimeSeconds_bounds`), +0.01% against PDG. The old
  `877.15 s` row used `41/43` as a Governor above one (`neutronCorrected_governor_gt_one`) and
  is shown unscored.

The +8.0% is the product of the four neutron-only factors, not a separate E8 anomaly:
Coulomb on the outgoing electron (1.032), `g_A` (1.034; E8 `5/4` vs measured `1.2754`),
low-energy radiative (1.018), times spectral-vs-continuum (0.994). The product is `1.0799`.
`NeutronCorrection` applies them as supplied comparison factors; the E8 counterparts, worked:

1. **`R` — done as the running of the contact** (`ShortDistanceRunning`). With E8 `α`, the E8
   carrier charges, the E8 tree-level `m_Z` and the E8 proton,
   `R = 1 + (3α/4π)(1+2Q̄) ln(m_Z²/m_p²) ∈ (1.021178, 1.021180)` (`runningFactor_bounds`); the
   pion's assigned `32/33` gives `R ∈ (1.021111, 1.021131)`; they agree to `< 7×10⁻⁵`
   (`runningFactor_sub_shared`). So `32/33 = |V_ud|²·R` is the running, not a free margin. The
   one-loop coefficient `(3/4π)(1+2Q̄)` is derived in `PMAction.ContactRunning` from the Dirac
   algebra and the leg charges (`runningFactor_from_contact`); the loop's overall normalization is
   still a continuum input.
2. **Coulomb — the lepton cube computes the right physics for the one mode it has**
   (floating point, `tools/lepton_coulomb.py`). On the lepton cube (`CubeScales.lepton_hop`:
   hop `= m_e`, `κ = 4π√2`) with `PMAction.CubeGreen3`'s Green function as the proton's potential,
   the electron density at the proton rises by 1.13%. Diagnosis (Nov 2026):
   * this matches the non-relativistic Sommerfeld factor `πα/v = 1.22%` at the mode's own
     velocity: the single open mode has `T = 1.757 m_e`, so the non-relativistic reading gives
     `v = 1.87c`. Refining the spacing inside the same box lowers it to 0.84% (the gain is not a
     lattice artefact being cut off);
   * larger cubes at the same spacing have slower lowest modes and a larger gain (1.5% at `5³`,
     2.3% at `9³`, 3.6% at `15³`), as the Sommerfeld factor requires;
   * the continuum Fermi factor `2πη/(1−e^{−2πη})`, `η = αE/p`, averaged over the continuum
     spectrum to the E8 endpoint `m_n − m_p`, is `1.0340` (supplied `1.0322`); slow electrons
     carry most of it (`β = 0.3`: 7.8%; `β = 0.9`: 2.6%).
   So the missing ~2% is not a wrong Coulomb law. It comes from the channel's reading: one mode,
   read with the non-relativistic Laplacian at a relativistic energy, carries no slow electrons.
   It is the same question as the spectral-vs-continuum factor and the beta cube rule (§2): which
   electron modes the channel opens. Candidate E8 counterpart: the continuum Fermi factor with
   E8 `α` and the E8 endpoint (`1.034`), the same status as `R` (a continuum calculation with E8
   inputs); not adopted.
3. **`g_A` — count done; reduction has a parameter-free candidate.** Count `5/3` (`AxialCount`);
   E8's `σ/D = 5/4` is the strong-interaction value (`NeutronRate.gA`). The carrier cube gives
   `1.38` on 3 sites per edge; resolved inside the 3-cell volume and centre-of-mass projected,
   `≈ 1.34`; with the source-confined pion cloud, `≈ 1.24–1.28`. Status and open items:
   `PMAction/REVIEW-AND-NEXT.md` A.3; calculations and log: `PILLARS.md`.

Net (Nov 2026): the E8 neutron is the continuum route (§2, `NeutronContinuum`):
`923.37–923.39 s` proved, +5.1%. It supplies the spectral and Coulomb factors from E8 inputs. The
low-energy radiative correction is the electron's own one-loop QED on the same route (Sirlin's
outer correction with E8 `α` and `m_p`, `+1.51%`, `tools/beta_channel_modes.py`, not yet in Lean):
`909.2 s`, +3.5%. **What is left is `g_A` alone:** this route needs `g_A = 1.2763` to give
`878.4 s`; the measurement is `1.2754` (0.07%).

**`g_A` (Nov 2026): the E8 `5/4` is the strong-interaction axial charge; the measured `λ` is not.**
The decay measures `λ = g_A/g_V`, which includes a percent-level electromagnetic correction from
virtual charged pions (Cirigliano, de Vries, Hayen, Mereghetti, Walker-Loud, PRL 129, 121801
(2022), arXiv:2202.10439): `λ = g_A^QCD (1 + δ_RC^λ)`, `δ_RC^λ ∈ (1.4, 2.6)%`. Lattice QCD, which
has no QED, gives `g_A^QCD = 1.246(28)` (2+1+1) and `1.248(23)` (2+1) (FLAG 2021). Against this:
* E8 `σ/D = 5/4 = 1.25` agrees with the lattice values;
* `1.2754/(5/4) = 1.0203` and the continuum route's `1.2763/(5/4) = 1.0210` both lie inside
  the published `δ_RC^λ` range; with that range the route gives `871–889 s` (measured `878.4`).
So the 2% between `5/4` and `1.2754` is the size of the known electromagnetic correction, not a
missing strong-interaction effect. The correction is `(α/2π)(Δ_A − Δ_V)` with
`Δ ∝ Z_π = (m_π±² − m_π0²)/(2e²F_π²)`; the E8 pion masses and `f_π = v/1890` give `Z_π = 0.810`
(the paper uses `0.81`). The rest of `Δ` is set by nucleon low-energy constants (`c₃`, `c₄`, a
counterterm) that the substrate does not yet supply. Open: derive `δ_RC^λ` on the substrate.
`NeutronCorrection` (all four factors supplied from outside E8) stays as bookkeeping. Direction: the rate goes as `1 + 3g_A²`, so a higher `g_A`
shortens the lifetime. The rate now uses `5/4`; the measured `1.2754` shortens it by 3.4%. The
single free carrier's `1.377` would shorten it by 17.6% (to about 806 s, −8%), overshooting, so
it is not fed in.

## 1. Decay margins — what the substrate number is, and what it matches — H

*Partly superseded:* §0 puts the neutron on the pion's template (`|V_ud|²R = 32/33`, no
Governor), so the neutron's `41/43` below is history; what stays open here is the reading of
`32/33` (now `|V_ud|²R`, §0.1) and the kaon's factor. `E8Margin` vs
`neutronLifetimeCorrected`: settled (Nov 2026) — `neutronLifetimeCorrected(Seconds)` is retired
(docstring note, no longer exported by `Values`), so `E8Margin`'s reading (the margin lowers the
rate) is the only one in use.

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
- **`E8Margin` vs the neutron's old use — settled (Nov 2026).** `phaseCorrected` lowers the rate;
  the neutron's `neutronLifetimeCorrected = (41/43)·τ` raised it. The latter is retired.
- **The kaon channel's factor.** On the pion's pattern the kaon would carry `|V_us|²` times the
  substrate counterpart of `S_EW`; the substrate supplies `|V_us|²` but not that counterpart.
- The SM side's `g_A`: `NeutronRate.gA = σ/D = 5/4` against `1.2754`; on the spectral route `g_A`
  does not appear separately.

## 2. Which modes the emitted electron has — H (Nov 2026)

The spectral template is `rate = (G_F²/3)·f_B`, with `f_B` the Boltzmann-weighted fraction of the
lepton cube's Dirichlet modes below the cutoff. On the minimal `3×3×3` cube only the lowest mode is
open, and below `6−3√2 = 1.757 m_e` none is (tritium and C-14 would not decay).

**Persistence reading.** The emitted electron is not a resource of any persistent volume: it
leaves through the Toll boundary (`TollGovernor`). By the same rule that makes the carrier's wall
hard (only a persistent volume's own sites are refreshed), nothing confines it, so its modes are
those of the unbounded lattice at its own spacing, not of a minimal cube. Tested
(`tools/beta_channel_modes.py`, floating point):

* **The Boltzmann template does not survive this.** As the cube grows `f_B` rises from `0.453`
  (`3³`) to `0.741` (unbounded), so the neutron moves from 948.7 s to about 580 s. The template
  saturates at one as the cutoff grows, so it has no `Q⁵` law: the tritium/neutron ratio comes
  out `4×10⁻³` against the phase-space `1.2×10⁻⁶`. Its 3³ agreement with the neutron is not
  a law that extends to other decays.
* **The continuum route does.** With the phase space PMElementaryParticles already derives for
  the muon (`MuonRate`, `PolarMeasure`), `Γ = G_F²|V_ud|²(1+3g_A²) R f/(2π³)`,
  `f = ∫ F(E) p E (E₀−E)² dE`, and only E8 inputs (`G_F`, `|V_ud|`, `R`, `α`,
  `E₀ = m_n − m_p`, `g_A = 5/4`): `954.2 s` without Coulomb (+8.6%; the 3³ template's 948.7 s is
  this to 0.6%, the "spectral factor"), `922.9 s` with the Fermi factor (+5.1%). With measured
  `g_A` it is `892.7 s` (+1.6%); the rest is the low-energy radiative correction.

So the persistence reading removes two of the four neutron-only factors (spectral: it is the
continuum; Coulomb: the Fermi factor with E8 `α`), leaves `g_A` (PMAction A.3) and the
low-energy radiative correction, and gives every beta decay open modes for any `Q > 0`.
**Adopted (Nov 2026).** `PMHadrons.NeutronContinuum` proves the closed-form phase space as the
integral, the leading Coulomb integral, the rate, and the lifetimes `954.32–954.34 s` (no Coulomb)
and `923.37–923.39 s` (Fermi factor to first order); `PMHadrons.Values` and e8p
(`neutron_lifetime_predicted_s`) use the latter. The `3³` template stays as an unscored comparison.
Certified outside Lean (Nov 2026, `tools/neutron_rc_certificate.py`, interval arithmetic on the
E8 bounds proved in Lean): full Fermi factor `922.91–923.06 s`; with the outer radiative
correction `909.22–909.37 s`; with `λ = (5/4)(1+δ)`, `δ ∈ (1.4, 2.6)%`, `871.4–888.7 s`. A Lean
proof of these two integrals (Fermi-factor inequalities, Spence-function bounds, integrability at
`E = 1`) is deferred: it moves the proved value by `0.05%` and `1.5%`.

## 3. The emission space (f_π, f_K) — C

`EmissionSpace` makes the pion's count a set: `pionEmission = cone ⊔ survivingPhases`
(Margin's `Δ²` one-cycle cone plus the Governor's `Δ − χ` boundary survivors), `|Ω_π| = 1890`.
The kaon needs the same rule plus what its line carrier (`σ`-direction register) does to the set.
Five simple rules are tabulated in the module; none reaches FLAG's `fK/fπ = 1.1934(19)`
(`|Ω_K| ≈ 1581–1586`). The assigned `Δ² − ν²` is the cone with its first `ν` slices removed, but
without the survivors the pion keeps. The missing premise: how a direction-holding carrier
restricts the cone. The cone is one spatial direction; a `σ`-direction carrier probably needs the
cone in more directions. This is the `f_K` tension's source (f_k_mev −3.8σ and the K/π ratio
−5.6σ are the same gap).

Tried Nov 2026 (one more premise, outside Lean): a line carrier is massive, so it leaves
slower than the light cone. A cone `|x| ≤ v t` over the same `Δ` ticks, with or without the
`Δ − χ` survivors, gives `|Ω_K| = 1494` (`v = 4/5`), `1597` / `1638` (`v = (Δ−σ)/Δ`), `1764`
(`v = (Δ−χ)/Δ`); none lands in `1581–1586`, and no persistence rule fixes `v`. Searching rule
families against the window is numerology, so this stops here until a premise says how the
`σ`-direction register restricts emission. What would decide it: the kaon's emission as a
computation (the line carrier's walk on the meson's own cube, as `PMAction.ConfinedCarrier` does
for the light carrier), not a count.

**E8's own count has a mechanism (Nov 2026; `PILLARS.md`, meson system).** E8 assigns
`|Ω_K| = Δ² − ν² = 1593` (`EmissionScale.kaonModes`). Reading: register routing is free at the
readout (`Machine.RegisterReference`) but each transition costs a tick (Toll), so routing the
line carrier through its sector's `ν` chiral channels delays the cone by `ν` ticks; routing that
starts at the cycle boundary occupies the `Δ − χ` exits the pion's survivors use. This explains
the assigned number rather than predicting a new one: `f_K/f_π = 1890/1593 = 1.1864`, `0.6%`
below FLAG's `1.1934(19)`. Open: why all `ν` channels, and the `0.6%`.
