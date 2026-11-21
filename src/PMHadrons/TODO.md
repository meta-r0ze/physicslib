# PMHadrons — open work

Results are in [OVERVIEW](OVERVIEW.md); the pillar calculations and their log are in
[PILLARS.md](PILLARS.md).

## Weak widths and meson emission (first)

In order: the normalization decision comes first because every rate below uses it.

- **One charged-current normalization.** Remove `32/33`
  (`MesonFiniteChannels.pionLifetimeCorrectedSeconds`, `E8Margin.pionMargin` as
  a rate factor) and `DecayInstantiation.sharedFactor` once nothing reads them;
  put the neutron in the same convention; derive the residual emission counts
  for `f_π` and `f_K` (`1890` and `1593` targets). Do not count the dressing,
  running and `δ` twice.
- **Partial, inclusive and total rates.** Complete the physical channel sums
  before predicting total lifetimes. The pion electronic rate still needs
  inclusive radiative matching. Derive the pi-zero branch rates, including
  Dalitz and other open channels, rather than using the measured two-photon
  fraction as an E8 input. Keep the triangle-loop normalization in
  `NeutralPionWidth` identified as supplied until derived.
- **Kaon multibody kinematics and amplitudes.** Give the electron and muon modes
  distinct massive phase spaces in `ParticleChannels`. Derive the form-factor
  normalization and slope, radiative and isospin corrections, and bound-state
  amplitudes for the semileptonic and nonleptonic channels.
- **Neutron low-energy matching.** Derive the axial radiative shift, including the nucleon
  low-energy constants and counterterm. Specify whether the assigned `g_A = 5/4` is a core or a
  fully strong-dressed QCD coupling before adding strong pion-cloud and electromagnetic effects;
  those are distinct corrections. Formalize the full Fermi-factor and outer-radiative integrals
  already evaluated in `tools/neutron_rc_certificate.py`. The published 1.4–2.6% axial-shift
  estimate sets an unknown counterterm contribution to zero; its 871–889 s diagnostic band is not
  a parameter-free E8 lifetime prediction. Do not insert measured `g_A` as the derivation.
  Benchmark: [Cirigliano et al.](https://arxiv.org/pdf/2202.10439).
- **Meson emission and finite radiation.** Derive one emission-space rule for both mesons,
  reusing `EmissionSpace`'s pion cone-plus-survivors construction. Explain from line-carrier
  dynamics why kaon routing uses all nu channels and occupies the pion's surviving exits.
  Compute the charged/isospin and photon-inclusive matching in the same convention as the
  emission overlaps. Do not choose a nearby replacement for the count 1593 by matching data.
  Benchmark conventions: [PDG meson review](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-pseudoscalar-meson-decay-cons.pdf).
- **Tau inclusive hadronic factor.** Derive the inclusive quark-current spectral weight, including
  strong dressing, strange-channel masses, CKM/dressing and short-distance electroweak matching,
  so the tau total lifetime has no supplied branching fraction. The target inferred from `B_e`
  is a falsification test, not a fitted value of `h`.

## Lean organization (from the 2026-11-17 review)

- **Neutron routes.** After the normalization decision, decide whether e8p keeps
  the finite-cube rows as labelled intermediates.
- **Meson-width conventions.** The normalization item above decides which of the
  three overlapping normalizations survives; then keep one module for it.
  Keep the finite-cube instances that PMAtoms uses.

## Nucleon and pion dressing (after the weak widths)

- Recompute the cloud and intrinsic magnetic moments with the finely resolved, centre-of-mass-projected carrier as the source. Include recoil. The axial and pion source is the on-site spin `Σⱼ` on both walls (`PMAction.ConfinedAxialCurrent`); its value needs the carrier's size (PMAction's carrier level and radius certificate).
- Determine the Toll rule for a virtual pion pair that leaves and returns, and the Governor constraint on the nonperturbative colour coupling at cube scale. Compare the resulting pillar values with `CompositeMasses` and `MesonMasses`. Calculation history and competing premises are in [PILLARS.md](PILLARS.md).
