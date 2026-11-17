# PMHadrons — open work

Done results are in [OVERVIEW](OVERVIEW.md); the pillar calculations and their log are in
[PILLARS.md](PILLARS.md).

## Weak widths and meson emission (first)

In order: the normalization decision comes first because every rate below uses it.

- **One charged-current normalization.** Test done (`tools/charged_current_normalization.py`). Counting
  each factor once, `Γ(P → μν(γ)) = G_F² |q V|² f_P² m_P m_μ² (1 − m_μ²/m_P²)²/(8π) · (1 + δ_P)`: `G_F`
  from muon decay; PMFlavor's dressing `q² = 515/516` on colour-carrier transitions
  (`PMFlavor.DressingInheritance`); `δ_P` the full radiative correction, `δ_π = 0.0176(21)`,
  `δ_K = 0.0107(21)` (arXiv:1509.02220, supplied). In this convention the measured widths give
  `|V_ud| f_π = 127.13(13)` and `|V_us| f_K = 35.09(6)` MeV. E8: `q|V_ud| f_π = 126.83` (`−0.24%`,
  `−2.3σ`; the measurement implies `f_π = 130.58(13)` against E8 `130.275`), `q|V_us| f_K = 34.64`
  (`−1.3%`, `−7σ`; implies `f_K = 156.6`). The pion's `32/33` stands in for `|V_ud|²(1 + δ_π)` and fits
  the pion by construction; its `6·10⁻⁵` agreement with `|V_ud|² R` leaves out both the dressing and
  the long-distance part, so it does not survive the count-once rule. The derived running is the
  short-distance part of `δ`: `R − 1 = 0.0212` (`μ = m_p`, E8 `M_Z`) against the standard `0.0218`.
  Next: (1) one Lean module with this rate (supplied `δ_P`, `R` as its short-distance part) for pion
  and kaon, e8p rows re-pointed, `32/33`, `sharedFactor` and `MesonFiniteChannels`' corrected lifetime
  retired; (2) the neutron in the same convention (its `δ` is the outer plus inner correction); (3) the
  residuals are then the emission counts: `f_π` mildly (`1890`), `f_K` clearly (`1593`, the meson
  emission item below). Do not count the dressing, `R` and `δ` twice.
- **Partial, inclusive and total rates.** Define photon-inclusive channels and sum actual partial
  widths before predicting a total lifetime. `PionWidth` and `KaonWidth` supply muon-channel
  partial widths; `NeutralPionWidth` supplies the two-photon partial width. Against the frozen
  PDG inputs, the charged-pion muon-channel partial lifetime is about 26.0362 ns (total 26.033 ns),
  and the kaon muon-channel partial lifetime is about 19.478 ns (total 12.380 ns). For pi-zero,
  include Dalitz and other open channels: using the measured two-photon fraction 0.98823 only as a
  diagnostic converts a model partial lifetime of about `8.46 × 10⁻¹⁷ s` to a total of about
  `8.36 × 10⁻¹⁷ s`. Derive the branch rates rather than using that fraction as an E8 input.
  Keep the triangle-loop normalization in `NeutralPionWidth` identified as supplied until derived.
- **Channel inventory wiring.** After choosing the common convention above, make `ParticleChannels`
  consume the same corrected partial rates as the exported observables: its muon/pion entries
  still use tree-level widths and the kaon entry lacks the shared factor. Keep calibrated tau
  fractions explicit and distinguish an incomplete sum from a predicted total; zero-valued
  `.blocked` entries are unknown rates, not physically absent channels. The elementary radiative
  kernels and tau leptonic ratio belong in [PMElementaryParticles](../PMElementaryParticles/REVIEW-AND-NEXT.md).
- **Kaon multibody kinematics and amplitudes.** In `KaonSemileptonic.l3Z`, use the neutral-pion
  mass for the stated `K+ -> pi-zero l+ nu` final state; the current definition uses `pionPlus`.
  At fixed other inputs this raises the massless phase factor by about 3.7% (diagnostic, not a
  Lean bound). Give electron and muon modes their distinct massive phase spaces instead of the
  same massless rate in `ParticleChannels`. Then derive the form-factor normalization/slope,
  radiative/isospin corrections and bound-state amplitudes needed by semileptonic and
  nonleptonic kaon channels. Do not attribute the entire leading-order residual to form factors
  before fixing these kinematics.
- **Neutron low-energy matching.** Derive the axial radiative shift, including the nucleon
  low-energy constants and counterterm. Specify whether the assigned `g_A = 5/4` is a core or a
  fully strong-dressed QCD coupling before adding strong pion-cloud and electromagnetic effects;
  those are distinct corrections. Formalize the full Fermi-factor and outer-radiative integrals
  already evaluated in `tools/neutron_rc_certificate.py`. Its diagnostics move the leading-Coulomb
  result from about 923 s to about 909 s with outer radiation; better Coulomb integration alone
  cannot close the remaining gap. The published 1.4–2.6% axial-shift estimate sets an unknown
  counterterm contribution to zero; its 871–889 s diagnostic band is not a parameter-free E8
  lifetime prediction. Do not insert measured `g_A` as the derivation.
  Benchmark: [Cirigliano et al.](https://arxiv.org/pdf/2202.10439).
- **Meson emission and finite radiation.** Derive one emission-space rule for both mesons,
  reusing `EmissionSpace`'s pion cone-plus-survivors construction. Explain from line-carrier
  dynamics why kaon routing uses all nu channels and occupies the pion's surviving exits.
  `f_K/f_pi = 70/59` remains low; the usual electromagnetic difference in the kaon/pion width
  ratio is negative (about −0.69%), so adding it alone worsens the current rate-ratio deficit.
  Compute the charged/isospin and photon-inclusive matching in the same convention as the
  emission overlaps. Do not choose a nearby replacement for the count 1593 by matching data.
  Benchmark conventions: [PDG meson review](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-pseudoscalar-meson-decay-cons.pdf).
- **Tau inclusive hadronic factor.** `PMElementaryParticles.TauBranching` derives the leptonic
  channels and colour count (`B_e = 1/(1 + f(r) + 3h)`); the supplied `B_e = 0.1782` requires
  `h` about 1.213 (`supplied_needs`). Derive the inclusive quark-current spectral weight, including
  strong dressing, strange-channel masses, CKM/dressing and short-distance electroweak matching,
  so the tau total lifetime has no supplied branching fraction. The target inferred from `B_e`
  is a falsification test, not a fitted value of `h`.

## Lean organization (from the 2026-11-17 review)

- **Neutron routes.** One scored route (`NeutronContinuum`, formulas in `NeutronRate`) and the
  finite-cube comparison (`NeutronPrediction`, `BetaCalibration`), which PMAtoms uses. After the
  normalization decision, decide whether e8p keeps the finite-cube rows as labelled intermediates.
- **Meson-width conventions.** Three overlapping normalizations: the pion's `32/33`
  (`MesonFiniteChannels.pionLifetimeCorrectedSeconds`, the scored row), the shared factor
  (`DecayInstantiation`) and the derived running (`ShortDistanceRunning`). The normalization item
  above decides which survives; then keep one module for it. `MesonFiniteChannels` and
  `NeutronPrediction` also serve PMAtoms (`SpectralDecoherenceInstances`, `PersistenceComplex`,
  `SpectralMeasure`) as finite-cube instances, so their finite channels stay.

## Nucleon and pion dressing (after the weak widths)

- Recompute the cloud and intrinsic magnetic moments with the finely resolved, centre-of-mass-projected carrier as the source. Include recoil. The axial and pion source is the on-site spin `Σⱼ` on both walls (`PMAction.ConfinedAxialCurrent`); its value needs the carrier's size (PMAction's carrier level and radius certificate).
- Determine the Toll rule for a virtual pion pair that leaves and returns, and the Governor constraint on the nonperturbative colour coupling at cube scale. Compare the resulting pillar values with `CompositeMasses` and `MesonMasses`. Calculation history and competing premises are in [PILLARS.md](PILLARS.md).
- The pion-dressing numbers, threshold argument and the open capacity question formerly in
  `PION-WIP.md` are in [PILLARS.md](PILLARS.md) ("Pion dressing status").

