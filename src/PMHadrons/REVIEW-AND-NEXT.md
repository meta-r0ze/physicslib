# PMHadrons — open work

## Nucleon and pion dressing

- Recompute the cloud and intrinsic magnetic moments with the finely resolved, centre-of-mass-projected carrier as the source. Include recoil. The axial and pion source is the on-site spin `Σⱼ` on both walls (`PMAction.ConfinedAxialCurrent`); its value needs the carrier's size (PMAction's carrier level and radius certificate).
- Determine the Toll rule for a virtual pion pair that leaves and returns, and the Governor constraint on the nonperturbative colour coupling at cube scale. Compare the resulting pillar values with `CompositeMasses` and `MesonMasses`. Calculation history and competing premises are in [PILLARS.md](PILLARS.md).

## Weak widths and meson emission

- **One charged-current normalization.** Assemble a consistent physical partial-rate convention
  across pion, kaon and neutron channels. Reuse `ShortDistanceRunning.runningFactor_bounds`
  (`1.021178–1.021180`): the leading-log coefficient and its numerical enclosure already exist.
  `DecayInstantiation.sharedFactor` instead enforces `|V_ud|² R = 32/33`; the library proves the
  two factors differ by `4–7 × 10⁻⁵`, not that they are equal. Derive the matching and finite
  corrections needed to relate them, rather than identifying nearby values. The kaon already has
  the shared-factor construction (`kaonChannelCKM_rate`), while `KaonWidth.kaonWidthE8` and the
  exported finite lifetime still use the earlier formula. Establish how PMFlavor's charged-current
  dressing (`q² = 515/516`) enters physical rates: the catalog compares dressed `V_ud`, but these
  formulas use raw CKM magnitudes. Do not count that dressing, `32/33`, contact running or finite
  radiative terms twice. This normalization decision precedes the e8p export update.
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
- **Tau inclusive hadronic factor.** `PMElementaryParticles.TauBranching` derives the leptonic
  channels and colour count (`B_e = 1/(1 + f(r) + 3h)`); the supplied `B_e = 0.1782` requires
  `h` about 1.213 (`supplied_needs`). Derive the inclusive quark-current spectral weight, including
  strong dressing, strange-channel masses, CKM/dressing and short-distance electroweak matching,
  so the tau total lifetime has no supplied branching fraction. The target inferred from `B_e`
  is a falsification test, not a fitted value of `h`.
