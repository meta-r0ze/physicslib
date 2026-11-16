# PMHadrons — open work

## Nucleon and pion dressing

- Recompute the cloud and intrinsic magnetic moments with the finely resolved, centre-of-mass-projected carrier as the source. Include recoil. The axial and pion source is the on-site spin `Σⱼ` on both walls (`PMAction.ConfinedAxialCurrent`); its value needs the carrier's size (PMAction's carrier level and radius certificate).
- Determine the Toll rule for a virtual pion pair that leaves and returns, and the Governor constraint on the nonperturbative colour coupling at cube scale. Compare the resulting pillar values with `CompositeMasses` and `MesonMasses`. Calculation history and competing premises are in [PILLARS.md](PILLARS.md).

## Weak widths and meson emission

- Derive the low-energy axial radiative shift in neutron decay, including the nucleon low-energy constants and counterterm. Formalize the full Fermi-factor and outer-radiative integrals in Lean if tighter enclosures are needed; the external interval certificate is `tools/neutron_rc_certificate.py`.
- Explain the meson channel factor `32/33` and fix the short-distance factor and channel normalization for the kaon on the same footing as the pion.
- Derive from the line-carrier dynamics why kaon routing uses all ν channels and occupies the pion's surviving exits. Test the resulting emission count against the residual in `f_K/f_π`.
- Determine the bound-state amplitudes and physical final states needed by multibody kaon and hadronic tau widths.
- Tau hadronic factor. `PMElementaryParticles.TauBranching` derives the leptonic channels and the colour count (`B_e = 1/(1 + f(r) + 3h)`); the supplied `B_e = 0.1782` needs `h ≈ 1.213` (`supplied_needs`). Derive `h`, the strong dressing of a `d̄u` pair at the tau mass, so the tau lifetime has no supplied branching fraction.
