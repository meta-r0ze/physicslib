# PMElementaryParticles — open work

Done results are in [OVERVIEW](OVERVIEW.md). The wire (one light-mass form shared by every protocol)
is PMAction's; label changes are PMFlavor's.

## The protocol readout (first)

The wire inputs `K = 1`, `k = α/2` are withdrawn (`PMAction.CarrierAdmittance`: natively the
three carrier classes have the same exchange, so the bare wire at the resonance gives one massless
state and a degenerate pair; PMAction REVIEW, "Generation hierarchy source"). The numbers below use
the withdrawn inputs. The results so far are in OVERVIEW ("Protocol readout"): the wire's flip sits on the cycle resonance
(`PMAction.OtherWallStationary`), where the wire gives `m₂/m₃ ≈ 0.023` for every protocol, and the
data need one weight `w` on the heavy label per protocol, `w_e : w_d : w_u ≈ 1 : 3 : 16–18`. Until the
readout is derived, e8p's masses are the `QuarkMasses`/`LeptonMasses` tier ledgers (declared; their
e8p caveats say so). The tier ladder (`TierLedger`) is the same question in the paper's form.

- **Heavy-label weight.** Derive the heavy (vector-class) state's upkeep per protocol. The reading
  that fits all three is a charge-dependent cost, `w ∝ e^{(c/2) Y_R}` with `c ≈ 1.7` (the library has no
  such cost yet); the crossing-fraction reading read colour as carrier axes and is excluded
  (`PMAction.ColourRegister`).
- **Light masses.** At the resonance the light mass is zero; derive the light masses as corrections.
  As the lazy `β` event every protocol takes the real root (`PMAction.OtherWallFlipEvent`), so flavour
  mixing has to come from the readout, and the lazy event's offset changes the mass law to `s²/c'`
  (PMAction REVIEW, "Lazy or coherent flip event").
- **Protocol register.** Protocol identity is a separate register from the wire's spinor components
  (OVERVIEW, "Protocols are not wire modes"). Derive how a protocol couples to the wire; the partner
  (up/down, `ν`/`e`) difference and the heavy-label weight both have to enter there (the charge
  reading above is one such coupling).

## Mathematical gap (Lean)

**Three-body phase-space factorization.** Derived from Lebesgue measure: the daughter's measure
`P/(4π²)` (`ElectronMeasure.width_from_lebesgue`), the pair's two-body volume `1/(8π)` at rest
(`PolarMeasure`), the boost invariance of each massless leg's measure (`NullBoost`), and the pair at
fixed total momentum in shell coordinates (`PairShell.shell_integral`: for every `g`,
`∫ g(k) d³k/(|k||P⃗ − k|) = ∫ (sin ν/2) g(Ψ(E, ν, φ)) dE dν dφ`, so the energy delta is the coordinate
`E` and the density at fixed `E` is the rest-frame solid angle). Open: the last link, that the
`(ν, φ)` average of the pair tensor `k^μ k̄^ν` at fixed `E` equals `PairTransport`'s transported
average (the boost along `e₀` with `γ = E/M` maps the rest-frame pair to `Ψ`); then
`MassiveDaughterSpectrum.pair_density` follows rather than being assembled.

## Other open work

- **Final channels.** `PMAction.NativeExternal` makes `AmplitudeTrace`'s spinors the native wall
  eigenmodes and its bilinears the native charged current. Identify which protocol channels are the
  final states of each decay (and so the first row's external states).
- **Radiative factor.** `MuonLifetimeCorrected` supplies the one-loop QED factor; derive it as the soft
  photon dressing of the charged daughter.
- **First-row deficit as leakage** (`0.0016 ± 0.0007`). `PMAction.WallCurrentWeights`: the full
  charged projector keeps a gapped component, so total gapped weight is not a row deficit; the row
  needs the external-state and final-channel readout (PMAction REVIEW, native current to external
  amplitude). `PMAction.WallGapCalibration`: the library admits every flip-to-gap ratio, so the size
  waits on PMAction's crossing-to-flip calibration.
