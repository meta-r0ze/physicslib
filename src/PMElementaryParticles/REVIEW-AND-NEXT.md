# PMElementaryParticles — open work

Done results are in [OVERVIEW](OVERVIEW.md). The wire (one light-mass form shared by every protocol)
is PMAction's; label changes are PMFlavor's.

## The protocol readout (first)

Wire inputs: `κ_R = (K, k, k)` (`PMAction.ReferenceClassHop`), other wall class-blind
(`PMAction.CarrierAdmittance`), `k/K` open (PMAction REVIEW, "Node-restoring amplitude"). The readout
on this wire is in OVERVIEW ("Protocol readout"): at the resonance `m₁ = 0` and `m₂/m₃ = √(3/2) k`
for every protocol, and the data need a heavy-label weight `s_e : s_d : s_u ≈ 1 : 3 : 13` (`k = α/2`).
Until the readout is derived, e8p's masses are the `QuarkMasses`/`LeptonMasses` tier ledgers (declared; their
e8p caveats say so). The tier ladder (`TierLedger`) is the same question in the paper's form.

- **Heavy-label weight.** Derive the heavy (label-`v`) state's upkeep per protocol,
  `s_e : s_d : s_u ≈ 1 : 3 : 13`. A charge-dependent upkeep `s ∝ e^{a Y_R}` (`Y_R = −2, −2/3, 4/3`)
  fits both ratios with one `a` on the derived wire: for `k = α/2`, `a = 0.82` (down) and `0.77` (up)
  at PDG mixed scales, `0.74` and `0.75` with `m_b`, `m_t` at their own scale (2–11% apart across
  the quark-mass choices); for `k = α` they are 7–18% apart (`tools/protocol_readout_scan.py`). So the reading passes a one-parameter
  test, better at `α/2`. Derive the upkeep and `a` (the library has no such cost yet). The
  crossing-fraction reading read colour as carrier axes and is excluded (`PMAction.ColourRegister`).
- **Mixing.** On the derived wire (OVERVIEW, "Protocol readout") neither root assignment gives the
  CKM: same root `|V_us| ≈ 0`, `|V_cb|, |V_ub| ≈ 0.009, 0.008`; different roots `|V_us| = √3/2`. With
  each protocol's flip moved off the resonance to fit its `m₁/m₂` (Light masses below), same-root
  `|V_us| ≈ 0.063`, `|V_cb| ≈ 0.007`, `|V_ub| ≈ 0.0065` (data `0.225`, `0.041`, `0.0037`). Cheap tests
  (`tools/mixing_candidates_check.py`, masses held at data): `|V_us| = 0.225` is reached by each of a
  relative flip phase between up and down (`0.49`), a light-class asymmetry `k_s/k_c ≈ 1.2` exchanged
  between up and down (the doublet reflection's `s ↔ c`), or an other-wall cycle phase or asymmetry,
  so `|V_us|` does not discriminate. `|V_cb|` stays at `0.002–0.010` under every deformation tried
  (those, the weight's placement on one or both walls, a joint phase × asymmetry fit, and `k/K` from
  `α/4` to `10α`), with `|V_cb| ≈ |V_ub|` against the data's ratio `11`. So the wire's heavy–light
  rotation is capped near `m₂/m₃`-size and treats the two light generations alike; `|V_cb|` (about
  `2 m_s/m_b`) needs a source outside the wire's mass matrices: the protocol readout.
- **Light masses.** At the resonance the lightest state is exactly massless on the full wire, not
  only at leading order (`PMAction.ExactZeroMode`), and no heavy-label weight changes that
  (`PMAction.OtherWallStationary.massless_iff`). So `m_e`, `m_u`, `m_d` come from outside the wire:
  the protocol register, or a reason the flip sits off the resonance. Numerically (derived wire,
  `k = α/2`, fitted weights) a real offset `δ = −1 + ε` reproduces each `m₁/m₂` with
  `ε ≈ 0.038 (e), 0.14 (d), 0.0024 (u)` and keeps `m₂/m₃` within 2–7%; no single law in the
  weight or charge fits those three offsets.
- **Protocol register.** Protocol identity is a separate register from the wire's spinor components
  (OVERVIEW, "Protocols are not wire modes"). Derive how a protocol couples to the wire; the partner
  (up/down, `ν`/`e`) difference and the heavy-label weight both have to enter there (the charge
  reading above is one such coupling).

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
