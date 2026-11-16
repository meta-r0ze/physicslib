# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md).

**Substrate premise** marks a supplied parameter or identification still to derive from the E8 update. **Certificate** marks an external calculation awaiting formal verification. **Route premise** marks a requirement of a particular derivation route. **Extension** marks a stronger result beyond the present theorem scope. Each current theorem states its hypotheses.

## Substrate premises

- **Generation hierarchy source (substrate premise).** `CarrierAdmittance`: conserving exchanges are scalar on the reference and the native exchange is the same for every class, so `κ_R` and `κ_O` are class-blind unless an event weight breaks triality. Then the light factor at the resonance has singular values `0, √3λ, √3λ` (one massless state, a degenerate pair), and `NodeAmplitude`'s `K = 1`, `k = α/2` is withdrawn for the wire. Find what breaks the three classes' symmetry on the wire (the class the reference occupies, the crossing `y` per class, or the even-complement price), or show the splitting comes from the protocol register. Dependents in PMAction: `NodeAmplitude`, `GenerationMass`, `MassInsertion`, `LightSplit`, `GenerationCurrent`, `WallHopPhase`.
- **Event clock: crossing, carrier and flip rates (substrate premise).** Derive the duration of one native event in hop-time units and the substrate tick, then the wall-crossing rate `y` and the in-wall carrier and flip rates in those units (a certain event of duration `τ` has rate `≥ π/(2τ)`, `CertainTransferRate`; turning a node admittance into a Hamiltonian rate needs the same duration). `WallGapCalibration`: the native realization, glue support and stationary reference alone admit every flip-to-crossing ratio, so a microscopic relation is needed. `SplitClockBoundary` excludes identifying the split update with one Hamiltonian exponential; compare the finite-tick update with the wall evolution on the light subspace instead. At the derived rates, certify the light-band error with `LightLeakage`.
- **Lazy or coherent flip event (substrate premise).** Economy fixes the other wall's flip on a root of `δ³ = −κ_O0κ_O1κ_O2` (`OtherWallStationary`). As the lazy `β` event it is the real root, realized by attempt probability `(1 − e^{−|δ|})/2` (`OtherWallFlipEvent`), with a wall-local offset that turns the light masses into `s²/c'` (`WallOffset`); as a coherent event it keeps the singular values `s` but needs its identification and duration. Derive which the native event is (the same clock question as above).
- **Even-complement realization and price (route premise).** Derive the invisible-sector action of the full physical split update, including compensation between coherent gate factors. Determine whether its admitted completions include the identity completion and whether microscopic event costs assign a positive price to invisible-mode squared displacement.
- **Colour register (substrate premise).** `ColourRegister`: colour that commutes with `β` and the `αⱼ` cannot act on the carrier axes, so it is a separate factor. Construct that factor natively (which E8 structure carries the three colours). `NativeDetuning`'s per-protocol crossing paragraph reads colour as axes and needs re-deriving with it.

## Extensions

- **Polarization continuum matching (extension).** Compare the normalized primitive-period response tensor (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator limits. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits (extension).** Establish joint-limit and operator-domain control for the integrated gauge Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and interacting-field estimates.

## Certificates

- **Carrier spectrum and radius (certificate).** Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
