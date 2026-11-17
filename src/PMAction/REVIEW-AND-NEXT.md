# PMAction — open work

Checked results are in [OVERVIEW](OVERVIEW.md).

**Substrate premise** marks a supplied parameter or identification still to derive from the E8 update. **Certificate** marks an external calculation awaiting formal verification. **Route premise** marks a requirement of a particular derivation route. **Extension** marks a stronger result beyond the present theorem scope. Each current theorem states its hypotheses.

## Substrate premises

In dependency order: the first two feed `k/K`, the register and PMFlavor's charged-current readout.

- **The reference's restoring node: occupied legs, one carrier (substrate premise).** `ReferenceNode` gives `k/K = α/2` from two inputs to derive: (a) the node has legs only to occupied carrier modes (legs to all three classes would give `α/3`, `star_three`); (b) the reference is one carrier, so it occupies one class (`ReferenceClassHop`, `ReferenceRouting`, `OrientationDoublet` use it; the only other stationary option, an antisymmetric two-class reference, is excluded by the data, OVERVIEW). For (b), the argument has to come from how the reference's maintenance records it (`NativeReferenceBackground`: one common reference per payload label). Dependents: `NodeAmplitude`, `GenerationMass`, `MassInsertion`, `LightSplit`, `GenerationCurrent`, `WallHopPhase`.
- **Protocol register (substrate premise).** `ColourRegister`: colour must be a separate factor, not the carrier axes. The surviving candidate (OVERVIEW, "Protocol register candidates"): the label is the even sector of the reference's own class (stationary, `EvenComplement`; `1 + 3` about the reference's axis), and the weak doublet is a generation's two wall orientations (`PMFlavor.OrientationDoublet`). Derive (i) where the reference class's even sector sits as a factor of each generation's state, and (ii) the orientation as the doublet. The alternative, the reference class's eight carriers as an occupation register (`IndependentRegisters`), needs that register's E8 origin. Then re-derive `NativeDetuning`'s per-protocol crossing paragraph, which reads colour as axes.
- **Event clock: crossing, carrier and flip rates (substrate premise).** Derive the duration of one native event in hop-time units and the substrate tick, then the wall-crossing rate `y` and the in-wall carrier and flip rates in those units (a certain event of duration `τ` has rate `≥ π/(2τ)`, `CertainTransferRate`; turning a node admittance into a Hamiltonian rate needs the same duration). `WallGapCalibration`: the native realization, glue support and stationary reference alone admit every flip-to-crossing ratio, so a microscopic relation is needed. `SplitClockBoundary` excludes identifying the split update with one Hamiltonian exponential; compare the finite-tick update with the wall evolution on the light subspace instead. At the derived rates, certify the light-band error with `LightLeakage`.
- **Lazy or coherent flip event (substrate premise).** Economy fixes the other wall's flip on a root of `δ³ = −κ_O0κ_O1κ_O2` (`OtherWallStationary`). As the lazy `β` event it is the real root (`OtherWallFlipEvent`) with a wall-local offset that squares the mass ratios (`WallOffset`); as a coherent event it keeps the singular values but needs its identification and duration. The data favour coherent strongly (lazy gives `m₂/m₃ ≈ 2·10⁻⁵`, PMElementaryParticles OVERVIEW). Derive which the native event is (the same clock question as above).

## Extensions

- **Polarization continuum matching (extension).** Compare the normalized primitive-period response tensor (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator limits. Sharpen the lattice remainder bound enough to compare it with `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits (extension).** Establish joint-limit and operator-domain control for the integrated gauge Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and interacting-field estimates.

## Certificates

- **Carrier spectrum and radius (certificate).** Certify the lowest positive level of the full 216-dimensional operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.
