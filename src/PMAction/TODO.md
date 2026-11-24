# PMAction — open work

Repo-wide named premises are listed once in [SCOPE](../../SCOPE.md#named-premises).

Checked results are in [OVERVIEW](OVERVIEW.md). The shared clock, record and
handoff tasks are in the [transport review](../PMKAutomaton/TODO.md).

**Extension** marks a stronger result beyond the present theorem scope. **Certificate** marks an
external calculation awaiting formal verification. Each current theorem states its hypotheses.

## Scope premises

- **Spacetime and amplitude structure.** Derive the Lorentzian signature and complex amplitude from
  substrate persistence instead of entering them as modelling premises; the finite gauge measure has
  site-reflection positivity. Blocker: no selection principle fixes the signature or complex structure,
  and the MassGap branch covers only the distinction substrate, not a continuum relativistic gauge
  theory (see [MassGap/README.md](MassGap/README.md)).

## Extensions

- **Polarization continuum matching.** Compare the normalized primitive-period response tensor
  (`PrimitivePolarization`) with the continuum shell through its transverse large-volume and regulator
  limits. Sharpen the lattice remainder bound enough to compare it with
  `tools/lattice_polarization_check.py` at fixed spacing.
- **Further field limits.** Establish joint-limit and operator-domain control for the integrated gauge
  Hessian, mode and domain control for the real-space PDE limit, the full real-space fermion field and
  interacting-field estimates.

## Certificates

- **Carrier spectrum and radius.** Certify the lowest positive level of the full 216-dimensional
  operator and the spin-up rms radius in Lean. The existing exact subspace and radius calculations are
  in `tools/carrier_mode_exact.py` and `tools/carrier_rms_certificate.py`.

## Generation masses

The generation-mass modules (`MassInsertion`, `GenerationMass`, `CompositeMass`, `CyclicSeesaw`,
`GenerationParity`, `GenerationOrientation`) point here.

Settled, so not open: where the mass sits. The crossing within one convention is one-directional,
never Hermitian (`GenerationParity`), and the seesaw on the crossing alone gives three equal masses
(`CyclicSeesaw.gram_equal`), so the crossing carries no hierarchy. The generation-diagonal mass is
the single-wall carrier of the label class in the on-site chirality-flip slot, a correction to `δ`
(`CompositeMass`): its diagonal is linear in the carrier amplitudes (`composite_diag`), and for a
class-independent crossing the three masses differ only by those amplitudes
(`diag_class_independent`).

- **Carrier amplitude per class.** On the wire, the reference's class and stationarity distinguish
  the direct insertion from the two restoring insertions (`PMKAutomaton.Machine.ReferenceClassHop`).
  `ReferenceNode` derives `α/2` for a conserving two-leg node. `CertainTransferRate` derives
  principal pulse areas and their rate ratio for supplied weights and durations. The open input is
  the admitted pulse for each insertion, its retained output, and its duration and normalization
  in the same clock units as the gapped crossing.
- **Split the suppressed pair.** The two node-crossing classes share one amplitude, so
  `CompositeMass.diag_class_independent` makes them degenerate. A further effect must split them
  (`PMFlavor.ExchangeChirality`: the weak wall separates the two classes). Comparisons belong in
  e8p; species names belong in `PMElementaryParticles`.
- **Regime and the spectrum.** `WireResonanceSpectrum` certifies the bare masses and the cubic
  with a real static offset. `WallSeesawAccuracy.full_energy_near_schur` controls the error for
  each full light energy when the crossing is common and the two coupling norms are bounded.
  The exact test `full_energy_iff` also gives a reduced determinant for root isolation.
  Derive the coupling bounds from the admitted rates and match the light modes in order. Retain the
  cyclic terms in the spectrum and use the resulting eigenvectors for the PMFlavor rotation.
- **Single crossing at a fixed class.** Whether `GenerationOrientation.single_crossing_unequal`
  is a physical move.
