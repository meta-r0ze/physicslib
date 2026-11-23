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

- **Carrier amplitude per class.** One amplitude per class sets the three masses. The label class
  of one generation is the reference's class, whose displacement can avoid the reference axis; every
  displacement of the other two classes touches it (`PMFlavor.ExchangeAxis` as carrier counts), so
  those two pass the reference node. Derive the amplitude of a displacement that crosses the node,
  with the leg weight from the handoff price (`PMConstants.HandoffAdmittance.closure_one_price`,
  one leg or two, `PMFlavor.NodeElimination`). Until then the hierarchy has one free amplitude.
- **Split the suppressed pair.** The two node-crossing classes share one amplitude, so
  `CompositeMass.diag_class_independent` makes them degenerate. A further effect must split them
  (`PMFlavor.ExchangeChirality`: the weak wall separates the two classes). Comparisons belong in
  e8p; species names belong in `PMElementaryParticles`.
- **Regime and the off-diagonal terms.** `CompositeMass.composite_expansion` keeps two cyclic
  terms, of relative size `δ/κ`. Fix the regime (`|κ|` against `|δ|`) and read those terms as a
  mixing prediction (`PMFlavor`).
- **Single crossing at a fixed class.** Whether `GenerationOrientation.single_crossing_unequal`
  is a physical move.
