import PMElementaryParticles.DoubletReflection
import PMAction.NativeDetuning

/-!
# The native chirality flip tells the up and down protocols apart

`DoubletReflection`: reflecting a colour axis fixes the reference axis and exchanges the up and
down protocols' carriers (`±2eᵢ`), so an amplitude built from the carrier geometry and the
reference *axis* cannot tell them apart. The native on-site flip `β` (`NativeDetuning`: the Weyl
word that only swaps coordinates, axes `0 ↔ 2` and `1 ↔ 3`) uses more than the axis.

* `beta_keeps_sign`: `β` preserves the doublet sign of every vector-class carrier.
* `beta_onto_reference_axis`: `β` moves a carrier on axis `2` onto the reference axis with the same
  coordinate. So the up protocol's carrier `+2e₂` goes to `+2e₀`, the neutral lepton-axis carrier,
  the reference's carrier; the down protocol's `−2e₂` goes to `−2e₀`, the electron protocol's.
* `beta_conjugates_flip2`: `β` turns the reflection of axis `2` into the reflection of axis `0`,
  which reverses the reference carrier (`flip_reverses_reference`). So the up/down reflection is
  not a symmetry of `β` events on that axis.
* `beta_conjugates_flip1`: on the other colour pair (`1 ↔ 3`) the reflection stays a reflection
  of a colour axis and keeps the reference.

**Correction to `DoubletReflection`'s reading.** "Any up/down difference is not geometric" holds
for amplitudes that do not use `β`. The on-site detuning `δ_O` is the rate of the `β` event
(`NativeDetuning.generator_split`), and through `β` the up protocol meets the reference carrier
while the down protocol meets the electron protocol's. So `δ_O` may differ between the up and down
protocols with no charge input.

**Where it acts on the wire.** `NativeDetuning.beta_crossings`: `β` moves vector-class carriers
across the reference axis and never spinor-class ones. The wire's heavy label is the vector class
(`UndetunedWall`: row `g` carries `κ_R(e g)`, and `κ_R(v) = K` is the heavy row). So among all
(protocol, label) pairs, `β` lands on the reference carrier only for the up protocol's heavy
label (`onto_reference_iff`). The data single out the same slot: the up protocol's second ratio
fits when its heavy label has its own on-site entry (`K` instead of `Kδ`), while the down and
electron protocols fit with one `δ` on all labels (PMElementaryParticles REVIEW). Why the
entry is `K` there is open.

**On the vector-class label `β` is never protocol-diagonal** (`beta_fixes_none`, `beta_involutive`).
Every vector carrier changes axis: a colour carrier goes to another colour or to the lepton axis,
a lepton-axis carrier to a colour axis. So on that label an on-site entry cannot be first order in
`β`; it comes from the round trip `β` then `β` (amplitude² over the gap of the image state). For
the up protocol's carrier on the paired axis the image is the reference carrier, a stationary
zero mode, so the gap vanishes: the round trip is resonant, and degenerate mixing gives an entry
of the order of the `β` amplitude itself, not its square over a gap.

**But colour.** The same holds off the paired axis: `β` sends a colour-`1` carrier to the same
protocol's colour-`3` carrier (axes `1 ↔ 3`), which is degenerate with it. So for both the up and
down protocols, colours `1` and `3` mix at first order into `|1⟩ ± |3⟩`, and colour `2` goes to the
lepton axis. A fixed `β` on the axis index therefore splits the colours of a quark protocol on the
vector-class label, against unbroken colour (`ReferenceStabilizer.colour_unbroken`). Before any
per-slot claim, the library must settle how the on-site `β` acts on colour: on a separate (Dirac)
index that commutes with colour, or colour-averaged. In both cases the colour-`2`/reference
resonance must be re-derived. For the spinor-class labels `β` never moves a carrier across the
reference axis (`NativeDetuning.beta_crossings`).

**And the wire's modes.** The wire's on-site `β` acts in the coordinate-odd sector
(`CarrierVacuumSector.range_iff_odd`: the even modes are excluded). There the mode of axis `i` is
the antipodal combination `|+2eᵢ⟩ − |−2eᵢ⟩`: the doublet sign is fixed by the projection, and `β`
sends the axis-`2` mode to the axis-`0` mode with no reference to sign. So the sign sensitivity
above is a statement about single carriers. It reaches the wire only if a protocol's state on the
wire keeps its sign, which the odd sector as written does not. Open: how a protocol's doublet sign
is carried on the wire (`CarrierRepresentation`'s premise that the sign is the doublet index,
against the odd-sector restriction).

**Premise to derive, and a colour test.** Candidate premise: when a label's `β` image is the
reference carrier, its on-site transition is carried by the reference-class (vector) carrier, so
its on-site entry is that carrier's amplitude `K`, not a `β` rate (`δ = u k`, node-suppressed). The
fixed `β` reaches the reference from one of the three up-protocol carriers only
(`one_colour_onto_reference`), and colour is unbroken, so each colour must get the same entry:
* colour-covariant (each colour's carrier is paired with the reference axis by its own `β`): entry
  `K` for every colour; predicted `m_c/m_t = 0.00366` (data `0.00372`, `0.98×`);
* colour-averaged (one fixed `β`, averaged over colours): entry `K/3 + 2δ/3`; predicted `0.0101`
  (`2.7×`).
Which treatment of the Dirac pairing holds is to be derived, not chosen; the data favour the
first. Numbers: corrected wire, `k = α/2`, masses at `M_Z`, `δ` fixed by `m_u/m_c`.

**Excluded: protocol-wide exclusion blocking.** Carriers never share a slot
(`CarrierStatistics.exclusion`), and the reference occupies its carrier. If `β` were blocked
whenever its image is the reference's slot, averaged over the three colour carriers, then
`δ_up : δ_down = 2/3` and `δ_e = δ_down`; data `0.18` and `0.29`. Fails.

**Candidate (not derived).** The reference is stationary and maintained (`δ_R = 0`). A `β` event
that lands on its carrier may be suppressed, giving the up protocol the smallest detuning. Data
(`u = δ_O/k`): up `11.5` < electron `18.6` < down `64.7`; up is smallest. The electron and down
protocols are each other's `β` partners; a rate proportional to the crossing fraction
(`lepton_always_crosses`, `colour_crosses_iff`: `1` against `1/3`) would give the electron the
larger detuning, the reverse of the data. Which colour axis `β` pairs with the reference axis
is the Dirac-basis choice; the statement holds for that axis.
-/

namespace PMElementaryParticles.BetaReference
open PMAction PMAction.CarrierEvents PMConstants.CarrierRepresentation

/-- The native on-site flip on the vector class. -/
def beta (v : V) : V := CarrierWeyl.lookup 0 0 v

theorem beta_keeps_sign : ∀ v : V, positive (beta v) = positive v := by decide +kernel

theorem beta_onto_reference_axis : ∀ v : V, coord (beta v) 0 = coord v 2 := by decide +kernel

theorem flip_reverses_reference (x : Fin 4 → ℤ) :
    DoubletReflection.flip 0 x 0 = -x 0 := by
  simp [DoubletReflection.flip]

theorem beta_conjugates_flip2 : ∀ v v' : V, vector v' = DoubletReflection.flip 2 (vector v) →
    vector (beta v') = DoubletReflection.flip 0 (vector (beta v)) := by decide +kernel

theorem beta_conjugates_flip1 : ∀ v v' : V, vector v' = DoubletReflection.flip 1 (vector v) →
    vector (beta v') = DoubletReflection.flip 3 (vector (beta v)) := by decide +kernel

/-- `β` lands on the reference carrier `+2e₀` exactly from the up protocol's carrier `+2e₂`. -/
theorem onto_reference_iff : ∀ v : V, coord (beta v) 0 = 2 ↔ coord v 2 = 2 := by decide +kernel

/-- Of the three up-protocol carriers (positive, off the reference axis), the fixed `β` sends
exactly one onto the reference carrier: the one on the colour axis `β` pairs with axis `0`. -/
theorem one_colour_onto_reference :
    (Finset.univ.filter (fun v : V => coord v 0 = 0 ∧ positive v = true ∧
      coord (beta v) 0 = 2)).card = 1 := by decide +kernel

theorem beta_involutive : ∀ v : V, beta (beta v) = v := by decide +kernel

/-- `β` fixes no vector-class carrier: every carrier changes axis, so on the vector-class label
`β` never maps a protocol's carrier to itself. -/
theorem beta_fixes_none : ∀ v : V, beta v ≠ v := by decide +kernel

end PMElementaryParticles.BetaReference
