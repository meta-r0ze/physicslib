import PMElementaryParticles.ControlledGluedRegister
import PMElementaryParticles.RefreshMap
import PMElementaryParticles.VacancyProjection
import PMAction.CommonResponse
import PMKAutomaton.Interface

/-!
# Constraints on a Toll from the glued protocol label

The active channels determine the four comparison protocols. Colour relabeling
has precisely those four orbits. A reversible colour-equivariant label update
preserves the colourless sector. A fixed schedule of weak and colour relabelings,
priced by changed labels, gives both weak partners the same Toll even if the
primitive prices differ.

The root-displacement test uses every forward displacement in the reference
vector frame, so it tests the proposed event-count ladder before imposing
gauge equivariance. The algebraic tests take a strict comparison order as a
hypothesis and use no fitted masses or weights.

The last section evaluates the static hypercharge flags under the derived
Toll-to-amplitude conversion (`PMAction.TollAmplitude`), which the affine
bound does not cover.

## Readout audit notes

### Protocol Toll constraints

`ProtocolFlagCosts` derives four colour orbits on the active packet from its finite
relabelings. Any reversible colour-equivariant map on the labels preserves
the coloured and colourless sectors. A fixed word of weak and colour
relabelings charges weak partners equally when each operation charges its own
price on a changed label (`changedGateCost_weak_partners`). The proof uses the
commutation of the relabelings with the weak involution. An even reading also
ties the partners. For the comparison order `ν < e < d < u`, Lean excludes
every monotone function of a single odd scalar reading and every positive
sector factor times a sign factor.

The product of two linear overlaps with fixed references is even under the
weak toggle. Both transported labels change sign
(`overlap_product_weak_partners`). Keeping the full signed pair of overlaps
with the fixed vector `+2e₀` still gives a collision between the neutrino
and one up colour and between the electron and the corresponding down
colour on the heavy generation's two walls
(`heavy_reference_overlap_collisions`). Those inputs cannot give a strict
four-species ladder under any scalar postprocessing.

The proposed label-only chain uses a coloured-to-colourless transition, so a
reversible colour-equivariant update on the labels cannot realize it. The
unrestricted forward root-displacement graph in the vector frame also has
shortcuts (`forward_shortcuts`): every active down or electron label can
reach an up label in one displacement, and every up label can reach the
active neutrino in one. Here forward means nonnegative component on the
reference axis. These exclusions use the substrate operations and the
comparison order, with no mass values in the proof.

Comparison diagnostics are in `tools/toll_forms_check.py` and
`tools/readout_placement_check.py`. In the wire fit with `k = α/2`, the
four inferred weights are about `0.030, 0.087, 0.26, 1.14` for `ν, e, d, u`.
The neutrino target assumes a neutral mass mechanism. The fitted ladder
has a typical step factor `3.2–3.4` and also appears when only the
reference wall is weighted. Weighting only the other wall or scaling the
detuning reaches the up comparison alone in the scans. A passive node load
lowers the bare coupling (`PMAction.ReferenceNodeBoundary`), while the
charged-lepton and down comparisons need a larger effective coupling.
These are targets for a future substrate calculation of the flip coefficients.

The static hypercharge comparison gives another exact test. Take the
unchanged reference branch in `PMAction.CommonResponse` and use the
packet hypercharge transport for the other branch. The vacancy has zero
flag probability. The absolute hypercharges of down, up and electron
are in the ratio `1:2:3`. Their flag probabilities obey
`P_e + 3P_d − 2P_u = 4P_d(1 − 2P_d)² ≥ 0` at every phase
(`ProtocolFlagCosts.hyperchargeFlag_static_gap`). Every finite nonnegative
weighted sum of those flags with a common baseline therefore satisfies
`2(T_u − T_ν) ≤ (T_e − T_ν) + 3(T_d − T_ν)`
(`hyperchargeFlag_schedule_bound`).

For a common positive affine map from that Toll to the wire amplitude,
the same bound holds for the amplitudes. With a nonnegative baseline
and `s_e < s_d` it requires `s_u < 2s_d`. The nominal charged
comparison has `s_u/s_d ≈ 4.38`. An affine map to squared amplitude
likewise requires `s_u² < 2s_d²`. These tests use the charged order and
do not require a neutrino mass prediction.

The generic comparison, repair cost, and conversion from a scheduled
pulse to its wire coupling belong to PMAction. The evaluation on the
E8 protocol packet, and the test against the heavy-weight readout,
belong here. This bound covers common per-flag pricing against an
unchanged reference. A label-conditioned repair length or a joint
reference response requires its own derivation.

The conversion itself is derived in `PMAction.TollAmplitude`: a label with
Toll `T` keeps amplitude `exp(−T/2)`, which is not affine. Under it the
static flags are not bounded this way. At the steps `π/2` and `3π/2` the
electron, down and up flags are `(1, ¼, ¾)` and `(1, 1, 0)`
(`flags_quarter`, `flags_three_quarter`). Counts `w₁, w₂` give
`T_e − T_d = ¾w₁` and `T_d − T_u = w₂ − ½w₁` (`twoPhaseHyperchargeFlagCost_differences`),
the strict order `s_e < s_d < s_u` for `w₁ > 0`, `w₂ > ½w₁`
(`survival_ladder`), and `2s_d ≤ s_u` exactly when `w₂ − ½w₁ ≥ 2 log 2`
(`doubling_iff`). The steps are a witness, not a derived schedule.

One step at a time: a static step is fixed by its down flag `d`. The up
flag is `4d(1 − d)` and the electron flag `d(3 − 4d)²`, so the step adds
`8d(1 − d)(1 − 2d)` to `T_e − T_d` (positive only for `d < ½`) and
`d(4d − 3)` to `T_d − T_u` (positive only for `d > ¾`)
(`step_differences`, `step_orders_lepton`, `step_orders_quark`). No
single step orders the charged labels (`single_step_no_order`). Their
sum `16d(d − d₋)(d − d₊)`, `d∓ = (5 ∓ √5)/8`, is not positive inside
`[d₋, d₊]` (`step_charged_span`, `window_no_span`), so a schedule inside
that window gives `T_e ≤ T_u` (`window_no_ladder`). The vacancy
preparation's steps `k · 6π/5` sit exactly on the window's ends
(`fifth_root_steps`), and the charged selector's step `3π/4` has `d = ½`
(`selector_step`, `selector_in_window`).

Doublet-position readouts. A weak gate that treats the partners
differently must export the doublet position
(`RefreshMap.asymmetric_gate_records`). A static step with down flag `1`
flags down and the electron fully and up and the vacancy not at all: it
reads that bit on every static label (`full_readout`; step `3π/2`). It
adds only to `T_d − T_u`. The electron flag is `1` exactly when the down
flag is `1` or `¼` (`lepton_readout_iff`); the second is the lepton-only
readout at `π/2`, below the window (`quarter_below_window`), adding `¾`
to `T_e − T_d` and `−½` to `T_d − T_u`. These are exactly the witness
steps of `survival_ladder`.

What one charged-current event requires (`EventRequirements`). The
emitted labels depend on the parent's sign alone (`pairs_of_sign`,
`pairs_disjoint`), and no axis-only rule can choose them
(`axis_cannot_choose`): the event requires exactly the parent's doublet
bit. The quark bit is read only by the full readout (`quark_bit_iff`).
If each label pays only its own event's readout, electron and down pay
`1` and up and the vacancy `0` (`own_event_tolls`): own-event accounting
ties `e` with `d` and `u` with `ν`. An ordering needs flags a label
receives in other labels' events.

A persisting massive label is on both walls with equal weight
(`PMAction.WallRestChirality.charged_weight_half`), so its flag is the
mean of its active and static slots (`massive_flag`; the readout does not
interfere channels, `PMAction.DiagonalReadout.state_flag`). The active
doublet slot cannot read the doublet bit. The full readout `3π/2` reads
both the lepton and the quark bit (`full_reads_both`) and gives massive
flags `¾` (electron, down) and `¼` (up, vacancy) (`full_massive`). So
the doublet readouts, with Economy and both walls, separate up from down
and never the electron from down. These Tolls are generation-blind, and a
generation-blind Toll scales the wire mass by one factor and cancels from
every ratio (`uniform_weight_cancels`); only a Toll that reaches some
generations' flips matters. The light generations pass through the
reference node and the heavy one does not (`PMAction.ReferenceClassHop`);
a Toll on the node legs raises the effective heavy weight by `exp(T/2)`
(`node_toll_raises_heavy`).


-/

noncomputable section
namespace PMElementaryParticles.ProtocolFlagCosts

open PMConstants.PacketGaugeActions ProtocolInventory
open ControlledGluedRegister GluedRegister

theorem same_active_colour_orbit : ∀ c d : Channels, active c = true → active d = true →
    (baseProtocol c = baseProtocol d ↔ ∃ a b : Fin 3, permuteColour a b c = d) := by
  decide +kernel

theorem colour_fixed_iff : ∀ c : Channels,
    (∀ a b : Fin 3, permuteColour a b c = c) ↔ colourBulk c = false := by
  decide +kernel

/-- A reversible colour-equivariant update on the label alone keeps the
colourless and coloured channels separate. -/
theorem equivariant_preserves_colourBulk (f : Channels → Channels)
    (hf : Function.Injective f)
    (hc : ∀ a b c, permuteColour a b (f c) = f (permuteColour a b c)) (c : Channels) :
    colourBulk (f c) = colourBulk c := by
  have h : ((∀ a b, permuteColour a b (f c) = f c) ↔ ∀ a b, permuteColour a b c = c) := by
    constructor
    · intro h a b
      exact hf ((hc a b c).symm.trans (h a b))
    · intro h a b
      rw [hc, h a b]
  rw [colour_fixed_iff, colour_fixed_iff] at h
  cases h₁ : colourBulk (f c) <;> cases h₂ : colourBulk c <;> simp_all

/-- The relabelings already defined on the protocol packet. -/
inductive Gate where
  | weak
  | colour (a b : Fin 3)

def Gate.step : Gate → Channels → Channels
  | .weak => flipWeak
  | .colour a b => permuteColour a b

private theorem step_weak (gate : Gate) (c : Channels) :
    gate.step (flipWeak c) = flipWeak (gate.step c) := by
  cases gate with
  | weak => rfl
  | colour a b =>
    change permuteColour a b (flipWeak c) = flipWeak (permuteColour a b c)
    revert a b c
    decide +kernel

/-- Charge a primitive when it changes the incoming label. -/
def changedGateCost (price : Gate → ℝ) : List Gate → Channels → ℝ
  | [], _ => 0
  | gate :: rest, c =>
    (if gate.step c = c then 0 else price gate) + changedGateCost price rest (gate.step c)

theorem changedGateCost_weak_partners (price : Gate → ℝ) (word : List Gate) (c : Channels) :
    changedGateCost price word (flipWeak c) = changedGateCost price word c := by
  induction word generalizing c with
  | nil => rfl
  | cons gate rest ih =>
    have hinj : Function.Injective flipWeak :=
      (show Function.Involutive flipWeak from RefreshMap.two_ticks).injective
    simp [changedGateCost, step_weak, hinj.eq_iff, ih]

/-- A candidate displacement in the reference frame, with nonnegative clock component. -/
def ForwardShift (c d : Channels) : Prop :=
  ∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧ 0 ≤ root i j s t 0 ∧
    carrier 0 (labelIndex d) = carrier 0 (labelIndex c) + root i j s t

instance (c d : Channels) : Decidable (ForwardShift c d) := by
  unfold ForwardShift
  infer_instance

private def neutrino : Channels := .inr (.inr (.inl 0))
private def electron : Channels := flipWeak neutrino
private def up : Channels := .inl (0, 0)
private def down : Channels := flipWeak up

/-- The weak toggle negates both transported labels. A product of two
linear overlaps with fixed references is therefore weak-even. -/
theorem overlap_product_weak_partners (g : Fin 3) (refT refF : Wt) (c : Channels)
    (hc : active c = true) :
    dot refT (frame (wallClass g false) (labelIndex (flipWeak c))) *
      dot refF (frame (wallClass g true) (labelIndex (flipWeak c))) =
    dot refT (frame (wallClass g false) (labelIndex c)) *
      dot refF (frame (wallClass g true) (labelIndex c)) := by
  simp only [weak_label, hc, ite_true, dot, Pi.neg_apply, mul_neg,
    Finset.sum_neg_distrib, neg_mul, neg_neg]

/-- The two heavy-wall overlaps with the same fixed vector reference. -/
def heavyReferenceOverlaps (c : Channels) : ℤ × ℤ :=
  (dot (carrier 0 0) (frame (wallClass 0 false) (labelIndex c)),
   dot (carrier 0 0) (frame (wallClass 0 true) (labelIndex c)))

/-- Even retaining both signed overlaps cannot rank these channels:
the fixed-reference readout already collides before a cost is assigned. -/
theorem heavy_reference_overlap_collisions :
    heavyReferenceOverlaps neutrino = heavyReferenceOverlaps up ∧
      heavyReferenceOverlaps electron = heavyReferenceOverlaps down := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The unrestricted forward displacement graph bypasses the proposed ladder
in both directions. -/
theorem forward_shortcuts :
    (∀ c : Channels, active c = true →
      (baseProtocol c = some .electron ∨ baseProtocol c = some .down) →
      ∃ d : Channels, active d = true ∧ baseProtocol d = some .up ∧ ForwardShift c d) ∧
    (∀ c : Channels, active c = true → baseProtocol c = some .up → ForwardShift c neutrino) := by
  decide +kernel

/-- An odd scalar reading followed by a monotone map cannot produce the
comparison order on the active packet. -/
theorem no_monotone_odd_toll (f read : Channels → ℝ) (map : ℝ → ℝ)
    (hread : ∀ c, read c = map (f c)) (hmono : Monotone map)
    (hodd : ∀ c, active c = true → f (flipWeak c) = -f c) :
    ¬ (read neutrino < read electron ∧ read electron < read down ∧ read down < read up) := by
  rintro ⟨hne, hed, hdu⟩
  have reflect {a b : Channels} (h : read a < read b) : f a < f b := by
    apply lt_of_not_ge
    intro hab
    apply (not_le_of_gt h)
    simpa only [hread] using hmono hab
  have hel : f electron = -f neutrino := hodd neutrino rfl
  have hdn : f down = -f up := hodd up rfl
  linarith [reflect hne, reflect hed, reflect hdu]

/-- A positive sector factor times a sign factor gives the same ordering of
signs in both sectors. -/
theorem no_separable_toll (lepton coloured positive negative : ℝ)
    (hl : 0 < lepton) (hc : 0 < coloured) :
    ¬ (lepton * positive < lepton * negative ∧ coloured * negative < coloured * positive) := by
  rintro ⟨hl', hc'⟩
  exact (lt_of_mul_lt_mul_left hl' hl.le).not_gt (lt_of_mul_lt_mul_left hc' hc.le)

/-- Use Action's coherent flag on the packet hypercharge transport. -/
def hyperchargeFlag (t : ℝ) (c : Channels) : ℝ :=
  PMAction.InterferenceReadout.flagProbability (hypercharge t) c

theorem hyperchargeFlag_eq_cos (t : ℝ) (c : Channels) :
    hyperchargeFlag t c =
      (1 - Real.cos (t * (PMConstants.ChannelOccupancy.hyperchargeThirds c : ℝ) / 3)) / 2 := by
  rw [hyperchargeFlag, VacancyProjection.hypercharge_flag, PMAction.DiagonalReadout.flag, mul_div_assoc]

/-- The vacancy's static hypercharge makes it invisible to this flag. -/
@[simp]
theorem hyperchargeFlag_static_neutral (t : ℝ) :
    hyperchargeFlag t (opposite neutrino) = 0 := by
  norm_num [hyperchargeFlag_eq_cos, neutrino, opposite, PMConstants.ChannelOccupancy.hyperchargeThirds_apply]

/-- Up and down static hypercharges have absolute ratio two, so their
flag responses obey the same identity at every phase and every colour. -/
theorem hyperchargeFlag_quark_pair (t : ℝ) (a : Fin 3) :
    let d := hyperchargeFlag t (.inr (.inl (a, 1)))
    hyperchargeFlag t (.inr (.inl (a, 0))) = 4 * d * (1 - d) := by
  dsimp only
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply]
  push_cast
  norm_num
  rw [show -(t * 2) / 3 = -(t * 2 / 3) by ring, Real.cos_neg,
    show t * 4 / 3 = 2 * (t * 2 / 3) by ring, Real.cos_two_mul]
  ring

/-- The static electron has three times the absolute hypercharge of down.
The three flag probabilities obey this identity at every common phase. -/
theorem hyperchargeFlag_static_gap (t : ℝ) (a : Fin 3) :
    let d := hyperchargeFlag t (.inr (.inl (a, 1)))
    hyperchargeFlag t (opposite electron) + 3 * d -
      2 * hyperchargeFlag t (.inr (.inl (a, 0))) = 4 * d * (1 - 2 * d) ^ 2 := by
  dsimp only
  rw [hyperchargeFlag_quark_pair]
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply,
    electron, neutrino, flipWeak, opposite]
  push_cast
  norm_num
  rw [show -(t * 2) / 3 = -(t * 2 / 3) by ring, Real.cos_neg]
  rw [show -(t * 6) / 3 = -(3 * (t * 2 / 3)) by ring, Real.cos_neg, Real.cos_three_mul]
  ring

/-- A common floor and any finite schedule of static hypercharge flag
costs with nonnegative weights obey a joint electron/up/down bound.
The weights can include Action's per-flag repair price and multiplicity. -/
theorem hyperchargeFlag_schedule_bound {ι : Type*} [Fintype ι]
    (t w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (floor : ℝ) (a : Fin 3) :
    let score := fun c => floor + ∑ i, w i * hyperchargeFlag (t i) c
    2 * (score (.inr (.inl (a, 0))) - score (opposite neutrino)) ≤
      (score (opposite electron) - score (opposite neutrino)) +
        3 * (score (.inr (.inl (a, 1))) - score (opposite neutrino)) := by
  have hwm (k : ℝ) (f : ι → ℝ) : (∑ i, w i * (k * f i)) = k * ∑ i, w i * f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : 0 ≤ ∑ i, w i * (hyperchargeFlag (t i) (opposite electron) +
      3 * hyperchargeFlag (t i) (.inr (.inl (a, 1))) -
        2 * hyperchargeFlag (t i) (.inr (.inl (a, 0)))) := by
    apply Finset.sum_nonneg
    intro i _
    rw [hyperchargeFlag_static_gap]
    have hd : 0 ≤ hyperchargeFlag (t i) (.inr (.inl (a, 1))) := by
      rw [hyperchargeFlag_eq_cos]
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by norm_num)
    exact mul_nonneg (hw i) (mul_nonneg (mul_nonneg (by norm_num) hd) (sq_nonneg _))
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hwm] at hsum
  dsimp only
  simp only [hyperchargeFlag_static_neutral, mul_zero, Finset.sum_const_zero, add_zero,
    add_sub_cancel_left]
  exact sub_nonneg.mp hsum

/-!
# The static hypercharge Toll under the survival conversion

`ProtocolFlagCosts.hyperchargeFlag_schedule_bound` bounds every nonnegative schedule of static
hypercharge flags. With a common positive *affine* conversion to the wire amplitude that bound
forces `s_u < 2 s_d`. `PMAction.TollAmplitude` derives the conversion instead: a label with Toll
`T` keeps amplitude `exp(−T/2)`, which is not affine (`TollAmplitude.no_affine_form`). This
section evaluates the static flags under that conversion.

* `flags_quarter`, `flags_three_quarter`: at the hypercharge steps `π/2` and `3π/2` the static
  electron, down and up flags are `(1, ¼, ¾)` and `(1, 1, 0)`. The vacancy flag is zero at
  every step (`ProtocolFlagCosts.hyperchargeFlag_static_neutral`).
* `twoPhaseHyperchargeFlagCost_differences`: with counts `w₁, w₂` at those steps,
  `T_e − T_d = ¾ w₁` and `T_d − T_u = w₂ − ½ w₁`.
* `survival_ladder`: for `w₁ > 0` and `w₂ > ½ w₁` the amplitudes are strictly ordered,
  `s_e < s_d < s_u`, in every colour.
* `doubling_iff`: `2 s_d ≤ s_u` exactly when `w₂ − ½ w₁ ≥ 2 log 2`. So the ratio the affine
  conversion excludes is an ordinary schedule condition here.

The steps and counts are not derived. This section shows only that the static flags with the
derived conversion admit the charged order and any ratio size; the schedule remains open.
-/
section Survival
open PMAction.TollAmplitude Real

/-- The static down slot of colour `a`. -/
abbrev downStatic (a : Fin 3) : Channels := .inr (.inl (a, 1))

/-- The static up slot of colour `a`. -/
abbrev upStatic (a : Fin 3) : Channels := .inr (.inl (a, 0))

/-- The static electron slot. -/
abbrev electronStatic : Channels := opposite electron

/-- The static vacancy slot. -/
abbrev neutrinoStatic : Channels := opposite neutrino

/-- Static electron, down and up flags at the step `π/2`. -/
theorem flags_quarter (a : Fin 3) :
    hyperchargeFlag (π / 2) (opposite electron) = 1 ∧
    hyperchargeFlag (π / 2) (downStatic a) = 1 / 4 ∧
    hyperchargeFlag (π / 2) (upStatic a) = 3 / 4 := by
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply,
    electron, neutrino, flipWeak, opposite]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · rw [show π / 2 * -6 / 3 = -π by ring, cos_neg, cos_pi]; norm_num
  · rw [show π / 2 * -2 / 3 = -(π / 3) by ring, cos_neg, cos_pi_div_three]; norm_num
  · rw [show π / 2 * 4 / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]; norm_num

/-- Static electron, down and up flags at the step `3π/2`. -/
theorem flags_three_quarter (a : Fin 3) :
    hyperchargeFlag (3 * π / 2) (opposite electron) = 1 ∧
    hyperchargeFlag (3 * π / 2) (downStatic a) = 1 ∧
    hyperchargeFlag (3 * π / 2) (upStatic a) = 0 := by
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply,
    electron, neutrino, flipWeak, opposite]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · rw [show 3 * π / 2 * -6 / 3 = -π - 2 * π by ring, cos_sub_two_pi, cos_neg, cos_pi]
    norm_num
  · rw [show 3 * π / 2 * -2 / 3 = -π by ring, cos_neg, cos_pi]; norm_num
  · rw [show 3 * π / 2 * 4 / 3 = 2 * π by ring, cos_two_pi]; norm_num

/-- The Toll of a channel under `w₁` comparisons at `π/2` and `w₂` at `3π/2`. -/
def twoPhaseHyperchargeFlagCost (w₁ w₂ : ℝ) (c : Channels) : ℝ :=
  w₁ * hyperchargeFlag (π / 2) c + w₂ * hyperchargeFlag (3 * π / 2) c

/-- **The Toll differences.** -/
theorem twoPhaseHyperchargeFlagCost_differences (w₁ w₂ : ℝ) (a : Fin 3) :
    twoPhaseHyperchargeFlagCost w₁ w₂ (opposite electron) - twoPhaseHyperchargeFlagCost w₁ w₂ (downStatic a) = 3 / 4 * w₁ ∧
    twoPhaseHyperchargeFlagCost w₁ w₂ (downStatic a) - twoPhaseHyperchargeFlagCost w₁ w₂ (upStatic a) = w₂ - w₁ / 2 := by
  obtain ⟨e1, d1, u1⟩ := flags_quarter a
  obtain ⟨e2, d2, u2⟩ := flags_three_quarter a
  simp only [twoPhaseHyperchargeFlagCost, e1, d1, u1, e2, d2, u2]
  constructor <;> ring

/-- **The charged order.** -/
theorem survival_ladder {w₁ w₂ : ℝ} (h₁ : 0 < w₁) (h₂ : w₁ / 2 < w₂) (a : Fin 3) :
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (twoPhaseHyperchargeFlagCost w₁ w₂ (opposite electron)) <
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (twoPhaseHyperchargeFlagCost w₁ w₂ (downStatic a)) ∧
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (twoPhaseHyperchargeFlagCost w₁ w₂ (downStatic a)) <
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (twoPhaseHyperchargeFlagCost w₁ w₂ (upStatic a)) := by
  obtain ⟨hed, hdu⟩ := twoPhaseHyperchargeFlagCost_differences w₁ w₂ a
  constructor <;> rw [wireAmplitude_lt_iff] <;> linarith

/-- **Doubling is a schedule condition.** -/
theorem doubling_iff (w₁ w₂ : ℝ) (a : Fin 3) :
    2 * PersistenceMechanics.EffectiveAction.attenuationWeight 1 (twoPhaseHyperchargeFlagCost w₁ w₂ (downStatic a)) ≤
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (twoPhaseHyperchargeFlagCost w₁ w₂ (upStatic a)) ↔ 2 * log 2 ≤ w₂ - w₁ / 2 := by
  rw [ratio_ge_iff (by norm_num : (0 : ℝ) < 2), (twoPhaseHyperchargeFlagCost_differences w₁ w₂ a).2]

/-! ### One comparison step

Every static hypercharge step is fixed by its down flag `d`: the up flag is `4d(1 − d)`
(`hyperchargeFlag_quark_pair`) and the electron flag `d(3 − 4d)²`. So each step adds
`8d(1 − d)(1 − 2d)` to `T_e − T_d` and `d(4d − 3)` to `T_d − T_u` (`step_differences`).
The first is positive only for `d < ½`, the second only for `d > ¾` (`step_orders_lepton`,
`step_orders_quark`). So no single step, however often repeated, orders the three charged labels
(`single_step_no_order`); a schedule needs one step with `d < ½` and another with `d > ¾`.

The two hypercharge steps already selected in the library: the charged selector's `3π/4`
(`ChargedInsertion`) has `d = ½`. Electron and down tie, and up flags more (`selector_step_flags`).
The vacancy preparation's `6π/5` (`VacancyPreparation`) has `d = (5 + √5)/8 > ¾` and orders down above up
but electron below down (`vacancy_step`). A step with `d < ½` is still to be found natively.
-/

/-- The down flag lies in `[0, 1]`. -/
theorem down_flag_bounds (t : ℝ) (a : Fin 3) :
    0 ≤ hyperchargeFlag t (downStatic a) ∧ hyperchargeFlag t (downStatic a) ≤ 1 := by
  rw [hyperchargeFlag_eq_cos]
  constructor <;> linarith [Real.cos_le_one (t * (PMConstants.ChannelOccupancy.hyperchargeThirds (downStatic a) : ℝ) / 3), Real.neg_one_le_cos (t * (PMConstants.ChannelOccupancy.hyperchargeThirds (downStatic a) : ℝ) / 3)]

/-- **Each step's Toll differences depend only on its down flag.** -/
theorem step_differences (t : ℝ) (a : Fin 3) :
    let d := hyperchargeFlag t (downStatic a)
    hyperchargeFlag t (opposite electron) - d = 8 * d * (1 - d) * (1 - 2 * d) ∧
    d - hyperchargeFlag t (upStatic a) = d * (4 * d - 3) := by
  have hq := hyperchargeFlag_quark_pair t a
  have hg := hyperchargeFlag_static_gap t a
  dsimp only at hq hg ⊢
  constructor
  · have : hyperchargeFlag t (opposite electron) =
        4 * hyperchargeFlag t (downStatic a) * (1 - 2 * hyperchargeFlag t (downStatic a)) ^ 2
          - 3 * hyperchargeFlag t (downStatic a) + 2 * hyperchargeFlag t (upStatic a) := by
      simp only [downStatic, upStatic] at *; linarith
    rw [this, show hyperchargeFlag t (upStatic a) = _ from hq]; ring
  · rw [show hyperchargeFlag t (upStatic a) = _ from hq]; ring

/-- A step adds to `T_e − T_d` exactly when its down flag is in `(0, ½)`. -/
theorem step_orders_lepton (t : ℝ) (a : Fin 3) :
    hyperchargeFlag t (downStatic a) < hyperchargeFlag t (opposite electron) ↔
      0 < hyperchargeFlag t (downStatic a) ∧ hyperchargeFlag t (downStatic a) < 1 / 2 := by
  obtain ⟨he, -⟩ := step_differences t a
  obtain ⟨h0, h1⟩ := down_flag_bounds t a
  set d := hyperchargeFlag t (downStatic a)
  rw [← sub_pos, he]
  constructor
  · intro h
    rcases eq_or_lt_of_le h1 with h1 | h1
    · rw [h1] at h; norm_num at h
    rcases eq_or_lt_of_le h0 with h0 | h0
    · rw [← h0] at h; norm_num at h
    refine ⟨h0, ?_⟩
    by_contra hc
    push Not at hc
    nlinarith [mul_pos h0 (sub_pos.mpr h1)]
  · rintro ⟨h0, h2⟩
    have : 0 < 1 - d := by linarith
    have : 0 < 1 - 2 * d := by linarith
    positivity

/-- A step adds to `T_d − T_u` exactly when its down flag exceeds `¾`. -/
theorem step_orders_quark (t : ℝ) (a : Fin 3) :
    hyperchargeFlag t (upStatic a) < hyperchargeFlag t (downStatic a) ↔
      3 / 4 < hyperchargeFlag t (downStatic a) := by
  obtain ⟨-, hq⟩ := step_differences t a
  obtain ⟨h0, -⟩ := down_flag_bounds t a
  set d := hyperchargeFlag t (downStatic a)
  rw [← sub_pos, hq]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    have : 0 < d := by linarith
    nlinarith

/-- **No single step orders the charged labels.** -/
theorem single_step_no_order (t : ℝ) (a : Fin 3) :
    ¬ (hyperchargeFlag t (downStatic a) < hyperchargeFlag t (opposite electron) ∧
      hyperchargeFlag t (upStatic a) < hyperchargeFlag t (downStatic a)) := by
  rintro ⟨h1, h2⟩
  have := ((step_orders_lepton t a).mp h1).2
  have := (step_orders_quark t a).mp h2
  linarith

/-- The charged selector's step `3π/4` has down flag `½`. -/
theorem selector_step (a : Fin 3) : hyperchargeFlag (3 * π / 4) (downStatic a) = 1 / 2 := by
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply, downStatic]
  push_cast
  rw [show 3 * π / 4 * -2 / 3 = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  norm_num

/-- Vacancy-relative flags of the uncorrected selector transport. These are
probabilities of a flag in one comparison, independent of the colour. -/
theorem selector_step_flags (a : Fin 3) :
    hyperchargeFlag (3 * π / 4) electronStatic = 1 / 2 ∧
      hyperchargeFlag (3 * π / 4) (downStatic a) = 1 / 2 ∧
      hyperchargeFlag (3 * π / 4) (upStatic a) = 1 := by
  have hd := selector_step a
  obtain ⟨he, hu⟩ := step_differences (3 * π / 4) a
  rw [hd] at he hu
  norm_num at he hu
  exact ⟨by linarith, hd, by linarith⟩

/-- With a supplied price for the single uncompensated comparison, the
relative amplitude for a half flag is `α` exactly at this price. -/
theorem selector_half_flag_weight_iff (α w : ℝ) (hα : 0 < α) :
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (w / 2) = α ↔ w = 4 * log (1 / α) := by
  calc
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (w / 2) = α ↔ exp (-(w / 2) / 2) = exp (log α) := by
      rw [exp_log hα, PersistenceMechanics.EffectiveAction.attenuationWeight, one_mul]
    _ ↔ w = 4 * log (1 / α) := by
      rw [exp_eq_exp, log_div one_ne_zero hα.ne', log_one]
      constructor <;> intro h <;> linarith

/-- The vacancy preparation's step `6π/5` has down flag `(5 + √5)/8 > ¾`. -/
theorem vacancy_step (a : Fin 3) :
    hyperchargeFlag (6 * π / 5) (downStatic a) = (5 + √5) / 8 ∧
      3 / 4 < hyperchargeFlag (6 * π / 5) (downStatic a) := by
  have h : hyperchargeFlag (6 * π / 5) (downStatic a) = (5 + √5) / 8 := by
    simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply, downStatic]
    push_cast
    rw [show 6 * π / 5 * -2 / 3 = -(π - π / 5) by ring, Real.cos_neg, Real.cos_pi_sub,
      Real.cos_pi_div_five]
    ring
  refine ⟨h, ?_⟩
  rw [h]
  have : (1 : ℝ) < √5 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ### The fifth-root window

Per step, `T_e − T_u` grows by `16d(d − d₋)(d − d₊)` with `d∓ = (5 ∓ √5)/8`
(`step_charged_span`). It is not positive for `d₋ ≤ d ≤ d₊` (`window_no_span`). So a schedule
whose every step has its down flag in that window gives `T_e ≤ T_u`: the electron is never
lighter than up (`window_no_ladder`). The window's ends are exactly the flags of the vacancy
preparation's steps `k · 6π/5`, `k = 1, …, 4` (`fifth_root_steps`), and the charged selector's
`½` lies inside it. So no counts on the steps the library has selected so far order the charged
labels. A ladder needs at least one step with `d < (5 − √5)/8` or `d > (5 + √5)/8`.
-/

/-- The lower end of the window, `(5 − √5)/8 = sin²(π/5)`. -/
def dLow : ℝ := (5 - √5) / 8

/-- The upper end of the window, `(5 + √5)/8 = sin²(2π/5)`. -/
def dHigh : ℝ := (5 + √5) / 8

/-- **The charged span of one step.** -/
theorem step_charged_span (t : ℝ) (a : Fin 3) :
    let d := hyperchargeFlag t (downStatic a)
    hyperchargeFlag t (opposite electron) - hyperchargeFlag t (upStatic a) =
      16 * d * (d - dLow) * (d - dHigh) := by
  obtain ⟨he, hq⟩ := step_differences t a
  dsimp only at he hq ⊢
  set D := hyperchargeFlag t (downStatic a)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have : hyperchargeFlag t (opposite electron) - hyperchargeFlag t (upStatic a) =
      (hyperchargeFlag t (opposite electron) - D) + (D - hyperchargeFlag t (upStatic a)) := by ring
  rw [this, he, hq, dLow, dHigh]
  linear_combination (D / 4) * h5

/-- Inside the window a step does not raise the electron's Toll above up's. -/
theorem window_no_span (t : ℝ) (a : Fin 3)
    (hlo : dLow ≤ hyperchargeFlag t (downStatic a))
    (hhi : hyperchargeFlag t (downStatic a) ≤ dHigh) :
    hyperchargeFlag t (opposite electron) ≤ hyperchargeFlag t (upStatic a) := by
  have h := step_charged_span t a
  obtain ⟨h0, -⟩ := down_flag_bounds t a
  dsimp only at h
  have : 16 * hyperchargeFlag t (downStatic a) * (hyperchargeFlag t (downStatic a) - dLow) *
      (hyperchargeFlag t (downStatic a) - dHigh) ≤ 0 := by
    have h1 : 0 ≤ 16 * hyperchargeFlag t (downStatic a) *
        (hyperchargeFlag t (downStatic a) - dLow) := by
      have := sub_nonneg.mpr hlo; positivity
    exact mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)
  linarith

/-- **A schedule inside the window cannot make the electron lighter than up.** -/
theorem window_no_ladder {ι : Type*} [Fintype ι] (t w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : Fin 3)
    (hwin : ∀ i, dLow ≤ hyperchargeFlag (t i) (downStatic a) ∧
      hyperchargeFlag (t i) (downStatic a) ≤ dHigh) :
    ∑ i, w i * hyperchargeFlag (t i) (opposite electron) ≤
      ∑ i, w i * hyperchargeFlag (t i) (upStatic a) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (window_no_span (t i) a (hwin i).1 (hwin i).2) (hw i)

private lemma cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- **The vacancy preparation's steps sit on the window's ends.** At `k · 6π/5` the down flag
is `d₊` for `k = 1, 4` and `d₋` for `k = 2, 3`. -/
theorem fifth_root_steps (a : Fin 3) :
    hyperchargeFlag (6 * π / 5) (downStatic a) = dHigh ∧
    hyperchargeFlag (2 * (6 * π / 5)) (downStatic a) = dLow ∧
    hyperchargeFlag (3 * (6 * π / 5)) (downStatic a) = dLow ∧
    hyperchargeFlag (4 * (6 * π / 5)) (downStatic a) = dHigh := by
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.hyperchargeThirds_apply, downStatic, dLow, dHigh]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 6 * π / 5 * -2 / 3 = -(π - π / 5) by ring, Real.cos_neg, Real.cos_pi_sub,
      Real.cos_pi_div_five]; ring
  · rw [show 2 * (6 * π / 5) * -2 / 3 = 2 * π / 5 - 2 * π by ring, Real.cos_sub_two_pi,
      cos_two_pi_div_five]; ring
  · rw [show 3 * (6 * π / 5) * -2 / 3 = -(2 * π / 5 + 2 * π) by ring, Real.cos_neg,
      Real.cos_add_two_pi, cos_two_pi_div_five]; ring
  · rw [show 4 * (6 * π / 5) * -2 / 3 = (π - π / 5) - 2 * π - 2 * π by ring,
      Real.cos_sub_two_pi, Real.cos_sub_two_pi, Real.cos_pi_sub, Real.cos_pi_div_five]; ring

/-- The charged selector's flag `½` lies inside the window. -/
theorem selector_in_window : dLow ≤ 1 / 2 ∧ (1 : ℝ) / 2 ≤ dHigh := by
  have h1 : (1 : ℝ) ≤ √5 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  constructor <;> simp only [dLow, dHigh] <;> linarith

/-! ### Doublet-position readouts

A reversible weak gate that treats the partners differently must export the doublet position
(`RefreshMap.asymmetric_gate_records`, `CoherentGate.unequal_needs_orthogonal`). On the static
wall a hypercharge comparison reads that bit exactly when its flag is `0` on up and the vacancy
and `1` on down and the electron. That happens exactly when the down flag is `1`
(`full_readout`; the vacancy flag is always `0`). Such a step adds `1` to `T_d − T_u` and
nothing to `T_e − T_d`. A step that reads the lepton bit alone (electron flag `1`) has down flag
`1` or `¼` (`lepton_readout_iff`). The second, `π/2` (`flags_quarter`), lies below the
fifth-root window (`quarter_below_window`) and adds `¾` to `T_e − T_d` and `−½` to
`T_d − T_u`. So the two doublet readouts are exactly the steps of the witness schedule:
`n_L` lepton readouts and `n_Q` full readouts give `T_e − T_d = ¾ n_L` and
`T_d − T_u = n_Q − ½ n_L` (`twoPhaseHyperchargeFlagCost_differences`). The counts are not derived.
-/

/-- **The full doublet readout.** A step with down flag `1` flags down and the electron fully
and leaves up and the vacancy unflagged. -/
theorem full_readout (t : ℝ) (a : Fin 3) (h : hyperchargeFlag t (downStatic a) = 1) :
    hyperchargeFlag t (opposite electron) = 1 ∧ hyperchargeFlag t (upStatic a) = 0 ∧
      hyperchargeFlag t (opposite neutrino) = 0 := by
  obtain ⟨he, hq⟩ := step_differences t a
  rw [h] at he hq
  refine ⟨by linarith, by linarith, hyperchargeFlag_static_neutral t⟩

/-- **Lepton readouts.** The electron flag is `1` exactly when the down flag is `1` or `¼`. -/
theorem lepton_readout_iff (t : ℝ) (a : Fin 3) :
    hyperchargeFlag t (opposite electron) = 1 ↔
      hyperchargeFlag t (downStatic a) = 1 ∨ hyperchargeFlag t (downStatic a) = 1 / 4 := by
  obtain ⟨he, -⟩ := step_differences t a
  set D := hyperchargeFlag t (downStatic a)
  have hfe : hyperchargeFlag t (opposite electron) = D * (3 - 4 * D) ^ 2 := by linarith
  rw [hfe]
  constructor
  · intro h
    have : (D - 1) * (4 * D - 1) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1; linarith
  · rintro (h | h) <;> rw [h] <;> norm_num

/-- The lepton-only readout lies below the window. -/
theorem quarter_below_window : (1 : ℝ) / 4 < dLow := by
  have : √5 < 3 := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simp only [dLow]; linarith

end Survival

end PMElementaryParticles.ProtocolFlagCosts
