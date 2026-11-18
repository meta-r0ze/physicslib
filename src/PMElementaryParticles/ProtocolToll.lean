import PMElementaryParticles.ControlledGluedRegister
import PMElementaryParticles.RefreshMap
import PMElementaryParticles.VacancyProjection
import PMAction.CommonResponse
import PMAction.TollAmplitude

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
-/

noncomputable section
namespace PMElementaryParticles.ProtocolToll

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
def eventToll (price : Gate → ℝ) : List Gate → Channels → ℝ
  | [], _ => 0
  | gate :: rest, c =>
    (if gate.step c = c then 0 else price gate) + eventToll price rest (gate.step c)

theorem eventToll_weak_partners (price : Gate → ℝ) (word : List Gate) (c : Channels) :
    eventToll price word (flipWeak c) = eventToll price word c := by
  induction word generalizing c with
  | nil => rfl
  | cons gate rest ih =>
    have hinj : Function.Injective flipWeak :=
      (show Function.Involutive flipWeak from RefreshMap.two_ticks).injective
    simp [eventToll, step_weak, hinj.eq_iff, ih]

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

open scoped Matrix.Norms.Operator in
theorem hyperchargeFlag_eq_cos (t : ℝ) (c : Channels) :
    hyperchargeFlag t c =
      (1 - Real.cos (t * ((PMConstants.ChannelOccupancy.tag c).2.2 : ℝ) / 3)) / 2 := by
  classical
  rw [hyperchargeFlag, PMAction.InterferenceReadout.flag_formula _ (hypercharge_unitary t),
    hypercharge, PMAction.LinkEvolution.transport_eq_exp, VacancyProjection.charge_diagonal,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.diagonal_apply_eq, Pi.coe_exp,
    ← Complex.exp_eq_exp_ℂ]
  have h :
      (((t : ℂ) * Complex.I) •
        (fun c : Channels => ((PMConstants.ChannelOccupancy.tag c).2.2 : ℂ) / 3)) c =
      ((t * ((PMConstants.ChannelOccupancy.tag c).2.2 : ℝ) / 3 : ℝ) : ℂ) * Complex.I := by
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-- The vacancy's static hypercharge makes it invisible to this flag. -/
@[simp]
theorem hyperchargeFlag_static_neutral (t : ℝ) :
    hyperchargeFlag t (opposite neutrino) = 0 := by
  norm_num [hyperchargeFlag_eq_cos, neutrino, opposite, PMConstants.ChannelOccupancy.tag]

/-- Up and down static hypercharges have absolute ratio two, so their
flag responses obey the same identity at every phase and every colour. -/
theorem hyperchargeFlag_quark_pair (t : ℝ) (a : Fin 3) :
    let d := hyperchargeFlag t (.inr (.inl (a, 1)))
    hyperchargeFlag t (.inr (.inl (a, 0))) = 4 * d * (1 - d) := by
  dsimp only
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.tag]
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
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.tag,
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

`ProtocolToll.hyperchargeFlag_schedule_bound` bounds every nonnegative schedule of static
hypercharge flags. With a common positive *affine* conversion to the wire amplitude that bound
forces `s_u < 2 s_d`. `PMAction.TollAmplitude` derives the conversion instead: a label with Toll
`T` keeps amplitude `exp(−T/2)`, which is not affine (`TollAmplitude.no_affine_form`). This
section evaluates the static flags under that conversion.

* `flags_quarter`, `flags_three_quarter`: at the hypercharge steps `π/2` and `3π/2` the static
  electron, down and up flags are `(1, ¼, ¾)` and `(1, 1, 0)`. The vacancy flag is zero at
  every step (`ProtocolToll.hyperchargeFlag_static_neutral`).
* `survivalToll_differences`: with counts `w₁, w₂` at those steps,
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

/-- Static electron, down and up flags at the step `π/2`. -/
theorem flags_quarter (a : Fin 3) :
    hyperchargeFlag (π / 2) (opposite electron) = 1 ∧
    hyperchargeFlag (π / 2) (downStatic a) = 1 / 4 ∧
    hyperchargeFlag (π / 2) (upStatic a) = 3 / 4 := by
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.tag,
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
  simp only [hyperchargeFlag_eq_cos, PMConstants.ChannelOccupancy.tag,
    electron, neutrino, flipWeak, opposite]
  push_cast
  refine ⟨?_, ?_, ?_⟩
  · rw [show 3 * π / 2 * -6 / 3 = -π - 2 * π by ring, cos_sub_two_pi, cos_neg, cos_pi]
    norm_num
  · rw [show 3 * π / 2 * -2 / 3 = -π by ring, cos_neg, cos_pi]; norm_num
  · rw [show 3 * π / 2 * 4 / 3 = 2 * π by ring, cos_two_pi]; norm_num

/-- The Toll of a channel under `w₁` comparisons at `π/2` and `w₂` at `3π/2`. -/
def survivalToll (w₁ w₂ : ℝ) (c : Channels) : ℝ :=
  w₁ * hyperchargeFlag (π / 2) c + w₂ * hyperchargeFlag (3 * π / 2) c

/-- **The Toll differences.** -/
theorem survivalToll_differences (w₁ w₂ : ℝ) (a : Fin 3) :
    survivalToll w₁ w₂ (opposite electron) - survivalToll w₁ w₂ (downStatic a) = 3 / 4 * w₁ ∧
    survivalToll w₁ w₂ (downStatic a) - survivalToll w₁ w₂ (upStatic a) = w₂ - w₁ / 2 := by
  obtain ⟨e1, d1, u1⟩ := flags_quarter a
  obtain ⟨e2, d2, u2⟩ := flags_three_quarter a
  simp only [survivalToll, e1, d1, u1, e2, d2, u2]
  constructor <;> ring

/-- **The charged order.** -/
theorem survival_ladder {w₁ w₂ : ℝ} (h₁ : 0 < w₁) (h₂ : w₁ / 2 < w₂) (a : Fin 3) :
    wireAmplitude (survivalToll w₁ w₂ (opposite electron)) <
      wireAmplitude (survivalToll w₁ w₂ (downStatic a)) ∧
    wireAmplitude (survivalToll w₁ w₂ (downStatic a)) <
      wireAmplitude (survivalToll w₁ w₂ (upStatic a)) := by
  obtain ⟨hed, hdu⟩ := survivalToll_differences w₁ w₂ a
  constructor <;> rw [wireAmplitude_lt_iff] <;> linarith

/-- **Doubling is a schedule condition.** -/
theorem doubling_iff (w₁ w₂ : ℝ) (a : Fin 3) :
    2 * wireAmplitude (survivalToll w₁ w₂ (downStatic a)) ≤
      wireAmplitude (survivalToll w₁ w₂ (upStatic a)) ↔ 2 * log 2 ≤ w₂ - w₁ / 2 := by
  rw [ratio_ge_iff (by norm_num : (0 : ℝ) < 2), (survivalToll_differences w₁ w₂ a).2]

end Survival

end PMElementaryParticles.ProtocolToll
