import PMKAutomaton.ClockSymmetry
import PMElementaryParticles.GenerationOrbits

/-!
# Full clock-root stabilizers and the existing channel placement

ClockSymmetry.Gplus and Gpm are defined by the full Weyl stabilizer conditions,
not by a selected slice subgroup. Both have glue image {identity, (1 2)}.
The key (0,1), library generation zero, is fixed. The explicit swap has both
spacetime determinant signs among its representatives. Thus its glue action
alone cannot force a parity-odd splitting mechanism.

The existing per-generation channel placement is additional structure. Its
wall rule is oriented: a transposition of glue classes reverses the cyclic
order and exchanges the two wall classes. Each ProgramClasses class lies on
one wall. No element inducing the swap can preserve any such class, even at
one generation. This is proved for EVERY element of the full stabilizers by
diagonal glue, not just by testing one swap representative.

Both label-respecting orbit partitions are {0}, {1}, {2}, for all visible
classes and their species refinements. This imposes no cross-generation cost
equality. It derives no footprint or tier assignment. No parity-odd premise
is added. The original carrier lepton-axis and colour-axis sign flips do not
fix the internal projection of cu, even up to sign. They must not be confused
with the clock-adapted axis used in the explicit Weyl word.

These groups stabilize cu, not the full 43-state reading using cv. The explicit
swap changes that reading. Closure invariance under this larger root stabilizer
is therefore not silently assumed for a clockReading-based execution cost.
-/
noncomputable section
namespace PMElementaryParticles.FullGenerationOrbits
open PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment
open PMElementaryParticles.EPSpine PMElementaryParticles.EPLabelGen
open PMElementaryParticles.ProgramClasses PMConstants.PacketGaugeActions
open PMKAutomaton.ClockSymmetry

set_option maxRecDepth 100000 in
/-- A computational witness of diagonal glue for each doubled channel weight. -/
def channelLift (g : Fin 3) (c : Channels) : V :=
  (rootList.find? fun r => decide (internalProjection r = channelE8Gen g c)).getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem channelLift_correct : ∀ (g : Fin 3) (c : Channels),
    internalProjection (channelLift g c) = channelE8Gen g c := by decide +kernel

theorem channel_class_nonzero : ∀ (g : Fin 3) (c : Channels),
    internalClass (channelE8Gen g c) ≠ 0 := by decide +kernel

/-- The factor discriminants act by the SAME permutation on all channel weights. -/
theorem channel_class_action (w : Weyl) (hw : PreservesSectors w.val) (g : Fin 3) (c : Channels) :
    internalClass (w.val (channelE8Gen g c)) = keyAction w (internalClass (channelE8Gen g c)) := by
  have h := internal_glue_action w hw (channelLift g c)
  rwa [channelLift_correct, ← diagonal_glue (channelLift g c), channelLift_correct] at h

def swapIndex (g : Fin 3) : Fin 3 := if g = 0 then 0 else if g = 1 then 2 else 1

theorem swap_index : ∀ g : Fin 3,
    genIndex (spinorSwap (GluedExcursions.generationAt g)) = swapIndex g := by decide +kernel

/-- Full-group generation orbits before retaining channel placement. -/
def RawSameOrbit (reverse : Bool) (g h : Fin 3) : Prop :=
  ∃ w : fullGroup reverse,
    genIndex (generationAction w (GluedExcursions.generationAt g)) = h

theorem rawOrbit_iff (reverse : Bool) (g h : Fin 3) :
    RawSameOrbit reverse g h ↔ g = h ∨ swapIndex g = h := by
  constructor
  · rintro ⟨w, hw⟩
    rcases generation_image_upper_bound w with hi | hs
    · left
      rwa [hi, Equiv.Perm.one_apply, GluedExcursions.generationAt_index] at hw
    · right
      rwa [hs, swap_index] at hw
  · rintro (rfl | h)
    · refine ⟨1, ?_⟩
      rw [generationAction_one, Equiv.Perm.one_apply, GluedExcursions.generationAt_index]
    · refine ⟨swapElement reverse, ?_⟩
      rwa [swap_generation_check, swap_index]

theorem raw_orbit_table : ∀ g : Fin 3,
    (Finset.univ.filter (fun h : Fin 3 => g = h ∨ swapIndex g = h)) =
      if g = 0 then {0} else {1,2} := by decide +kernel

/-- Conditional raw-generation tie. No species placement or mass reading is
identified with this function. The class-respecting theorem below differs. -/
theorem raw_invariant_tie {A : Type*} (reverse : Bool) (f : NonzeroKey → A)
    (hinvariant : ∀ (w : fullGroup reverse) g, f (generationAction w g) = f g) :
    f (GluedExcursions.generationAt 1) = f (GluedExcursions.generationAt 2) := by
  have h := hinvariant (swapElement reverse) (GluedExcursions.generationAt 1)
  rw [swap_generation_check] at h
  have hs : spinorSwap (GluedExcursions.generationAt 1) = GluedExcursions.generationAt 2 := by decide +kernel
  rw [hs] at h
  exact h.symm

/-- Exhaustive finite wall-placement obstruction, including both walls and all species. -/
theorem swap_rejects_placement : ∀ (g : Fin 3) (c d : Channels), classOf c = classOf d →
    internalClass (channelE8Gen (swapIndex g) d) ≠
      ((internalClass (channelE8Gen g c)).1,
        (internalClass (channelE8Gen g c)).1 + (internalClass (channelE8Gen g c)).2) := by
  decide +kernel

/-- A placed label has its generation key and its actual internal vector. -/
abbrev Placed := NonzeroKey × V

def placedAction {reverse : Bool} (w : fullGroup reverse) (p : Placed) : Placed :=
  (generationAction w p.1, w.val.val p.2)

theorem placedAction_one (reverse : Bool) (p : Placed) : placedAction (1 : fullGroup reverse) p = p := by
  simp [placedAction, generationAction_one]

theorem placedAction_mul {reverse : Bool} (w v : fullGroup reverse) (p : Placed) :
    placedAction (w*v) p = placedAction w (placedAction v p) := by
  simp [placedAction, generationAction_mul, LinearEquiv.mul_apply, Equiv.Perm.mul_apply]

/-- Setwise stabilizer of an existing placement predicate under the full action. -/
def placementStabilizer (reverse : Bool) (P : Placed → Prop) : Subgroup (fullGroup reverse) where
  carrier := {w | ∀ p, P (placedAction w p) ↔ P p}
  one_mem' := by intro p; rw [placedAction_one]
  mul_mem' := by
    intro w v hw hv p
    rw [placedAction_mul]
    exact (hw _).trans (hv p)
  inv_mem' := by
    intro w hw p
    have h := hw (placedAction w⁻¹ p)
    rw [← placedAction_mul, mul_inv_cancel, placedAction_one] at h
    exact h.symm

def InClass (k : Fin 6) (p : Placed) : Prop :=
  ∃ c : Channels, classOf c = k ∧ p.2 = channelE8Gen (genIndex p.1) c

def classGroup (reverse : Bool) (k : Fin 6) : Subgroup (fullGroup reverse) :=
  placementStabilizer reverse (InClass k)

/-- Setwise placement preservation has exactly the existing weak/colour class meaning. -/
theorem classGroup_maps {reverse : Bool} {k : Fin 6} (w : classGroup reverse k)
    (g : NonzeroKey) (c : Channels) (hc : classOf c = k) :
    ∃ d : Channels, classOf d = k ∧ ProgramClasses.Joined c d ∧
      w.val.val.val (channelE8Gen (genIndex g) c) =
        channelE8Gen (genIndex (generationAction w.val g)) d := by
  have hp : InClass k (g, channelE8Gen (genIndex g) c) := ⟨c, hc, rfl⟩
  obtain ⟨d, hd, heq⟩ := (w.property _).2 hp
  exact ⟨d, hd, class_transitive c d (hc.trans hd.symm), heq⟩

/-- Any class-respecting element of either FULL stabilizer fixes every generation. -/
theorem classGroup_generation_identity {reverse : Bool} (k : Fin 6) (w : classGroup reverse k) :
    generationAction w.val = 1 := by
  rcases generation_image_upper_bound w.val with h | h
  · exact h
  · obtain ⟨c, hc⟩ := classOf_surjective k
    obtain ⟨d, hd, _, heq⟩ := classGroup_maps w (GluedExcursions.generationAt 0) c hc
    have hkey := channel_class_action w.val.val w.val.property.1 0 c
    have ht := congrArg Subtype.val (Equiv.congr_fun h
      ⟨internalClass (channelE8Gen 0 c), channel_class_nonzero 0 c⟩)
    change keyAction w.val.val (internalClass (channelE8Gen 0 c)) =
      ((internalClass (channelE8Gen 0 c)).1,
        (internalClass (channelE8Gen 0 c)).1 + (internalClass (channelE8Gen 0 c)).2) at ht
    rw [ht] at hkey
    have hidx : genIndex (generationAction w.val (GluedExcursions.generationAt 0)) = swapIndex 0 := by
      rw [h]; exact swap_index 0
    rw [GluedExcursions.generationAt_index, hidx] at heq
    rw [heq] at hkey
    exact False.elim ((swap_rejects_placement 0 c d (hc.trans hd.symm)) hkey)

/-- Species refinement can only remove symmetries, not restore a rejected swap. -/
def InSpecies (k : Fin 6) (species : ProtocolInventory.BaseProtocol) (p : Placed) : Prop :=
  ∃ c : Channels, classOf c = k ∧ ProtocolInventory.baseProtocol c = some species ∧
    p.2 = channelE8Gen (genIndex p.1) c

def speciesGroup (reverse : Bool) (k : Fin 6) (species : ProtocolInventory.BaseProtocol) :
    Subgroup (fullGroup reverse) :=
  classGroup reverse k ⊓ placementStabilizer reverse (InSpecies k species)

def SameOrbit (reverse : Bool) (k : Fin 6) (g h : Fin 3) : Prop :=
  ∃ w : classGroup reverse k,
    genIndex (generationAction w.val (GluedExcursions.generationAt g)) = h

theorem sameOrbit_iff (reverse : Bool) (k : Fin 6) (g h : Fin 3) :
    SameOrbit reverse k g h ↔ g = h := by
  constructor
  · rintro ⟨w, hw⟩
    rwa [classGroup_generation_identity, Equiv.Perm.one_apply, GluedExcursions.generationAt_index] at hw
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [show (1 : classGroup reverse k).val = 1 from rfl, generationAction_one,
      Equiv.Perm.one_apply, GluedExcursions.generationAt_index]

theorem species_generation_identity {reverse : Bool} (k : Fin 6)
    (species : ProtocolInventory.BaseProtocol) (w : speciesGroup reverse k species) :
    generationAction w.val = 1 :=
  classGroup_generation_identity k ⟨w.val, w.property.1⟩

theorem speciesOrbit_iff (reverse : Bool) (k : Fin 6) (species : ProtocolInventory.BaseProtocol)
    (g h : Fin 3) :
    (∃ w : speciesGroup reverse k species,
      genIndex (generationAction w.val (GluedExcursions.generationAt g)) = h) ↔ g = h := by
  constructor
  · rintro ⟨w, hw⟩
    rwa [species_generation_identity, Equiv.Perm.one_apply, GluedExcursions.generationAt_index] at hw
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [show (1 : speciesGroup reverse k species).val = 1 from rfl,
      generationAction_one, Equiv.Perm.one_apply, GluedExcursions.generationAt_index]

/-! ## A typed program action and its conditional cost consequence -/

private theorem placement_injective (g : Fin 3) : Function.Injective (channelE8Gen g) :=
  fun _ _ h => channelGen_internalContent_injective g (congrArg EPLabel.internalContent h)

private theorem label_image {reverse : Bool} {k : Fin 6} (w : classGroup reverse k)
    (g : NonzeroKey) (c : Channels) (hc : classOf c = k) :
    ∃ d : Channels, classOf d = k ∧
      w.val.val.val (channelE8Gen (genIndex g) c) = channelE8Gen (genIndex g) d := by
  obtain ⟨d, hd, _, heq⟩ := classGroup_maps w g c hc
  rw [classGroup_generation_identity, Equiv.Perm.one_apply] at heq
  exact ⟨d, hd, heq⟩

def mappedLabel {reverse : Bool} {k : Fin 6} (w : classGroup reverse k)
    (g : NonzeroKey) (c : Channels) (hc : classOf c = k) : Channels :=
  Classical.choose (label_image w g c hc)

theorem mappedLabel_spec {reverse : Bool} {k : Fin 6} (w : classGroup reverse k)
    (g : NonzeroKey) (c : Channels) (hc : classOf c = k) :
    classOf (mappedLabel w g c hc) = k ∧
      w.val.val.val (channelE8Gen (genIndex g) c) =
        channelE8Gen (genIndex g) (mappedLabel w g c hc) :=
  Classical.choose_spec (label_image w g c hc)

theorem mappedLabel_one {reverse : Bool} {k : Fin 6}
    (g : NonzeroKey) (c : Channels) (hc : classOf c = k) :
    mappedLabel (1 : classGroup reverse k) g c hc = c := by
  apply placement_injective (genIndex g)
  exact (mappedLabel_spec 1 g c hc).2.symm

theorem mappedLabel_mul {reverse : Bool} {k : Fin 6} (w v : classGroup reverse k)
    (g : NonzeroKey) (c : Channels) (hc : classOf c = k) :
    mappedLabel (w*v) g c hc =
      mappedLabel w g (mappedLabel v g c hc) (mappedLabel_spec v g c hc).1 := by
  apply placement_injective (genIndex g)
  rw [← (mappedLabel_spec (w*v) g c hc).2,
    ← (mappedLabel_spec w g (mappedLabel v g c hc) (mappedLabel_spec v g c hc).1).2,
    ← (mappedLabel_spec v g c hc).2]
  rfl

abbrev ClassProgram (k : Fin 6) := {p : Program // classOf p.label = k}

/-- The algebraic action retains the reference and firing data. It is an
actual action on the Program type. It is NOT claimed to preserve a physical
43-site execution or its pillars, since these root stabilizers need not fix cv. -/
def programAction {reverse : Bool} {k : Fin 6} (w : classGroup reverse k)
    (p : ClassProgram k) : ClassProgram k :=
  ⟨{ label := mappedLabel w p.val.generation p.val.label p.property
     generation := p.val.generation
     reference := p.val.reference
     firing := p.val.firing
     packet := w.val.val.val p.val.packet
     packet_root := weyl_root w.val.val _ p.val.packet_root
     packet_key := by
       rw [← keyAction_descent _ w.val.property.1, p.val.packet_key]
       exact congrArg Subtype.val (Equiv.congr_fun (classGroup_generation_identity k w) p.val.generation) },
    (mappedLabel_spec w p.val.generation p.val.label p.property).1⟩

private theorem program_ext {p q : Program} (hl : p.label = q.label)
    (hg : p.generation = q.generation) (hr : p.reference = q.reference)
    (hf : p.firing = q.firing) (hp : p.packet = q.packet) : p = q := by
  cases p; cases q
  cases hl; cases hg; cases hr; cases hf; cases hp
  rfl

theorem programAction_one {reverse : Bool} {k : Fin 6} (p : ClassProgram k) :
    programAction (1 : classGroup reverse k) p = p := by
  apply Subtype.ext
  apply program_ext
  · exact mappedLabel_one p.val.generation p.val.label p.property
  · rfl
  · rfl
  · rfl
  · rfl

theorem programAction_mul {reverse : Bool} {k : Fin 6}
    (w v : classGroup reverse k) (p : ClassProgram k) :
    programAction (w*v) p = programAction w (programAction v p) := by
  apply Subtype.ext
  apply program_ext
  · exact mappedLabel_mul w v p.val.generation p.val.label p.property
  · rfl
  · rfl
  · rfl
  · rfl

/-- Closure used as a supplied invariance property, with no selected cost formula. -/
theorem invariant_cost_equal {reverse : Bool} {k : Fin 6} {A : Type*}
    (cost : Program → A)
    (hinvariant : ∀ (w : classGroup reverse k) (p : ClassProgram k),
      cost (programAction w p).val = cost p.val)
    (p q : ClassProgram k) (h : ∃ w : classGroup reverse k, q = programAction w p) :
    cost q.val = cost p.val :=
  GenerationOrbits.invariant_cost_equal programAction (fun p : ClassProgram k => cost p.val)
    hinvariant p q h

/-- Even after imposing full label-respecting invariance, a real-valued
function may separate any distinct generations. This is not a mass reading. -/
theorem invariant_can_separate {reverse : Bool} {k : Fin 6} (p q : ClassProgram k)
    (hne : p.val.generation ≠ q.val.generation) :
    ∃ cost : Program → ℝ,
      (∀ (w : classGroup reverse k) (x : ClassProgram k),
        cost (programAction w x).val = cost x.val) ∧ cost p.val ≠ cost q.val := by
  refine ⟨fun x => ((genIndex x.generation).val : ℝ), fun _ _ => rfl, ?_⟩
  intro h
  apply hne
  apply genIndex_bijective.injective
  apply Fin.ext
  change ((genIndex p.val.generation).val : ℝ) = ((genIndex q.val.generation).val : ℝ) at h
  exact_mod_cast h

/-- Finite report shared by all five visible classes and all seven class/species rows. -/
theorem orbit_table : ∀ (g h : Fin 3),
    (h ∈ (Finset.univ.filter (fun i : Fin 3 => i = g))) ↔ g = h := by decide +kernel

/-- The fixed key of the raw swap is precisely the earlier ±2-excursion key. -/
theorem fixed_excursion_key :
    (GluedExcursions.generationAt 0).val = (0,1) ∧
    spinorSwap (GluedExcursions.generationAt 0) = GluedExcursions.generationAt 0 ∧
    (2,1) ∈ GluedExcursions.clockHistogram 0 ∧ (41,1) ∈ GluedExcursions.clockHistogram 0 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact (GenerationOrbits.two_tick_generation 0).2 rfl

/-- Flip in the ORIGINAL internal signed-axis chart of the carriers. -/
def carrierAxisFlip (i : Fin 4) (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun j => if j = i then -v j else v j

def flippedInternalClock (i : Fin 4) : V :=
  ChannelPlacement.sector1Embed (ChannelPlacement.d4FromEps (carrierAxisFlip i ![1,-1,-1,-1]))

/-- The lepton-axis flip (0) and all three colour-axis flips fail equally. -/
theorem carrier_axis_clock_checks : ∀ i : Fin 4,
    flippedInternalClock i ≠ internalProjection PMSubstrate.ClockPlane.cu ∧
    flippedInternalClock i ≠ -internalProjection PMSubstrate.ClockPlane.cu := by decide +kernel

theorem no_single_carrier_axis {reverse : Bool} (w : fullGroup reverse) (i : Fin 4) :
    w.val.val (internalProjection PMSubstrate.ClockPlane.cu) ≠ flippedInternalClock i := by
  rw [internalProjection_commutes _ w.property.1]
  rcases w.property.2 with hw | ⟨_, hw⟩
  · rw [hw]; exact (carrier_axis_clock_checks i).1.symm
  · rw [hw]
    have hn : internalProjection (-PMSubstrate.ClockPlane.cu) =
        -internalProjection PMSubstrate.ClockPlane.cu := by
      simp only [internalProjection, sectorProjection, Matrix.mulVec_neg, smul_neg]
      abel
    rw [hn]
    exact (carrier_axis_clock_checks i).2.symm

end PMElementaryParticles.FullGenerationOrbits
