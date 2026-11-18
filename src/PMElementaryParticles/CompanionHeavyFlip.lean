import PMElementaryParticles.HeavyFlipControl
import PMElementaryParticles.HeavyCrossingCost

/-!
# Use a retained carrier to address the heavy flip

The glued root's class and the companion's class select the two directions
of the heavy endpoint exchange. The companion sits in the other occupied
class. The two crossing words transport the live root, and triality
transports the companion to the class vacated by the live root while
retaining its signed carrier index. The companion and protocol record are
supplied. This is the endpoint word on the encoded states.
-/

namespace PMElementaryParticles.CompanionHeavyFlip

open ControlledGluedRegister GluedRegister HeavyFlipControl
open PMConstants.PacketGaugeActions

abbrev State := (Wt × Wt) × Wt

private def inClass (x : Fin 3) (v : Wt) : Bool :=
  decide (∃ i : Fin 8, v = frame x i)

private theorem frame_class_test (x y : Fin 3) (i : Fin 8) :
    inClass x (frame y i) = true ↔ x = y := by
  simp only [inClass, decide_eq_true_eq]
  exact ⟨fun ⟨j, h⟩ => (frame_class_unique _ _ _ _ h).symm,
    fun h => ⟨i, by rw [h]⟩⟩

private theorem live_class_test (x g : Fin 3) (c : Channels) (a : Fin 8) :
    inClass x (encode g c a).1 = true ↔ x = wallClass g (ProtocolInventory.active c) := by
  obtain ⟨i, j, h⟩ := encode_glued g c a
  obtain ⟨k, hk⟩ := frame_onto _ i
  rw [h]
  change inClass x (carrier (wallClass g (ProtocolInventory.active c)) i) = true ↔ _
  rw [← hk, frame_class_test]

/-- The companion may occupy any signed carrier in the other wall's class. -/
def pack (g : Fin 3) (c : Channels) (a k : Fin 8) : State :=
  (encode g c a, frame (wallClass g (!ProtocolInventory.active c)) k)

def ready (b : Bool) (w : State) : Bool :=
  inClass (wallClass 0 b) w.1.1 && inClass (wallClass 0 (!b)) w.2

private theorem pair_address : ∀ (g : Fin 3) (b c : Bool),
    (wallClass 0 b = wallClass g c ∧ wallClass 0 (!b) = wallClass g (!c)) ↔
      g = 0 ∧ c = b := by decide +kernel

/-- The class pair addresses exactly generation zero and the indicated
incoming wall. The test is independent of both carrier indices. -/
theorem ready_pack (b : Bool) (g : Fin 3) (c : Channels) (a k : Fin 8) :
    ready b (pack g c a k) = true ↔ g = 0 ∧ ProtocolInventory.active c = b := by
  rw [ready, Bool.and_eq_true]
  change (inClass _ (encode g c a).1 = true ∧ inClass _
    (frame (wallClass g (!ProtocolInventory.active c)) k) = true) ↔ _
  rw [live_class_test, frame_class_test]
  exact pair_address g b (ProtocolInventory.active c)

/-- Update the companion and the live root using their transported frames.
The forward and reverse words are selected by the two observed classes. -/
def run (selected stored : Record) (w : State) : State :=
  if stored = selected then
    if ready false w then (runCrossing w.1, triality (triality w.2))
    else if ready true w then
      ((HeavyCrossingCost.word true).foldl
        (fun p r => reflectPair (HeavyCrossingCost.rootPair r) p) w.1, triality w.2)
    else w
  else w

private theorem pack_opposite_live (c : Channels) (a : Fin 8) (b : Bool)
    (hc : ProtocolInventory.active c = b) :
    (HeavyCrossingCost.word b).foldl
      (fun p r => reflectPair (HeavyCrossingCost.rootPair r) p) (encode 0 c a) =
      encode 0 (opposite c) a := by
  simpa [HeavyCrossingCost.input, encode, hc, opposite_active, opposite_label] using
    HeavyCrossingCost.endpoint b a (labelIndex c)

private theorem advance_companion (b : Bool) (k : Fin 8) :
    (if b then triality (frame (wallClass 0 (!b)) k)
      else triality (triality (frame (wallClass 0 (!b)) k))) =
      frame (wallClass 0 b) k := by
  cases b
  · change triality (triality (frame 2 k)) = frame 1 k
    rw [frame_succ, frame_succ]
    rfl
  · change triality (frame 1 k) = frame 2 k
    rw [frame_succ]
    rfl

/-- The same guarded flip as `HeavyFlipControl`, with the generation
address read from the companion. Its carrier index remains available for
the reverse operation. -/
theorem run_pack (selected stored : Record) (g : Fin 3) (c : Channels) (a k : Fin 8) :
    let out := controlledFlip selected ((g, c, a), stored)
    run selected stored (pack g c a k) = pack out.1.1 out.1.2.1 out.1.2.2 k := by
  dsimp only
  by_cases hs : stored = selected
  · by_cases hg : g = 0
    · subst g
      have hf : ready false (pack 0 c a k) = true ↔ ProtocolInventory.active c = false := by
        rw [ready_pack]; simp
      have ht : ready true (pack 0 c a k) = true ↔ ProtocolInventory.active c = true := by
        rw [ready_pack]; simp
      cases hc : ProtocolInventory.active c
      · have hready := hf.mpr hc
        simp only [run, hs, hready, ite_true, controlledFlip, Equiv.coe_fn_mk, direct_iff, and_self]
        have hl := pack_opposite_live c a false hc
        change runCrossing (encode 0 c a) = _ at hl
        simp only [pack, opposite_active, hc, Bool.not_false, Bool.not_true]
        rw [hl]
        exact congrArg (fun v => (encode 0 (opposite c) a, v)) (advance_companion false k)
      · have hready := ht.mpr hc
        have hn : ready false (pack 0 c a k) ≠ true := fun h =>
          Bool.noConfusion (hc.symm.trans (hf.mp h))
        simp only [run, hs, hready, hn, Bool.false_eq_true, ite_true, ite_false, controlledFlip, Equiv.coe_fn_mk,
          direct_iff, and_self]
        simp only [pack, opposite_active, hc, Bool.not_true, Bool.not_false]
        rw [pack_opposite_live c a true hc]
        exact congrArg (fun v => (encode 0 (opposite c) a, v)) (advance_companion true k)
    · have hn (b : Bool) : ready b (pack g c a k) ≠ true := fun h =>
        hg ((ready_pack b g c a k).mp h).1
      simp [run, hs, hn, flip_light _ _ g hg]
  · simp [run, hs, controlledFlip]

/-- The packed companion and live root return exactly under the same guarded word. -/
theorem run_twice_pack (selected stored : Record) (g : Fin 3) (c : Channels) (a k : Fin 8) :
    run selected stored (run selected stored (pack g c a k)) = pack g c a k := by
  rw [run_pack]
  by_cases h : direct g ∧ stored = selected
  · simp only [controlledFlip, Equiv.coe_fn_mk, h]
    rw [run_pack]
    simp [controlledFlip, h, opposite_twice]
  · simp only [controlledFlip, Equiv.coe_fn_mk, h, ite_false]
    rw [run_pack]
    simp [controlledFlip, h]

end PMElementaryParticles.CompanionHeavyFlip
