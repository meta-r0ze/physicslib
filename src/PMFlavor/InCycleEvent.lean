import PMElementaryParticles.ControlledGluedRegister
import PMAction.GenerationHistory

/-!
# The E8 root word for the in-cycle generation edge

A four-reflection diagonal inverse triality preserves the transported signed
indices and moves the generation back by one within either wall. On the
active wall, four pure D4 reflections on the label factor implement the
separate weak sign exchange. The combined word realizes the required edge
on a chosen active generation. Selecting just the light pair needs a wall
record: the untagged glued root also encodes a static state in another
generation. With a supplied wall tag the light-pair exchange can be isolated.
-/

namespace PMFlavor.InCycleEvent

open PMElementaryParticles.GluedRegister PMElementaryParticles.ControlledGluedRegister
open PMElementaryParticles.ProtocolInventory PMConstants.PacketGaugeActions

/-- E8 reflections in application order, with each vector specified by its
common glue class and its signed index in each D4 factor. -/
def generationWord : List (Fin 3 × Fin 8 × Fin 8) :=
  [(1, 6, 6), (2, 6, 6), (1, 6, 1), (2, 6, 1)]

def runGenerationShift (w : Wt × Wt) : Wt × Wt :=
  generationWord.foldl (fun p (x, a, b) => reflectPair (carrier x a, carrier x b) p) w

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The word applies inverse triality in each factor, without a factor swap. -/
theorem generation_word_glued : ∀ (x : Fin 3) (a b : Fin 8),
    runGenerationShift (carrier x a, carrier x b) =
      (triality (triality (carrier x a)), triality (triality (carrier x b))) := by
  decide +kernel

/-- The same geometric word moves every generation and preserves both the
protocol channel and the signed amplitude index. -/
theorem generation_shift_encode (g : Fin 3) (c : Channels) (amp : Fin 8) :
    runGenerationShift (encode g c amp) = encode (g - 1) c amp := by
  obtain ⟨a,b,h⟩ := encode_glued g c amp
  have hword : runGenerationShift (encode g c amp) =
      (triality (triality (encode g c amp).1), triality (triality (encode g c amp).2)) := by
    rw [h, generation_word_glued]
  have hx : ∀ g : Fin 3, ∀ b : Bool, wallClass g b + 1 + 1 = wallClass (g - 1) b := by
    decide
  rw [hword]
  cases hc : active c <;> simp [encode, place, hc, frame_succ, hx]

/-- Two orthogonal pure roots on each coordinate pair produce the antipode
in the first D4 factor. -/
def labelWord : List (Fin 4 × Fin 4 × Bool) :=
  [(0, 1, true), (0, 1, false), (2, 3, true), (2, 3, false)]

def runLabelAntipode (w : Wt × Wt) : Wt × Wt :=
  labelWord.foldl (fun p (i, j, s) => reflectPair (root i j false s, 0) p) w

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem label_word_glued : ∀ (x : Fin 3) (a b : Fin 8),
    runLabelAntipode (carrier x a, carrier x b) = (-carrier x a, carrier x b) := by
  decide +kernel

/-- On the active wall the first factor carries the protocol sign, so this
word implements the weak refresh there. -/
theorem label_word_active (g : Fin 3) (c : Channels) (amp : Fin 8) (hc : active c = true) :
    runLabelAntipode (encode g c amp) = encode g (flipWeak c) amp := by
  obtain ⟨a,b,h⟩ := encode_glued g c amp
  have hword : runLabelAntipode (encode g c amp) =
      (-(encode g c amp).1, (encode g c amp).2) := by
    rw [h, label_word_glued]
  rw [hword, encode_weak]
  simp [encode, place, hc]

def runForward (w : Wt × Wt) : Wt × Wt :=
  runGenerationShift (runLabelAntipode w)

/-- On an active source this candidate acts as the weak flip and the
`g → g - 1` label change. In particular `g = 2` supplies the desired geometry. -/
theorem forward_active (g : Fin 3) (c : Channels) (amp : Fin 8) (hc : active c = true) :
    runForward (encode g c amp) = encode (g - 1) (flipWeak c) amp := by
  rw [runForward, label_word_active g c amp hc, generation_shift_encode]

/-- No operation of the untagged glued root alone can implement the active
in-cycle edge and fix every static root. The conflicting inputs encode the
same root in two different generations. -/
theorem no_untagged_event (F : Wt × Wt → Wt × Wt)
    (hactive : ∀ c amp, active c = true →
      F (encode 2 c amp) = encode 1 (flipWeak c) amp)
    (hstatic : ∀ g c amp, active c = false → F (encode g c amp) = encode g c amp) :
    False := by
  let a : Channels := .inl (0, 0)
  let b : Channels := .inr (.inl (0, 0))
  have hsame : encode 2 a 2 = encode 0 b 2 := by decide +kernel
  have hdiff : encode 1 (flipWeak a) 2 ≠ encode 0 b 2 := by decide +kernel
  exact hdiff ((hactive a 2 rfl).symm.trans ((congrArg F hsame).trans (hstatic 0 b 2 rfl)))

/-- If the companion carrier holds the other wall's class, the two classes
recover both the active-wall bit and the omitted generation. The orientation
is the existing glued-register convention. -/
theorem companion_decodes : ∀ (g : Fin 3) (b : Bool),
    let live := wallClass g b
    let companion := wallClass g (!b)
    decide (companion = live + 2) = b ∧ PMAction.GenerationHistory.third live companion = g := by
  decide +kernel

/-- Use the supplied wall record and the class of the root to select the two
active light sectors. The reverse branch applies inverse triality twice
and the same weak sign exchange. -/
def runSelected (isActive : Bool) (w : Wt × Wt) : Wt × Wt :=
  if isActive then
    if onWall 2 true w then runForward w
    else if onWall 1 true w then runGenerationShift (runForward w)
    else w
  else w

private theorem select_active (k g : Fin 3) (c : Channels) (amp : Fin 8)
    (hc : active c = true) :
    onWall k true (encode g c amp) = true ↔ g = k := by
  simp only [onWall, encode, hc, place, ite_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha⟩
    have h := frame_class_unique _ _ _ _ ha
    exact sub_left_inj.mp (show g - 1 = k - 1 from h)
  · rintro rfl
    exact ⟨labelIndex c, rfl⟩

/-- The tagged candidate is the identity on static states and on generation
zero. On the active light pair it exchanges generations and refreshes the
protocol sign while preserving the amplitude index. -/
theorem selected_encode (g : Fin 3) (c : Channels) (amp : Fin 8) :
    runSelected (active c) (encode g c amp) =
      if active c then
        if g = 2 then encode 1 (flipWeak c) amp
        else if g = 1 then encode 2 (flipWeak c) amp
        else encode g c amp
      else encode g c amp := by
  cases hc : active c
  · simp [runSelected]
  · fin_cases g
    · have h₂ := not_congr (select_active 2 0 c amp hc) |>.mpr (by decide)
      have h₁ := not_congr (select_active 1 0 c amp hc) |>.mpr (by decide)
      simp [runSelected, h₂, h₁]
    · have h₂ := not_congr (select_active 2 1 c amp hc) |>.mpr (by decide)
      have h₁ := (select_active 1 1 c amp hc).mpr rfl
      simp [runSelected, h₂, h₁, forward_active _ _ _ hc, generation_shift_encode,
        show (-1 : Fin 3) = 2 from rfl]
    · have h₂ := (select_active 2 2 c amp hc).mpr rfl
      simp [runSelected, h₂, forward_active _ _ _ hc]

/-- The tagged event is reversible on the encoded states, with the same
wall tag retained across both applications. -/
theorem selected_twice (g : Fin 3) (c : Channels) (amp : Fin 8) :
    runSelected (active c) (runSelected (active c) (encode g c amp)) = encode g c amp := by
  have hweak : ∀ c : Channels, flipWeak (flipWeak c) = c := by decide +kernel
  have hsecond (j : Fin 3) :
      runSelected (active c) (encode j (flipWeak c) amp) =
        if active c then
          if j = 2 then encode 1 c amp
          else if j = 1 then encode 2 c amp
          else encode j (flipWeak c) amp
        else encode j (flipWeak c) amp := by
    rw [← weak_active c, selected_encode, weak_active, hweak]
  rw [selected_encode]
  cases hc : active c
  · simp [runSelected]
  · have hzero := selected_encode 0 c amp
    rw [hc] at hzero hsecond
    fin_cases g
    · simpa using hzero
    · simpa using hsecond 2
    · simpa using hsecond 1

end PMFlavor.InCycleEvent
