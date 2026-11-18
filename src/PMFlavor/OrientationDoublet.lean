import PMFlavor.InCycleEvent
import PMElementaryParticles.RefreshMap
import Mathlib.Tactic

/-!
# If the weak doublet is the wall orientation, every move flips it

Candidate (PMAction OVERVIEW, "Protocol register candidates"): a generation is a pair of distinct
nontrivial classes, one per wall, and its two orientations, which class sits on which wall, are the
weak partners. Label the three classes by `Fin 3` and call a pair `(t, f)` (wall `T`, wall `F`)
positively oriented when `f = t + 1`; `PMAction.GenerationWalls.side` fixes one such convention.

* `wall_F_shift_flips`, `wall_T_shift_flips`: a single-wall shift, which changes the class on one
  wall to the third class and so changes the generation (`PMAction.GenerationLabel.single_wall_shift`),
  always reverses the orientation.
* `root_move_flips`: the root move by the generation's label exchanges the two classes
  (`register_candidates_check.py`, T5), keeping the generation and reversing the orientation.
* `no_neutral_change`: so no single move changes the generation and keeps the orientation.

Read with the orientation as the doublet: every elementary move is an up ↔ down transition. The
same-generation one is a root move (direct); the generation-changing ones are single-wall shifts,
direct through the reference's class and through the node otherwise (`ReferenceRouting`). These are
the charged-current transitions with the CKM's pattern (diagonal, Cabibbo, node-suppressed), and a
flavour change that keeps the doublet member (a neutral one) needs two moves.

* `flip_reverses`, `flip_node_edges`: the `s ↔ c` exchange, a symmetry of the wire and of the
  reference node (it fixes the reference's class), reverses every orientation and maps the node edge
  `1 → 0` (up member holding the reference's class) onto the reverse of the edge `0 → 2` (down member
  holding it). So any readout that is the same for up and down members gives the two node entries
  the same size: `|V_cb| ≠ |V_ub|` needs a charged-current readout that distinguishes the doublet
  member holding the reference's class.

In the glued register used by the current in-cycle candidate, the ordered
live/companion classes encode the bank. Weak refresh changes the signed
label within that bank. The selected in-cycle edge also preserves the
live/companion orientation while flipping the weak partner.
-/

namespace PMFlavor.OrientationDoublet

/-- Orientation of a two-wall pair: positive when the wall-`F` class follows the wall-`T` class. -/
def orient (t f : Fin 3) : Bool := decide (f = t + 1)

/-- **Shifting the wall-`F` class to the third class reverses the orientation.** -/
theorem wall_F_shift_flips : ∀ t f f' : Fin 3, t ≠ f → f' ≠ t → f' ≠ f →
    orient t f' = !orient t f := by decide

/-- **Shifting the wall-`T` class to the third class reverses the orientation.** -/
theorem wall_T_shift_flips : ∀ t t' f : Fin 3, t ≠ f → t' ≠ f → t' ≠ t →
    orient t' f = !orient t f := by decide

/-- **The root move by the label exchanges the walls' classes and reverses the orientation.** -/
theorem root_move_flips : ∀ t f : Fin 3, t ≠ f → orient f t = !orient t f := by decide

/-- The generation of a pair is the class it omits. -/
def gen (t f : Fin 3) : Fin 3 := -t - f

/-- **No single move changes the generation and keeps the orientation.** -/
theorem no_neutral_change : ∀ t f t' f' : Fin 3, t ≠ f → t' ≠ f' →
    ((t = t' ∧ f ≠ f') ∨ (f = f' ∧ t ≠ t') ∨ (t' = f ∧ f' = t)) →
    gen t f ≠ gen t' f' → orient t' f' ≠ orient t f := by
  intro t f t' f'
  fin_cases t <;> fin_cases f <;> fin_cases t' <;> fin_cases f' <;> simp [gen, orient]

/-- The colour-axis reflection's action on classes: it fixes the reference's class `0` and exchanges
`s = 1` and `c = 2` (PMElementaryParticles `DoubletReflection.flip_spinor`, `flip_cospinor`). -/
def flip : Fin 3 → Fin 3 := ![0, 2, 1]

/-- **The `s ↔ c` exchange reverses the orientation** of every two-wall pair, and relabels the
generation by the same exchange. -/
theorem flip_reverses : ∀ t f : Fin 3, t ≠ f →
    orient (flip t) (flip f) = !orient t f ∧ gen (flip t) (flip f) = flip (gen t f) := by
  decide

/-- **It maps one node edge onto the other with up and down exchanged**: the up state of generation
`1` holding the reference's class on wall `F`, `(2, 0)`, goes to the down state of generation `2`
holding it, `(1, 0)`; the edge `1 → 0` becomes the reverse of the edge `0 → 2`. -/
theorem flip_node_edges :
    (orient 2 0 = true ∧ gen 2 0 = 1) ∧ (orient (flip 2) (flip 0) = false ∧ gen (flip 2) (flip 0) = 2) ∧
    (orient 2 1 = false ∧ gen 2 1 = 0) ∧ (orient (flip 2) (flip 1) = true ∧ gen (flip 2) (flip 1) = 0) := by
  decide

open PMElementaryParticles.GluedRegister PMElementaryParticles.ControlledGluedRegister
open PMElementaryParticles.ProtocolInventory PMConstants.PacketGaugeActions

/-- Read the two classes in live/companion order, as in the tagged in-cycle event. -/
def classOrder (g : Fin 3) (c : Channels) : Fin 3 × Fin 3 :=
  (wallClass g (active c), wallClass g (!active c))

/-- In this register the class orientation records the bank. -/
theorem classOrder_orientation (g : Fin 3) (c : Channels) :
    orient (classOrder g c).1 (classOrder g c).2 = !active c := by
  have h : ∀ (g : Fin 3) (b : Bool), orient (wallClass g b) (wallClass g (!b)) = !b := by
    decide +kernel
  exact h g (active c)

/-- At fixed generation the weak refresh preserves both ordered classes. -/
theorem weak_classOrder (g : Fin 3) (c : Channels) :
    classOrder g (flipWeak c) = classOrder g c := by
  simp [classOrder, weak_active]

/-- At fixed generation a class-order reversal changes banks. -/
theorem swapped_classOrder_iff (g : Fin 3) (c d : Channels) :
    classOrder g d = (classOrder g c).swap ↔ active d = !active c := by
  constructor
  · intro h
    exact wallClass_injective g (congrArg Prod.fst h)
  · intro h
    simp [classOrder, h]

/-- The weak refresh cannot realize the class-order reversal on this register. -/
theorem weak_classOrder_ne_swap (g : Fin 3) (c : Channels) :
    classOrder g (flipWeak c) ≠ (classOrder g c).swap := by
  rw [ne_eq, swapped_classOrder_iff, weak_active]
  cases active c <;> decide

/-- The selected active in-cycle word changes the weak partner and generation
while preserving the live/companion orientation. -/
theorem selected_inCycle_preserves_orientation (c : Channels) (amp : Fin 8)
    (hc : active c = true) :
    InCycleEvent.runSelected true (encode 2 c amp) = encode 1 (flipWeak c) amp ∧
    flipWeak c ≠ c ∧
    orient (classOrder 1 (flipWeak c)).1 (classOrder 1 (flipWeak c)).2 =
      orient (classOrder 2 c).1 (classOrder 2 c).2 := by
  refine ⟨?_, (PMElementaryParticles.RefreshMap.moves_iff_active c).mpr hc, ?_⟩
  · simpa [hc] using InCycleEvent.selected_encode 2 c amp
  · simp only [classOrder_orientation, weak_active]

end PMFlavor.OrientationDoublet
