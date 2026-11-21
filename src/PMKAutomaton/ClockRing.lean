import PMSubstrate.ThetaE8
import PMSubstrate.ClockPlane

/-!
# The clock closes the receiver ring

`RingReceiver` closes the encoded root line by a periodic identification. This
module proposes the identification from the substrate: the clock. The clock's
states are the discriminant group of the clock plane `ℤ cu + ℤ cv ⊂ E₈`
(`PMSubstrate.ClockPlane.clock_glue`: `w ↦ w₁ − 2 w₂ mod 43`). A lattice vector
reads the clock by pairing with that plane:

`clockReading z = ⟨z,cu⟩ − 2 ⟨z,cv⟩  (mod 43)`.

* `clockReading_add`, `clockReading_neg`: the reading is additive.
* `rootList_complete`: the explicit list holds every E₈ root
  (from `PMSubstrate.ThetaE8.e8_card_roots`).
* `one_tick_roots`, `minus_tick_roots`, `silent_roots`, `moving_roots`: 22 roots
  advance the reading by `+1`, 22 by `−1`, 22 leave it unchanged, 218 change it.
* `plus_projection`, `plus_split`: the `+1` roots project onto the clock plane as
  `(1,0)` or `(−1,−1)`, eleven each.
* `walk_reading`, `walk_returns_iff`: a walk of `+1` roots advances the reading by
  its length and returns to its start exactly when 43 divides the length.
* `plus_step_rotates`: as a site in `Fin 43` (`toFin`), a `+1` root step is
  `finRotate 43`, the receiver ring's stream shift.

So a packet that makes one root event per tick, each changing the reading by
`±1`, lives on a ring of exactly 43 sites (`Δ`, `PMSubstrate.E8Values.Delta_eq`).
The identification of the receiver's tick with one such root event is the
modelling step; it is stated in `PMElementaryParticles/LINE-AND-COMPOSITION.md`,
which also lists the checks still open (step weights between the two projection
classes, consistency with `SliceHop`). Exploration script:
`tools/clock_ring_check.py`.
-/

namespace PMKAutomaton.ClockRing

open Matrix PMSubstrate

abbrev V := Fin 8 → ℤ

/-- The E₈ pairing in the simple-root basis. -/
def pair (a b : V) : ℤ := a ⬝ᵥ (Lattices.gram *ᵥ b)

/-- The clock reading of a lattice vector: its class in the clock's
discriminant group `ℤ/43` (`ClockPlane.clock_glue`). -/
def clockReading (z : V) : ZMod 43 :=
  ((pair z ClockPlane.cu - 2 * pair z ClockPlane.cv : ℤ) : ZMod 43)

/-- The reading is `clock_glue`'s map applied to the plane projection. -/
theorem clockReading_eq_glue (z : V) :
    clockReading z = (((pair z ClockPlane.cu, pair z ClockPlane.cv).1 -
      2 * (pair z ClockPlane.cu, pair z ClockPlane.cv).2 : ℤ) : ZMod 43) := rfl

theorem pair_add_left (a b c : V) : pair (a + b) c = pair a c + pair b c := by
  simp [pair, add_dotProduct]

theorem pair_neg_left (a c : V) : pair (-a) c = -pair a c := by
  simp [pair, neg_dotProduct]

theorem clockReading_add (a b : V) :
    clockReading (a + b) = clockReading a + clockReading b := by
  unfold clockReading
  rw [pair_add_left, pair_add_left]
  push_cast
  ring

theorem clockReading_neg (a : V) : clockReading (-a) = -clockReading a := by
  unfold clockReading
  rw [pair_neg_left, pair_neg_left]
  push_cast
  ring

theorem clockReading_zero : clockReading 0 = 0 := by
  simp [clockReading, pair]

/-- A coordinate vector from a list of eight integers. -/
def ofList (l : List ℤ) : V := fun i => l.getD i.val 0

/-- The 240 roots of `E₈` in the simple-root basis of `Lattices.gram`, as integer lists.
(Plain lists keep elaboration cheap; `![…]` literals for all 240 time out.) -/
def rawRoots : List (List ℤ) := [
  [-2, -3, -4, -6, -5, -4, -3, -2],
  [-2, -3, -4, -6, -5, -4, -3, -1],
  [-2, -3, -4, -6, -5, -4, -2, -1],
  [-2, -3, -4, -6, -5, -3, -2, -1],
  [-2, -3, -4, -6, -4, -3, -2, -1],
  [-2, -3, -4, -5, -4, -3, -2, -1],
  [-2, -3, -3, -5, -4, -3, -2, -1],
  [-2, -2, -4, -5, -4, -3, -2, -1],
  [-2, -2, -3, -5, -4, -3, -2, -1],
  [-2, -2, -3, -4, -4, -3, -2, -1],
  [-2, -2, -3, -4, -3, -3, -2, -1],
  [-2, -2, -3, -4, -3, -2, -2, -1],
  [-2, -2, -3, -4, -3, -2, -1, -1],
  [-2, -2, -3, -4, -3, -2, -1, 0],
  [-1, -3, -3, -5, -4, -3, -2, -1],
  [-1, -2, -3, -5, -4, -3, -2, -1],
  [-1, -2, -3, -4, -4, -3, -2, -1],
  [-1, -2, -3, -4, -3, -3, -2, -1],
  [-1, -2, -3, -4, -3, -2, -2, -1],
  [-1, -2, -3, -4, -3, -2, -1, -1],
  [-1, -2, -3, -4, -3, -2, -1, 0],
  [-1, -2, -2, -4, -4, -3, -2, -1],
  [-1, -2, -2, -4, -3, -3, -2, -1],
  [-1, -2, -2, -4, -3, -2, -2, -1],
  [-1, -2, -2, -4, -3, -2, -1, -1],
  [-1, -2, -2, -4, -3, -2, -1, 0],
  [-1, -2, -2, -3, -3, -3, -2, -1],
  [-1, -2, -2, -3, -3, -2, -2, -1],
  [-1, -2, -2, -3, -3, -2, -1, -1],
  [-1, -2, -2, -3, -3, -2, -1, 0],
  [-1, -2, -2, -3, -2, -2, -2, -1],
  [-1, -2, -2, -3, -2, -2, -1, -1],
  [-1, -2, -2, -3, -2, -2, -1, 0],
  [-1, -2, -2, -3, -2, -1, -1, -1],
  [-1, -2, -2, -3, -2, -1, -1, 0],
  [-1, -2, -2, -3, -2, -1, 0, 0],
  [-1, -1, -2, -3, -3, -3, -2, -1],
  [-1, -1, -2, -3, -3, -2, -2, -1],
  [-1, -1, -2, -3, -3, -2, -1, -1],
  [-1, -1, -2, -3, -3, -2, -1, 0],
  [-1, -1, -2, -3, -2, -2, -2, -1],
  [-1, -1, -2, -3, -2, -2, -1, -1],
  [-1, -1, -2, -3, -2, -2, -1, 0],
  [-1, -1, -2, -3, -2, -1, -1, -1],
  [-1, -1, -2, -3, -2, -1, -1, 0],
  [-1, -1, -2, -3, -2, -1, 0, 0],
  [-1, -1, -2, -2, -2, -2, -2, -1],
  [-1, -1, -2, -2, -2, -2, -1, -1],
  [-1, -1, -2, -2, -2, -2, -1, 0],
  [-1, -1, -2, -2, -2, -1, -1, -1],
  [-1, -1, -2, -2, -2, -1, -1, 0],
  [-1, -1, -2, -2, -2, -1, 0, 0],
  [-1, -1, -2, -2, -1, -1, -1, -1],
  [-1, -1, -2, -2, -1, -1, -1, 0],
  [-1, -1, -2, -2, -1, -1, 0, 0],
  [-1, -1, -2, -2, -1, 0, 0, 0],
  [-1, -1, -1, -2, -2, -2, -2, -1],
  [-1, -1, -1, -2, -2, -2, -1, -1],
  [-1, -1, -1, -2, -2, -2, -1, 0],
  [-1, -1, -1, -2, -2, -1, -1, -1],
  [-1, -1, -1, -2, -2, -1, -1, 0],
  [-1, -1, -1, -2, -2, -1, 0, 0],
  [-1, -1, -1, -2, -1, -1, -1, -1],
  [-1, -1, -1, -2, -1, -1, -1, 0],
  [-1, -1, -1, -2, -1, -1, 0, 0],
  [-1, -1, -1, -2, -1, 0, 0, 0],
  [-1, -1, -1, -1, -1, -1, -1, -1],
  [-1, -1, -1, -1, -1, -1, -1, 0],
  [-1, -1, -1, -1, -1, -1, 0, 0],
  [-1, -1, -1, -1, -1, 0, 0, 0],
  [-1, -1, -1, -1, 0, 0, 0, 0],
  [-1, 0, -1, -1, -1, -1, -1, -1],
  [-1, 0, -1, -1, -1, -1, -1, 0],
  [-1, 0, -1, -1, -1, -1, 0, 0],
  [-1, 0, -1, -1, -1, 0, 0, 0],
  [-1, 0, -1, -1, 0, 0, 0, 0],
  [-1, 0, -1, 0, 0, 0, 0, 0],
  [-1, 0, 0, 0, 0, 0, 0, 0],
  [0, -1, -1, -2, -2, -2, -2, -1],
  [0, -1, -1, -2, -2, -2, -1, -1],
  [0, -1, -1, -2, -2, -2, -1, 0],
  [0, -1, -1, -2, -2, -1, -1, -1],
  [0, -1, -1, -2, -2, -1, -1, 0],
  [0, -1, -1, -2, -2, -1, 0, 0],
  [0, -1, -1, -2, -1, -1, -1, -1],
  [0, -1, -1, -2, -1, -1, -1, 0],
  [0, -1, -1, -2, -1, -1, 0, 0],
  [0, -1, -1, -2, -1, 0, 0, 0],
  [0, -1, -1, -1, -1, -1, -1, -1],
  [0, -1, -1, -1, -1, -1, -1, 0],
  [0, -1, -1, -1, -1, -1, 0, 0],
  [0, -1, -1, -1, -1, 0, 0, 0],
  [0, -1, -1, -1, 0, 0, 0, 0],
  [0, -1, 0, -1, -1, -1, -1, -1],
  [0, -1, 0, -1, -1, -1, -1, 0],
  [0, -1, 0, -1, -1, -1, 0, 0],
  [0, -1, 0, -1, -1, 0, 0, 0],
  [0, -1, 0, -1, 0, 0, 0, 0],
  [0, -1, 0, 0, 0, 0, 0, 0],
  [0, 0, -1, -1, -1, -1, -1, -1],
  [0, 0, -1, -1, -1, -1, -1, 0],
  [0, 0, -1, -1, -1, -1, 0, 0],
  [0, 0, -1, -1, -1, 0, 0, 0],
  [0, 0, -1, -1, 0, 0, 0, 0],
  [0, 0, -1, 0, 0, 0, 0, 0],
  [0, 0, 0, -1, -1, -1, -1, -1],
  [0, 0, 0, -1, -1, -1, -1, 0],
  [0, 0, 0, -1, -1, -1, 0, 0],
  [0, 0, 0, -1, -1, 0, 0, 0],
  [0, 0, 0, -1, 0, 0, 0, 0],
  [0, 0, 0, 0, -1, -1, -1, -1],
  [0, 0, 0, 0, -1, -1, -1, 0],
  [0, 0, 0, 0, -1, -1, 0, 0],
  [0, 0, 0, 0, -1, 0, 0, 0],
  [0, 0, 0, 0, 0, -1, -1, -1],
  [0, 0, 0, 0, 0, -1, -1, 0],
  [0, 0, 0, 0, 0, -1, 0, 0],
  [0, 0, 0, 0, 0, 0, -1, -1],
  [0, 0, 0, 0, 0, 0, -1, 0],
  [0, 0, 0, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 1],
  [0, 0, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 1, 1],
  [0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 1, 1, 0],
  [0, 0, 0, 0, 0, 1, 1, 1],
  [0, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 0, 1, 1, 1, 0],
  [0, 0, 0, 0, 1, 1, 1, 1],
  [0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 1, 1, 0, 0, 0],
  [0, 0, 0, 1, 1, 1, 0, 0],
  [0, 0, 0, 1, 1, 1, 1, 0],
  [0, 0, 0, 1, 1, 1, 1, 1],
  [0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 1, 1, 0, 0, 0, 0],
  [0, 0, 1, 1, 1, 0, 0, 0],
  [0, 0, 1, 1, 1, 1, 0, 0],
  [0, 0, 1, 1, 1, 1, 1, 0],
  [0, 0, 1, 1, 1, 1, 1, 1],
  [0, 1, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 0, 0, 0],
  [0, 1, 0, 1, 1, 0, 0, 0],
  [0, 1, 0, 1, 1, 1, 0, 0],
  [0, 1, 0, 1, 1, 1, 1, 0],
  [0, 1, 0, 1, 1, 1, 1, 1],
  [0, 1, 1, 1, 0, 0, 0, 0],
  [0, 1, 1, 1, 1, 0, 0, 0],
  [0, 1, 1, 1, 1, 1, 0, 0],
  [0, 1, 1, 1, 1, 1, 1, 0],
  [0, 1, 1, 1, 1, 1, 1, 1],
  [0, 1, 1, 2, 1, 0, 0, 0],
  [0, 1, 1, 2, 1, 1, 0, 0],
  [0, 1, 1, 2, 1, 1, 1, 0],
  [0, 1, 1, 2, 1, 1, 1, 1],
  [0, 1, 1, 2, 2, 1, 0, 0],
  [0, 1, 1, 2, 2, 1, 1, 0],
  [0, 1, 1, 2, 2, 1, 1, 1],
  [0, 1, 1, 2, 2, 2, 1, 0],
  [0, 1, 1, 2, 2, 2, 1, 1],
  [0, 1, 1, 2, 2, 2, 2, 1],
  [1, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 0, 0, 0],
  [1, 0, 1, 1, 0, 0, 0, 0],
  [1, 0, 1, 1, 1, 0, 0, 0],
  [1, 0, 1, 1, 1, 1, 0, 0],
  [1, 0, 1, 1, 1, 1, 1, 0],
  [1, 0, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 0, 0, 0, 0],
  [1, 1, 1, 1, 1, 0, 0, 0],
  [1, 1, 1, 1, 1, 1, 0, 0],
  [1, 1, 1, 1, 1, 1, 1, 0],
  [1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 2, 1, 0, 0, 0],
  [1, 1, 1, 2, 1, 1, 0, 0],
  [1, 1, 1, 2, 1, 1, 1, 0],
  [1, 1, 1, 2, 1, 1, 1, 1],
  [1, 1, 1, 2, 2, 1, 0, 0],
  [1, 1, 1, 2, 2, 1, 1, 0],
  [1, 1, 1, 2, 2, 1, 1, 1],
  [1, 1, 1, 2, 2, 2, 1, 0],
  [1, 1, 1, 2, 2, 2, 1, 1],
  [1, 1, 1, 2, 2, 2, 2, 1],
  [1, 1, 2, 2, 1, 0, 0, 0],
  [1, 1, 2, 2, 1, 1, 0, 0],
  [1, 1, 2, 2, 1, 1, 1, 0],
  [1, 1, 2, 2, 1, 1, 1, 1],
  [1, 1, 2, 2, 2, 1, 0, 0],
  [1, 1, 2, 2, 2, 1, 1, 0],
  [1, 1, 2, 2, 2, 1, 1, 1],
  [1, 1, 2, 2, 2, 2, 1, 0],
  [1, 1, 2, 2, 2, 2, 1, 1],
  [1, 1, 2, 2, 2, 2, 2, 1],
  [1, 1, 2, 3, 2, 1, 0, 0],
  [1, 1, 2, 3, 2, 1, 1, 0],
  [1, 1, 2, 3, 2, 1, 1, 1],
  [1, 1, 2, 3, 2, 2, 1, 0],
  [1, 1, 2, 3, 2, 2, 1, 1],
  [1, 1, 2, 3, 2, 2, 2, 1],
  [1, 1, 2, 3, 3, 2, 1, 0],
  [1, 1, 2, 3, 3, 2, 1, 1],
  [1, 1, 2, 3, 3, 2, 2, 1],
  [1, 1, 2, 3, 3, 3, 2, 1],
  [1, 2, 2, 3, 2, 1, 0, 0],
  [1, 2, 2, 3, 2, 1, 1, 0],
  [1, 2, 2, 3, 2, 1, 1, 1],
  [1, 2, 2, 3, 2, 2, 1, 0],
  [1, 2, 2, 3, 2, 2, 1, 1],
  [1, 2, 2, 3, 2, 2, 2, 1],
  [1, 2, 2, 3, 3, 2, 1, 0],
  [1, 2, 2, 3, 3, 2, 1, 1],
  [1, 2, 2, 3, 3, 2, 2, 1],
  [1, 2, 2, 3, 3, 3, 2, 1],
  [1, 2, 2, 4, 3, 2, 1, 0],
  [1, 2, 2, 4, 3, 2, 1, 1],
  [1, 2, 2, 4, 3, 2, 2, 1],
  [1, 2, 2, 4, 3, 3, 2, 1],
  [1, 2, 2, 4, 4, 3, 2, 1],
  [1, 2, 3, 4, 3, 2, 1, 0],
  [1, 2, 3, 4, 3, 2, 1, 1],
  [1, 2, 3, 4, 3, 2, 2, 1],
  [1, 2, 3, 4, 3, 3, 2, 1],
  [1, 2, 3, 4, 4, 3, 2, 1],
  [1, 2, 3, 5, 4, 3, 2, 1],
  [1, 3, 3, 5, 4, 3, 2, 1],
  [2, 2, 3, 4, 3, 2, 1, 0],
  [2, 2, 3, 4, 3, 2, 1, 1],
  [2, 2, 3, 4, 3, 2, 2, 1],
  [2, 2, 3, 4, 3, 3, 2, 1],
  [2, 2, 3, 4, 4, 3, 2, 1],
  [2, 2, 3, 5, 4, 3, 2, 1],
  [2, 2, 4, 5, 4, 3, 2, 1],
  [2, 3, 3, 5, 4, 3, 2, 1],
  [2, 3, 4, 5, 4, 3, 2, 1],
  [2, 3, 4, 6, 4, 3, 2, 1],
  [2, 3, 4, 6, 5, 3, 2, 1],
  [2, 3, 4, 6, 5, 4, 2, 1],
  [2, 3, 4, 6, 5, 4, 3, 1],
  [2, 3, 4, 6, 5, 4, 3, 2]
]

/-- The 240 roots as vectors. -/
def rootList : List V := rawRoots.map ofList

theorem rootList_roots : ∀ z ∈ rootList, pair z z = 2 := by decide +kernel

theorem rootList_nodup : rootList.Nodup := by decide +kernel

theorem rootList_length : rootList.length = 240 := by decide +kernel

/-- **The list is complete.** Every vector of norm 2 is in it. -/
theorem rootList_complete (z : V) (hz : pair z z = 2) : z ∈ rootList := by
  classical
  have hR : Nat.card {x : V // pair x x = 2} = 240 := ThetaE8.e8_card_roots
  haveI : Finite {x : V // pair x x = 2} :=
    Nat.finite_of_card_ne_zero (by rw [hR]; decide)
  let f : {x // x ∈ rootList.toFinset} → {x : V // pair x x = 2} :=
    fun x => ⟨x.1, rootList_roots x.1 (List.mem_toFinset.mp x.2)⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (congrArg Subtype.val h)
  have hcard : Nat.card {x // x ∈ rootList.toFinset} = Nat.card {x : V // pair x x = 2} := by
    rw [hR, Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup rootList_nodup, rootList_length]
  obtain ⟨⟨y, hy⟩, hyz⟩ := (hf.bijective_of_nat_card_le hcard.ge).2 ⟨z, hz⟩
  have hyz' : y = z := congrArg Subtype.val hyz
  exact hyz' ▸ List.mem_toFinset.mp hy

/-- **One-tick roots.** Exactly 22 roots advance the clock reading by `+1`. -/
theorem one_tick_roots : (rootList.filter fun r => clockReading r = 1).length = 22 := by
  decide +kernel

/-- Exactly 22 roots move the reading by `−1`. -/
theorem minus_tick_roots : (rootList.filter fun r => clockReading r = -1).length = 22 := by
  decide +kernel

/-- Exactly 22 roots leave the reading unchanged. -/
theorem silent_roots : (rootList.filter fun r => clockReading r = 0).length = 22 := by
  decide +kernel

/-- 218 roots change the reading. -/
theorem moving_roots : (rootList.filter fun r => clockReading r ≠ 0).length = 218 := by
  decide +kernel

/-- The `−1` roots are the negatives of the `+1` roots: the two streams. -/
theorem minus_iff_neg_plus (r : V) : clockReading (-r) = -1 ↔ clockReading r = 1 := by
  rw [clockReading_neg, neg_inj]

/-- Every `+1` root projects onto the clock plane as `(1,0)` or `(−1,−1)`. -/
theorem plus_projection : ∀ r ∈ rootList, clockReading r = 1 →
    (pair r ClockPlane.cu = 1 ∧ pair r ClockPlane.cv = 0) ∨
      (pair r ClockPlane.cu = -1 ∧ pair r ClockPlane.cv = -1) := by
  decide +kernel

/-- Eleven `+1` roots of each projection class. -/
theorem plus_split :
    (rootList.filter fun r => clockReading r = 1 ∧
        pair r ClockPlane.cu = 1 ∧ pair r ClockPlane.cv = 0).length = 11 ∧
      (rootList.filter fun r => clockReading r = 1 ∧
        pair r ClockPlane.cu = -1 ∧ pair r ClockPlane.cv = -1).length = 11 := by
  decide +kernel

theorem clockReading_sum : ∀ steps : List V,
    clockReading steps.sum = (steps.map clockReading).sum
  | [] => by simp [clockReading_zero]
  | r :: rs => by
    rw [List.sum_cons, clockReading_add, clockReading_sum rs, List.map_cons, List.sum_cons]

/-- **A walk of `+1` roots advances the reading by its length.** -/
theorem walk_reading (z : V) (steps : List V) (h : ∀ r ∈ steps, clockReading r = 1) :
    clockReading (z + steps.sum) = clockReading z + (steps.length : ZMod 43) := by
  rw [clockReading_add, clockReading_sum]
  have hm : steps.map clockReading = List.replicate steps.length 1 := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact h r hr
  rw [hm, List.sum_replicate, nsmul_eq_mul, mul_one]

/-- **The walk closes after exactly a multiple of 43 steps.** -/
theorem walk_returns_iff (z : V) (steps : List V) (h : ∀ r ∈ steps, clockReading r = 1) :
    clockReading (z + steps.sum) = clockReading z ↔ 43 ∣ steps.length := by
  rw [walk_reading z steps h]
  simp [CharP.cast_eq_zero_iff (ZMod 43) 43]

/-- The clock reading as a ring site: `ZMod 43` is `Fin 43`. -/
def toFin (x : ZMod 43) : Fin 43 := x

/-- **A `+1` root step is the ring's stream shift.** As a site in `Fin 43`, the reading
after the step is `finRotate 43` of the reading before. -/
theorem plus_step_rotates (z r : V) (hr : clockReading r = 1) :
    toFin (clockReading (z + r)) = finRotate 43 (toFin (clockReading z)) := by
  rw [finRotate_apply, clockReading_add, hr]
  rfl

end PMKAutomaton.ClockRing
