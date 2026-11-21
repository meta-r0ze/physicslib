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
modelling step; it is stated in `SCOPE.md` named premises,
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

/-- A coordinate vector from its code: base-13 digits, each offset by 6
(coordinates lie in `[-6, 6]`). -/
def ofCode (n : ℕ) : V := fun i => (((n / 13 ^ i.val) % 13 : ℕ) : ℤ) - 6

/-- The 240 roots of `E₈` in the simple-root basis of `Lattices.gram`, one code each.
(Literal vectors or integer lists for all 240 time out during elaboration.) The plain
coordinates are in `tools/clock_ring_check.py`. -/
def rootCodes : List ℕ := [
  266246023, 328994540, 333821349, 334192642, 334221203, 334223400, 334223569, 334223413,
  334223582, 334225779, 334254340, 334625633, 339452442, 402200959, 334223570, 334223583,
  334225780, 334254341, 334625634, 339452443, 402200960, 334225949, 334254510, 334625803,
  339452612, 402201129, 334256707, 334628000, 339454809, 402203326, 334656561, 339483370,
  402231887, 339854663, 402603180, 407429989, 334256720, 334628013, 339454822, 402203339,
  334656574, 339483383, 402231900, 339854676, 402603193, 407430002, 334658771, 339485580,
  402234097, 339856873, 402605390, 407432199, 339885434, 402633951, 407460760, 407832053,
  334658940, 339485749, 402234266, 339857042, 402605559, 407432368, 339885603, 402634120,
  407460929, 407832222, 339887800, 402636317, 407463126, 407834419, 407862980, 339887813,
  402636330, 407463139, 407834432, 407862993, 407865190, 407865359, 334658941, 339485750,
  402234267, 339857043, 402605560, 407432369, 339885604, 402634121, 407460930, 407832223,
  339887801, 402636318, 407463127, 407834420, 407862981, 339887970, 402636487, 407463296,
  407834589, 407863150, 407865347, 339887814, 402636331, 407463140, 407834433, 407862994,
  407865191, 339887983, 402636500, 407463309, 407834602, 407863163, 339890180, 402638697,
  407465506, 407836799, 339918741, 402667258, 407494067, 340290034, 403038551, 345116843,
  470613877, 412692169, 475440686, 408236653, 413063462, 475811979, 407893921, 408265214,
  413092023, 475840540, 407867557, 407896118, 408267411, 413094220, 475842737, 407865529,
  407867726, 407896287, 408267580, 413094389, 475842906, 407865373, 407867570, 407896131,
  408267424, 413094233, 475842750, 407867739, 407896300, 408267593, 413094402, 475842919,
  407898497, 408269790, 413096599, 475845116, 408298351, 413125160, 475873677, 413496453,
  476244970, 481071779, 407865361, 407865530, 407867727, 407896288, 408267581, 413094390,
  475842907, 407867740, 407896301, 408267594, 413094403, 475842920, 407898498, 408269791,
  413096600, 475845117, 408298352, 413125161, 475873678, 413496454, 476244971, 481071780,
  407898667, 408269960, 413096769, 475845286, 408298521, 413125330, 475873847, 413496623,
  476245140, 481071949, 408300718, 413127527, 475876044, 413498820, 476247337, 481074146,
  413527381, 476275898, 481102707, 481474000, 408300731, 413127540, 475876057, 413498833,
  476247350, 481074159, 413527394, 476275911, 481102720, 481474013, 413529591, 476278108,
  481104917, 481476210, 481504771, 413529760, 476278277, 481105086, 481476379, 481504940,
  481507137, 481507150, 413529761, 476278278, 481105087, 481476380, 481504941, 481507138,
  481507307, 481507151, 481507320, 481509517, 481538078, 481909371, 486736180, 549484697
]

/-- The 240 roots as vectors. -/
def rootList : List V := rootCodes.map ofCode

theorem rootList_roots : ∀ z ∈ rootList, pair z z = 2 := by decide +kernel

theorem rootList_nodup : rootList.Nodup := by decide +kernel

theorem rootList_length : rootList.length = 240 := by decide +kernel

/-- **The list is complete.** Every vector of norm 2 is in it. -/
theorem rootList_complete (z : V) (hz : pair z z = 2) : z ∈ rootList := by
  classical
  have hR : Nat.card {x : V // pair x x = 2} = 240 := ThetaE8.e8_card_roots
  have : Finite {x : V // pair x x = 2} :=
    Nat.finite_of_card_ne_zero (by rw [hR]; decide)
  let f : {x // x ∈ rootList.toFinset} → {x : V // pair x x = 2} :=
    fun x => ⟨x.1, rootList_roots x.1 (List.mem_toFinset.mp x.2)⟩
  have hf : Function.Injective f := fun a b h => by
    have hv := congrArg (fun y : {x : V // pair x x = 2} => y.val) h
    exact Subtype.ext hv
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
