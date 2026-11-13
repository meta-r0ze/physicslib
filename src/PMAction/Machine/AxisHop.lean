import Mathlib.Tactic

/-!
# The microscopic hop: an axis step is a word of two D₄ roots

PMAction REVIEW B.2 asks which E8 root words realize the split update's directional hop
(`SplitUpdate.direction`, a hop along the site permutation `e` in spatial direction `j`). The
internal generators already have root words (`CarrierWeyl`); this module does the site hop.

A sector's addresses form `D₄`: integer vectors with even coordinate sum, whose nearest-neighbour
moves are the 24 roots (two entries `±1`, the rest `0`; norm `2`). Coordinates are `ℤ⁴`.

* `unit_axis_not_address`: a unit axis step `eⱼ` has odd sum, so it is not a `D₄` vector. No
  address step moves along one axis by one.
* `axis_not_root`: `2eⱼ` has norm `4`, so it is not a root either: one root event cannot make an
  axis step.
* `axis_two_roots`: `2eⱼ = (eⱼ + eₖ) + (eⱼ − eₖ)` for any other axis `k`, both roots.
* `axis_words_count`: exactly six ordered pairs of roots sum to `2e₀` (three choices of `k`, two
  orders), and the same holds on every axis by symmetry.

So the shortest axis hop is a word of exactly two root events, with six equally short words and
no preferred one (Closure: the update cannot prefer a `k`). This is the microscopic content of a
directional factor: one axis step is two primitive root events. (`ClockLedger.clock_tick_cost`'s
factor `2` comes from four flags of probability `1/2`, a different count; the two are not
identified here.)
-/

namespace PMAction.AxisHop

/-- A vector in `{−1, 0, 1}⁴`, encoded by `Fin 3` (`0 ↦ 0`, `1 ↦ 1`, `2 ↦ −1`). -/
abbrev Tri := Fin 4 → Fin 3

def val (t : Fin 3) : ℤ := if t = 1 then 1 else if t = 2 then -1 else 0

def vec (t : Tri) : Fin 4 → ℤ := fun i => val (t i)

/-- `D₄` roots: exactly two nonzero entries. -/
def IsRoot (t : Tri) : Prop := (Finset.univ.filter fun i => t i ≠ 0).card = 2

instance : DecidablePred IsRoot := fun t => by unfold IsRoot; infer_instance

/-- The unit axis vector `eⱼ`. -/
def axis (j : Fin 4) : Fin 4 → ℤ := fun i => if i = j then 1 else 0

/-- **A unit axis step is not an address step**: its coordinate sum is odd. -/
theorem unit_axis_not_address (j : Fin 4) : ¬ 2 ∣ ∑ i, axis j i := by
  have : ∑ i, axis j i = 1 := by fin_cases j <;> simp [axis]
  rw [this]; decide

/-- **No single root is an axis step `2eⱼ`.** -/
theorem axis_not_root : ∀ (t : Tri) (j : Fin 4), IsRoot t → vec t ≠ fun i => 2 * axis j i := by
  intro t j _ h
  have := congrFun h j
  simp [vec, axis] at this
  unfold val at this
  split_ifs at this <;> omega

/-- **Two roots make an axis step.** `2e₀ = (e₀ + e₁) + (e₀ − e₁)`. -/
theorem axis_two_roots :
    IsRoot ![1, 1, 0, 0] ∧ IsRoot ![1, 2, 0, 0] ∧
      (fun i => vec ![1, 1, 0, 0] i + vec ![1, 2, 0, 0] i) = fun i => 2 * axis 0 i := by
  refine ⟨by decide, by decide, ?_⟩
  funext i; fin_cases i <;> decide

/-- **Exactly six ordered root pairs make the axis step `2e₀`.** -/
theorem axis_words_count :
    ((Finset.univ : Finset (Tri × Tri)).filter fun p =>
      IsRoot p.1 ∧ IsRoot p.2 ∧ ∀ i, val (p.1 i) + val (p.2 i) = 2 * axis 0 i).card = 6 := by
  decide +kernel

end PMAction.AxisHop
