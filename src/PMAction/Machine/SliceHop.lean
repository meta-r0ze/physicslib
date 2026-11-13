import PMAction.Machine.AxisHop

/-!
# Which root word the directional hop uses

`AxisHop` shows a spatial axis step `2eⱼ` is a word of two `D₄` roots, with six such words. This
module says which of them the split update's directional factor uses.

The directional factor (`LocalUnitary.neighbor`, `SplitUpdate.direction`) acts on sites and spin
within one tick: it has no clock register and does not move the clock. Take coordinate `3` as the
clock axis and coordinate `0` as the hop axis (the other spatial axes are the same by symmetry).

* `slice_words_count`: exactly four of the six words keep both root events in the tick's slice
  (clock coordinate `0`): `2e₀ = (e₀ ± eₖ) + (e₀ ∓ eₖ)` with `k` one of the two transverse
  spatial axes.
* `clock_words_count`, `clock_words_reverse`: the other two route through `e₀ ± e₃`, and each has
  one root event with clock coordinate `−1`, an event that runs the clock backwards. They are not
  within-tick transport.
* `slice_words_eq`, `slice_uniform`: the four slice words form one orbit of the slice's own
  symmetries that fix the hop axis (`swap12`, exchanging the transverse axes, and `flip1`, the sign
  of one transverse axis). So any transport weight defined inside the substrate (Closure: invariant
  under those symmetries) gives all four words the same weight.

So the directional hop is the equal-weight sum of the four in-slice two-root words; no word is
chosen. Under the full stabilizer of the axis, which also moves the clock axis, all six words would
be one orbit; the split update fixes a clock, so only the slice symmetries apply. This settles the
word. It does not fix the hop's overall normalization (shared group/trace normalization across
spacings, PMAction REVIEW B.2).
-/

namespace PMAction.SliceHop
open AxisHop

-- The word sets are irreducible: they are finite sets over `81²` pairs, and unfolding them while
-- elaborating a membership hypothesis exceeds the recursion limit. The kernel checks still unfold.

/-- Ordered root pairs whose sum is the hop `2e₀`. -/
@[irreducible] def words : Finset (Tri × Tri) :=
  Finset.univ.filter fun p => IsRoot p.1 ∧ IsRoot p.2 ∧ ∀ i, val (p.1 i) + val (p.2 i) = 2 * axis 0 i

/-- The words whose two root events both stay in the slice (clock coordinate `3` is `0`). -/
@[irreducible] def sliceWords : Finset (Tri × Tri) := words.filter fun p => p.1 3 = 0 ∧ p.2 3 = 0

/-- The words that move the clock coordinate. -/
@[irreducible] def clockWords : Finset (Tri × Tri) := words.filter fun p => ¬ (p.1 3 = 0 ∧ p.2 3 = 0)

/-- **Four in-slice words.** -/
theorem slice_words_count : sliceWords.card = 4 := by decide +kernel

/-- **Two clock-moving words.** -/
theorem clock_words_count : clockWords.card = 2 := by decide +kernel

theorem clock_forward_count :
    (clockWords.filter fun p => ¬ (val (p.1 3) = -1 ∨ val (p.2 3) = -1)).card = 0 := by
  decide +kernel

/-- **Each clock-moving word has an event that runs the clock backwards.** -/
theorem clock_words_reverse :
    ∀ p ∈ clockWords, val (p.1 3) = -1 ∨ val (p.2 3) = -1 := by
  intro p hp
  by_contra h
  have hm : p ∈ clockWords.filter fun p => ¬ (val (p.1 3) = -1 ∨ val (p.2 3) = -1) :=
    Finset.mem_filter.2 ⟨hp, h⟩
  rw [Finset.card_eq_zero.1 clock_forward_count] at hm
  simp at hm

/-- Negation on `{−1, 0, 1}` in the `Fin 3` encoding. -/
def neg (x : Fin 3) : Fin 3 := if x = 1 then 2 else if x = 2 then 1 else 0

/-- Exchange the transverse axes `1` and `2`. -/
def swap12 (t : Tri) : Tri := t ∘ Equiv.swap (1 : Fin 4) 2

/-- Reverse the sign of transverse axis `1`. -/
def flip1 (t : Tri) : Tri := Function.update t 1 (neg (t 1))

/-- A symmetry acting on both events of a word. -/
def act (σ : Tri → Tri) (p : Tri × Tri) : Tri × Tri := (σ p.1, σ p.2)

/-- The word `(e₀ + e₁, e₀ − e₁)`. -/
def base : Tri × Tri := (![1, 1, 0, 0], ![1, 2, 0, 0])

/-- The orbit of `base` under `swap12` and `flip1`. -/
def orbit : Finset (Tri × Tri) :=
  {base, act flip1 base, act swap12 base, act swap12 (act flip1 base)}

theorem slice_outside_count : (sliceWords.filter fun p => p ∉ orbit).card = 0 := by
  decide +kernel

/-- **The slice words are one orbit of `swap12` and `flip1`.** -/
theorem slice_words_eq : sliceWords = orbit := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    by_contra h
    have hm : p ∈ sliceWords.filter fun p => p ∉ orbit := Finset.mem_filter.2 ⟨hp, h⟩
    rw [Finset.card_eq_zero.1 slice_outside_count] at hm
    simp at hm
  · rw [slice_words_count]; decide +kernel

/-- The slice symmetries map slice words to slice words. -/
theorem swap12_preserves : sliceWords.image (act swap12) = sliceWords := by
  rw [slice_words_eq]; decide +kernel
theorem flip1_preserves : sliceWords.image (act flip1) = sliceWords := by
  rw [slice_words_eq]; decide +kernel

/-- **A symmetric transport weight is uniform on the slice words.** -/
theorem slice_uniform {R : Type*} (w : Tri × Tri → R)
    (hs : ∀ p, w (act swap12 p) = w p) (hf : ∀ p, w (act flip1 p) = w p) :
    ∀ p ∈ sliceWords, w p = w base := by
  intro p hp
  rw [slice_words_eq] at hp
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rfl
  · exact hf base
  · exact hs base
  · rw [hs, hf]

end PMAction.SliceHop
