import PMKAutomaton.Machine.ClockEps

/-!
# The directional hop in the aligned clock

`AxisHop` proved that a spatial step is a word of two `D₄` roots, with six such
words.  This file says which of them the split update's directional factor
uses, on the **actual clock**.

The spatial axis is the clock-silent norm-4 vector `h = (1,1,−1,−1)`
(`AxisHop.h`).  Of the six ordered root pairs summing to `h`, exactly four have
both root events clock-silent; the other two have one event reading `+1` and
one reading `−1` (`clock_words_signs`).  The four silent words are one orbit of
the clock-fixing coordinate swaps that fix `h`, namely `swap01` (exchange the
two `+1` coordinates) and `swap23` (exchange the two `−1` coordinates).  Both
are inside the `A3` slice symmetries (the coordinate permutations fixing the
clock vector `(1,1,1,1)`).

A transport weight defined inside the substrate is invariant under those
symmetries, so `slice_uniform` gives all four silent words the same weight; no
word is chosen.  The coordinate picture (`AxisHop.epsAxis` and the `p 3 = 0`
filter) is the triality image and is not used here.

The hop's overall Hamiltonian rate still requires calibration against the
inter-wall crossing and the substrate clock (`PMAction/TODO.md`).
-/

noncomputable section
namespace PMAction.SliceHop
open AxisHop
open PMKAutomaton.ClockRing

/-- A root event is clock-silent when its aligned clock reading is zero. -/
def silentRoot (t : Tri) : Prop := clockReading (ClockEps.rootE8 t) = 0

instance (t : Tri) : Decidable (silentRoot t) := by unfold silentRoot; infer_instance

/-- The `D₄` roots. -/
def rootSet : Finset Tri := Finset.univ.filter IsRoot

/-- Ordered root pairs whose sum is the spatial axis `h`. -/
def words : Finset (Tri × Tri) :=
  (rootSet.product rootSet).filter fun p => ∀ i, val (p.1 i) + val (p.2 i) = val (h i)

/-- The words whose two root events are both clock-silent. -/
def silentWords : Finset (Tri × Tri) :=
  words.filter fun p => silentRoot p.1 ∧ silentRoot p.2

/-- The words with a clock-moving root event. -/
def clockWords : Finset (Tri × Tri) :=
  words.filter fun p => ¬ (silentRoot p.1 ∧ silentRoot p.2)

theorem words_card : words.card = 6 := by decide +kernel

/-- **Exactly four of the six words are fully clock-silent.** -/
theorem silent_words_count : silentWords.card = 4 := by decide +kernel

/-- **Two of the six words move the clock.** -/
theorem clock_words_count : clockWords.card = 2 := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Each clock-moving word has one event reading `+1` and one reading `−1`.** -/
theorem clock_words_signs :
    ∀ p ∈ clockWords,
      (clockReading (ClockEps.rootE8 p.1) = 1 ∧ clockReading (ClockEps.rootE8 p.2) = -1) ∨
        (clockReading (ClockEps.rootE8 p.1) = -1 ∧ clockReading (ClockEps.rootE8 p.2) = 1) := by
  decide +kernel

/-- Exchange the two `+1` ε coordinates `0` and `1`. -/
def swap01 (t : Tri) : Tri := t ∘ Equiv.swap (0 : Fin 4) 1

/-- Exchange the two `−1` ε coordinates `2` and `3`. -/
def swap23 (t : Tri) : Tri := t ∘ Equiv.swap (2 : Fin 4) 3

/-- A symmetry acting on both events of a word. -/
def act (σ : Tri → Tri) (p : Tri × Tri) : Tri × Tri := (σ p.1, σ p.2)

/-- The base silent word `(e₀−e₂, e₁−e₃)`. -/
def base : Tri × Tri := (![1, 0, 2, 0], ![0, 1, 0, 2])

/-- The orbit of `base` under the clock-fixing swaps that fix `h`. -/
def orbit : Finset (Tri × Tri) :=
  {base, act swap01 base, act swap23 base, act swap01 (act swap23 base)}

theorem swap01_fixes_h : swap01 h = h := by decide +kernel
theorem swap23_fixes_h : swap23 h = h := by decide +kernel

/-- **The four silent words are exactly one orbit.** -/
theorem silent_words_eq_orbit : silentWords = orbit := by decide +kernel

theorem silent_words_one_orbit : (silentWords.filter fun p => p ∉ orbit).card = 0 := by
  rw [silent_words_eq_orbit]; decide +kernel

/-- The clock-fixing swaps preserve the silent set. -/
theorem swap01_preserves : silentWords.image (act swap01) = silentWords := by
  rw [silent_words_eq_orbit]; decide +kernel
theorem swap23_preserves : silentWords.image (act swap23) = silentWords := by
  rw [silent_words_eq_orbit]; decide +kernel

/-- **A symmetric transport weight is uniform on the silent words.** -/
theorem slice_uniform {R : Type*} (w : Tri × Tri → R)
    (hswap01 : ∀ p, w (act swap01 p) = w p)
    (hswap23 : ∀ p, w (act swap23 p) = w p) :
    ∀ p ∈ silentWords, w p = w base := by
  intro p hp
  rw [silent_words_eq_orbit] at hp
  simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rfl
  · exact hswap01 base
  · exact hswap23 base
  · rw [hswap01 (act swap23 base), hswap23 base]

end PMAction.SliceHop
