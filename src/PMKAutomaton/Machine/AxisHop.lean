import Mathlib.Tactic

/-!
# The microscopic hop in the aligned clock

`ClockEps` proves that in the aligned placement the clock reading of a
spacetime `D₄` vector `ε` is `21·(ε₀+ε₁+ε₂+ε₃) mod 43`.  So every coordinate
axis `2eⱼ` reads `−1` (it moves the clock; `ClockEps.two_epsAxis_reads`), and
the clock-silent norm-4 vectors are the six `±(1,1,−1,−1)`-type vectors: three
spatial axes with the clock along `(1,1,1,1)`.

The spatial axis `h = (1,1,−1,−1)` is not a root (its norm is 4), it is a sum
of two roots, and exactly six ordered root pairs sum to it.

The three spatial axes are the triality images of the three coordinate axes:
the coordinate picture (`epsAxis` and the `p 3 = 0` filter) is the
ε-coordinate description, not the clock.  The old ε statements are kept with an
`eps` prefix; they describe coordinates, not the clock.
-/

noncomputable section
namespace PMAction.AxisHop

/-- A vector in `{−1, 0, 1}⁴`, encoded by `Fin 3` (`0 ↦ 0`, `1 ↦ 1`, `2 ↦ −1`). -/
abbrev Tri := Fin 4 → Fin 3

def val (t : Fin 3) : ℤ := if t = 1 then 1 else if t = 2 then -1 else 0

def vec (t : Tri) : Fin 4 → ℤ := fun i => val (t i)

/-- `D₄` roots: exactly two nonzero entries. -/
def IsRoot (t : Tri) : Prop := (Finset.univ.filter fun i => t i ≠ 0).card = 2

instance : DecidablePred IsRoot := fun t => by unfold IsRoot; infer_instance

/-! ## The ε coordinate statements (coordinates, not the clock) -/

/-- The ε coordinate axis `eⱼ`. -/
def epsAxis (j : Fin 4) : Fin 4 → ℤ := fun i => if i = j then 1 else 0

/-- **A unit ε axis step is not an address step**: its coordinate sum is odd. -/
theorem epsUnit_not_address (j : Fin 4) : ¬ 2 ∣ ∑ i, epsAxis j i := by
  have : ∑ i, epsAxis j i = 1 := by fin_cases j <;> simp [epsAxis]
  rw [this]; decide

/-- **No single root is a coordinate axis step `2eⱼ`.**  This is a coordinate
statement: the coordinate axis also moves the clock (`ClockEps.two_epsAxis_reads`). -/
theorem epsAxis_not_root : ∀ (t : Tri) (j : Fin 4), IsRoot t → vec t ≠ fun i => 2 * epsAxis j i := by
  intro t j _ h
  have := congrFun h j
  simp [vec, epsAxis] at this
  unfold val at this
  split_ifs at this <;> omega

/-- **Two roots make the coordinate axis step.** `2e₀ = (e₀ + e₁) + (e₀ − e₁)`. -/
theorem epsAxis_two_roots :
    IsRoot ![1, 1, 0, 0] ∧ IsRoot ![1, 2, 0, 0] ∧
      (fun i => vec ![1, 1, 0, 0] i + vec ![1, 2, 0, 0] i) = fun i => 2 * epsAxis 0 i := by
  refine ⟨by decide, by decide, ?_⟩
  funext i; fin_cases i <;> decide

/-- **Exactly six ordered root pairs make the coordinate axis step `2e₀`.** -/
theorem epsAxis_words_count :
    ((Finset.univ : Finset (Tri × Tri)).filter fun p =>
      IsRoot p.1 ∧ IsRoot p.2 ∧ ∀ i, val (p.1 i) + val (p.2 i) = 2 * epsAxis 0 i).card = 6 := by
  decide +kernel

/-! ## Spatial axes: clock-silent norm-4 vectors -/

/-- The six clock-silent norm-4 vectors (three axes and their negatives). -/
def spatial : Finset Tri :=
  Finset.univ.filter fun t =>
    IsRoot t = false ∧ (∑ i, (val (t i)) ^ 2) = 4 ∧ ∑ i, val (t i) = 0

theorem spatial_card : spatial.card = 6 := by decide +kernel

/-- The representative spatial axis `h = (1,1,−1,−1)`. -/
def h : Tri := ![1, 1, 2, 2]

theorem h_mem_spatial : h ∈ spatial := by decide +kernel

/-- **The spatial axis `h` is not a root** (its norm is 4). -/
theorem h_not_root : ¬ IsRoot h := by decide +kernel

/-- **The spatial axis `h` is a sum of two roots.** -/
theorem h_two_roots :
    IsRoot ![1, 1, 0, 0] ∧ IsRoot ![0, 0, 2, 2] ∧
      (fun i => vec ![1, 1, 0, 0] i + vec ![0, 0, 2, 2] i) = vec h := by
  refine ⟨by decide, by decide, ?_⟩
  funext i; fin_cases i <;> decide

/-- **Exactly six ordered root pairs sum to `h`.** -/
theorem h_words_count :
    ((Finset.univ : Finset (Tri × Tri)).filter fun p =>
      IsRoot p.1 ∧ IsRoot p.2 ∧ ∀ i, val (p.1 i) + val (p.2 i) = val (h i)).card = 6 := by
  decide +kernel

end PMAction.AxisHop
