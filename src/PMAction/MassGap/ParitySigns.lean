import PMAction.MassGap.HistorySum

/-!
# Parity observables are edge signs

A product of site spins `Π_{x∈A} (−1)^{σ(p_x)}` is not local in the contour picture, but it is a
**product of edge signs over the boundary**: fix for each `x` a walk `π_x` from the root to `p_x`.
Then `(−1)^{σ(p_x)} = (−1)^{#(boundary edges on π_x)}` (`ContourRepresentation.cut_parity`, with
`σ root = false`), so

`Π_{x∈A} (−1)^{σ(p_x)} = Π_{e ∈ cut σ} (−1)^{m_A(e)}`, with `m_A(e) = Σ_x (times π_x uses e)`.

* `sgn b = −1` if `b`, `1` otherwise.
* `spin_eq_cut`: one spin as a product over boundary edges.
* `parity_eq_cut`: the product over `A`.
* `observable_weight`: an observable times the edge weight `Π_{cut} ω` is the edge weight
  `Π_{cut} (sign · ω)`. Combined with `HistorySum.contour_gas_weighted`, every parity correlation
  of the history sum is a contour gas with the signed edge weight. If the walks `π_x` stay inside
  one time slice, only contours touching that slice change sign.
-/

namespace PMAction.MassGap.ParitySigns
open Finset ContourRepresentation HistorySum

variable {X : Type*} [Fintype X] [DecidableEq X] (Γ : SimpleGraph X) [DecidableRel Γ.Adj]

/-- `−1` for `true`, `1` for `false`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

lemma sgn_ne (a b : Bool) : sgn (a != b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

omit [Fintype X] in
lemma countP_eq_sum_count (C : Finset (Sym2 X)) (l : List (Sym2 X)) :
    l.countP (fun e => decide (e ∈ C)) = ∑ e ∈ C, l.count e := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, ih]
    simp only [List.count_cons, sum_add_distrib]
    by_cases ha : a ∈ C
    · simp [ha, beq_iff_eq, sum_ite_eq]
    · have : ∑ x ∈ C, (if a = x then 1 else 0) = 0 :=
        sum_eq_zero fun x hx => ite_eq_right_iff.mpr fun h => absurd (h ▸ hx) ha
      simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero, beq_iff_eq]
      simp only [eq_comm (a := a)] at this ⊢
      rw [this, add_zero]

omit [Fintype X] [DecidableRel Γ.Adj] in
/-- `(−1)^{hits}` as a product over `C` of `(−1)^{count}`. -/
lemma neg_one_pow_hits (C : Finset (Sym2 X)) {a b : X} (p : Γ.Walk a b) :
    (-1 : ℝ) ^ hits C p = ∏ e ∈ C, (-1 : ℝ) ^ p.edges.count e := by
  rw [prod_pow_eq_pow_sum, hits, countP_eq_sum_count]

/-- **One spin as a product over boundary edges.** -/
theorem spin_eq_cut {σ : X → Bool} {r : X} (hr : σ r = false) {p : X} (π : Γ.Walk r p) :
    sgn (σ p) = ∏ e ∈ cutSet Γ σ, (-1 : ℝ) ^ π.edges.count e := by
  rw [← neg_one_pow_hits]
  have h := cut_parity (cutSet_isCut Γ σ) π
  rw [hr] at h
  rcases Nat.even_or_odd (hits (cutSet Γ σ) π) with he | ho
  · have : σ p = false := by
      by_contra hc
      have : Odd (hits (cutSet Γ σ) π) := h.mpr (by cases hσ : σ p <;> simp_all)
      exact (Nat.not_even_iff_odd.mpr this) he
    rw [this, he.neg_one_pow]; simp [sgn]
  · have : σ p = true := by
      have := h.mp ho; cases hσ : σ p <;> simp_all
    rw [this, ho.neg_one_pow]; simp [sgn]

/-- The sign multiplicity of `A`. -/
def mult {r : X} {ι : Type*} (A : Finset ι) (pt : ι → X) (π : ∀ i, Γ.Walk r (pt i))
    (e : Sym2 X) : ℕ :=
  ∑ i ∈ A, (π i).edges.count e

/-- **A parity observable as a product over boundary edges.** -/
theorem parity_eq_cut {σ : X → Bool} {r : X} (hr : σ r = false) {ι : Type*} (A : Finset ι)
    (pt : ι → X) (π : ∀ i, Γ.Walk r (pt i)) :
    ∏ i ∈ A, sgn (σ (pt i)) = ∏ e ∈ cutSet Γ σ, (-1 : ℝ) ^ mult Γ A pt π e := by
  rw [prod_congr rfl fun i _ => spin_eq_cut Γ hr (π i), prod_comm]
  refine prod_congr rfl fun e _ => ?_
  rw [prod_pow_eq_pow_sum, mult]

/-- **An observable times an edge weight is a signed edge weight.** -/
theorem observable_weight {σ : X → Bool} {r : X} (hr : σ r = false) {ι : Type*} (A : Finset ι)
    (pt : ι → X) (π : ∀ i, Γ.Walk r (pt i)) (ω : Sym2 X → ℝ) :
    (∏ i ∈ A, sgn (σ (pt i))) * ∏ e ∈ cutSet Γ σ, ω e =
      ∏ e ∈ cutSet Γ σ, ((-1 : ℝ) ^ mult Γ A pt π e * ω e) := by
  rw [parity_eq_cut Γ hr A pt π, ← prod_mul_distrib]

end PMAction.MassGap.ParitySigns
