import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Matrix powers as history sums

* `power_eq_history`: for any matrix `T` on a finite state space,
  `⟨u, Tᴸ w⟩ = Σ_{h : Fin (L+1) → n} u(h 0) · Π_{s<L} T(h s, h (s+1)) · w(h L)`.
  The `L`-th power of a transfer matrix is the sum over histories of `L` ticks.
* `pm_weight`: for the PM transfer matrix `T(s,s') = r^{c s} q^{d(s,s')} r^{c s'}` with `r² = q`
  and the free end `v₀ s = r^{c s}`, a history's weight is `q^{Σ_t c(h t) + Σ_s d(h s, h (s+1))}`,
  that is, `q` to the history's PM cost (spatial boundary edges in every slice, plus flips
  between ticks).
-/

namespace PMAction.MassGap.TransferHistory
open Finset Matrix

variable {n : Type*} [Fintype n]

/-- **Matrix powers are history sums.** -/
theorem power_eq_history (T : Matrix n n ℝ) (u w : n → ℝ) :
    ∀ L : ℕ, u ⬝ᵥ (T.mulVec)^[L] w =
      ∑ h : Fin (L + 1) → n, u (h 0) * (∏ s : Fin L, T (h s.castSucc) (h s.succ)) *
        w (h (Fin.last L)) := by
  intro L
  induction L generalizing w with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Finset.univ_eq_empty, prod_empty, mul_one]
    rw [dotProduct]
    apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) n).symm
    intro s; simp [Fin.last]
  | succ L ih =>
    rw [Function.iterate_succ_apply, ih (T *ᵥ w)]
    -- split the last state off the history
    rw [← (Fin.snocEquiv fun _ : Fin (L + 2) => n).sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [mulVec, dotProduct, mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    have h0 : (Fin.snoc h s : Fin (L + 2) → n) 0 = h 0 := by
      have : (0 : Fin (L + 2)) = Fin.castSucc 0 := rfl
      rw [this, Fin.snoc_castSucc]
    have hs : ∀ i : Fin L, (Fin.snoc h s : Fin (L + 2) → n) i.castSucc.succ = h i.succ := by
      intro i
      have : (i.castSucc.succ : Fin (L + 2)) = Fin.castSucc i.succ := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    have hl : (Fin.snoc h s : Fin (L + 2) → n) (Fin.last L).succ = s := by
      have : ((Fin.last L).succ : Fin (L + 2)) = Fin.last (L + 1) := Fin.ext rfl
      rw [this, Fin.snoc_last]
    simp only [h0, hs, hl]
    ring

omit [Fintype n] in
/-- **PM history weight.** -/
theorem pm_weight {q r : ℝ} (hr : r ^ 2 = q) (c : n → ℕ) (d : n → n → ℕ) (L : ℕ)
    (h : Fin (L + 1) → n) :
    r ^ c (h 0) * (∏ s : Fin L, (r ^ c (h s.castSucc) * q ^ d (h s.castSucc) (h s.succ) *
      r ^ c (h s.succ))) * r ^ c (h (Fin.last L)) =
    q ^ (∑ t, c (h t) + ∑ s : Fin L, d (h s.castSucc) (h s.succ)) := by
  have hA : r ^ c (h 0) * ∏ s : Fin L, r ^ c (h s.succ) = ∏ t, r ^ c (h t) :=
    (Fin.prod_univ_succ (fun t => r ^ c (h t))).symm
  have hB : (∏ s : Fin L, r ^ c (h s.castSucc)) * r ^ c (h (Fin.last L)) = ∏ t, r ^ c (h t) :=
    (Fin.prod_univ_castSucc (fun t => r ^ c (h t))).symm
  have hsq : (∏ t, r ^ c (h t)) * (∏ t, r ^ c (h t)) = q ^ ∑ t, c (h t) := by
    rw [← prod_mul_distrib, ← prod_pow_eq_pow_sum]
    refine prod_congr rfl fun t _ => ?_
    rw [← pow_add, ← hr, ← pow_mul]; ring_nf
  calc r ^ c (h 0) * (∏ s : Fin L, (r ^ c (h s.castSucc) * q ^ d (h s.castSucc) (h s.succ) *
        r ^ c (h s.succ))) * r ^ c (h (Fin.last L))
      = (r ^ c (h 0) * ∏ s : Fin L, r ^ c (h s.succ)) *
          ((∏ s : Fin L, r ^ c (h s.castSucc)) * r ^ c (h (Fin.last L))) *
          ∏ s : Fin L, q ^ d (h s.castSucc) (h s.succ) := by
        rw [prod_mul_distrib, prod_mul_distrib]; ring
    _ = (∏ t, r ^ c (h t)) * (∏ t, r ^ c (h t)) * ∏ s : Fin L, q ^ d (h s.castSucc) (h s.succ) := by
        rw [hA, hB]
    _ = q ^ (∑ t, c (h t) + ∑ s : Fin L, d (h s.castSucc) (h s.succ)) := by
        rw [hsq, prod_pow_eq_pow_sum, pow_add]

end PMAction.MassGap.TransferHistory
