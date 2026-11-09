import PMAction.PolymerConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Decay of influence in the polymer gas

`PolymerConvergence.dobrushin` shows that removing one polymer `γ` changes the partition function
by a ratio `ρ_S(γ) = Z S / Z (S − γ)` in `[1 − x, 1 + x]`. A mass gap needs more: that ratio must
depend only exponentially weakly on polymers far from `γ`. This file proves that.

* `AgreeNear k S S' γ`: the allowed sets `S` and `S'` agree on every polymer within `k`
  incompatibility steps of `γ` (defined inductively).
* `AgreeNear.sdiff`: removing the same polymers from both sets keeps the agreement.
* `quot_diff`: the product step. Peeling the neighbours of `γ` one at a time, the quotient
  `Z(T \ R) / Z T` differs between `T` and `T'` by at most `|R| · ε / (1 − x)^(|R|+1)` when each
  peeled ratio differs by at most `ε`.
* `ratio_decay`: with uniform `x < 1` and at most `m` incompatible neighbours per polymer, if
  `S` and `S'` agree to depth `k` around `γ` then
  `|ρ_S(γ) − ρ_{S'}(γ)| ≤ 2x · θ^k`, where `θ = x · m / (1 − x)^(m+1)`.

For `θ < 1` this is exponential decay of influence with rate `−log θ` per incompatibility step.
None of the constants depends on the number of polymers, so the decay is uniform in volume.

## What is still open after this

Exponential decay of the ratios is the polymer-gas form of decay of correlations. To use
`GapFromDecay` the Euclidean correlation `⟨v, Tᵗ v⟩` of the transfer matrix must be written as such
a ratio for a polymer gas of spacetime contours, with `t` the time separation. That spacetime
encoding is the remaining bridge.
-/

namespace PMAction.PolymerDecay
open Finset PolymerConvergence

variable {P : Type*} [Fintype P] [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc]
  (w : P → ℝ)

/-- The single-polymer ratio `Z S / Z (S − γ)`. -/
noncomputable def ratio (S : Finset P) (γ : P) : ℝ := Z inc w S / Z inc w (S.erase γ)

/-- `S` and `S'` agree on all polymers within `k` incompatibility steps of `γ`. -/
def AgreeNear : ℕ → Finset P → Finset P → P → Prop
  | 0, S, S', γ => (γ ∈ S ↔ γ ∈ S')
  | k + 1, S, S', γ => (γ ∈ S ↔ γ ∈ S') ∧ ∀ δ ∈ nbhd inc γ, AgreeNear k S S' δ

theorem AgreeNear.mem {k : ℕ} {S S' : Finset P} {γ : P}
    (h : AgreeNear inc k S S' γ) : (γ ∈ S ↔ γ ∈ S') := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

/-- Removing the same polymers from both sets preserves agreement. -/
theorem AgreeNear.sdiff (A : Finset P) :
    ∀ (k : ℕ) (S S' : Finset P) (γ : P), AgreeNear inc k S S' γ →
      AgreeNear inc k (S \ A) (S' \ A) γ := by
  intro k
  induction k with
  | zero =>
    intro S S' γ h
    simp only [AgreeNear, mem_sdiff] at h ⊢
    rw [h]
  | succ k ih =>
    intro S S' γ h
    refine ⟨?_, fun δ hδ => ih S S' δ (h.2 δ hδ)⟩
    simp only [mem_sdiff]; rw [h.1]

section Bounds
variable (x : ℝ) (hsymm : ∀ a b, inc a b → inc b a) (hx0 : 0 ≤ x) (hx1 : x < 1)
  (hw : ∀ γ, |w γ| ≤ x * ∏ _b ∈ nbhd inc γ, (1 - x))

include hsymm hx0 hx1 hw

lemma Z_pos (S : Finset P) : 0 < Z inc w S :=
  (dobrushin inc w hsymm (fun _ => x) (fun _ => hx0) (fun _ => hx1) hw S).1

lemma ratio_bounds (S : Finset P) {γ : P} (hγ : γ ∈ S) :
    1 - x ≤ ratio inc w S γ ∧ ratio inc w S γ ≤ 1 + x := by
  have hg := (dobrushin inc w hsymm (fun _ => x) (fun _ => hx0) (fun _ => hx1) hw S).2 γ hγ
  have hp := Z_pos inc w x hsymm hx0 hx1 hw (S.erase γ)
  unfold ratio
  exact ⟨(le_div_iff₀ hp).mpr hg.1, (div_le_iff₀ hp).mpr hg.2⟩

/-- The peeled quotient is at most `(1 − x)^(−|R|)`. -/
lemma quot_le (T R : Finset P) (hR : R ⊆ T) :
    Z inc w (T \ R) / Z inc w T ≤ 1 / (1 - x) ^ R.card := by
  have hpeel := peel inc w (fun _ => x) (fun _ => hx1) T
    (fun U _ => dobrushin inc w hsymm (fun _ => x) (fun _ => hx0) (fun _ => hx1) hw U) R hR
  rw [prod_const] at hpeel
  have hT := Z_pos inc w x hsymm hx0 hx1 hw T
  have hq : 0 < (1 - x) ^ R.card := pow_pos (by linarith) _
  rw [div_le_div_iff₀ hT hq, one_mul]
  linarith [hpeel]

/-- **Product step.** If every ratio met while peeling `R` differs by at most `ε` between `T` and
`T'`, the peeled quotients differ by at most `|R| · ε / (1 − x)^(|R|+1)`. -/
theorem quot_diff (T T' : Finset P) (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ R : Finset P, R ⊆ T → R ⊆ T' →
      (∀ A ⊆ R, ∀ r ∈ R, r ∉ A → |ratio inc w (T \ A) r - ratio inc w (T' \ A) r| ≤ ε) →
      |Z inc w (T \ R) / Z inc w T - Z inc w (T' \ R) / Z inc w T'| ≤
        R.card * ε / (1 - x) ^ (R.card + 1) := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ _ _
    have h1 := Z_pos inc w x hsymm hx0 hx1 hw T
    have h2 := Z_pos inc w x hsymm hx0 hx1 hw T'
    simp [div_self h1.ne', div_self h2.ne']
  | @insert a R ha ih =>
    intro hRT hRT' hrat
    have hRT₀ : R ⊆ T := fun b hb => hRT (mem_insert_of_mem hb)
    have hRT₀' : R ⊆ T' := fun b hb => hRT' (mem_insert_of_mem hb)
    have ih' := ih hRT₀ hRT₀' fun A hA r hr hrA =>
      hrat A (hA.trans (subset_insert a R)) r (mem_insert_of_mem hr) hrA
    have haT : a ∈ T \ R := mem_sdiff.mpr ⟨hRT (mem_insert_self a R), ha⟩
    have haT' : a ∈ T' \ R := mem_sdiff.mpr ⟨hRT' (mem_insert_self a R), ha⟩
    have heq : ∀ U : Finset P, U \ insert a R = (U \ R).erase a := by
      intro U; ext b; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    -- notation
    set q := Z inc w (T \ R) / Z inc w T
    set q' := Z inc w (T' \ R) / Z inc w T'
    set ρ := ratio inc w (T \ R) a
    set ρ' := ratio inc w (T' \ R) a
    have hρ := (ratio_bounds inc w x hsymm hx0 hx1 hw (T \ R) haT).1
    have hρ' := (ratio_bounds inc w x hsymm hx0 hx1 hw (T' \ R) haT').1
    have h1x : 0 < 1 - x := by linarith
    have hρpos : 0 < ρ := lt_of_lt_of_le h1x hρ
    have hρpos' : 0 < ρ' := lt_of_lt_of_le h1x hρ'
    have hq'le : q' ≤ 1 / (1 - x) ^ R.card := quot_le inc w x hsymm hx0 hx1 hw T' R hRT₀'
    have hq'0 : 0 ≤ q' := div_nonneg (Z_pos inc w x hsymm hx0 hx1 hw _).le
      (Z_pos inc w x hsymm hx0 hx1 hw _).le
    have hdρ : |ρ - ρ'| ≤ ε := hrat R (subset_insert a R) a (mem_insert_self a R) ha
    -- the new quotient is the old one divided by the peeled ratio
    have hsplit : ∀ U : Finset P, a ∈ U \ R →
        Z inc w (U \ insert a R) / Z inc w U =
          (Z inc w (U \ R) / Z inc w U) / ratio inc w (U \ R) a := by
      intro U _
      have h1 := Z_pos inc w x hsymm hx0 hx1 hw U
      have h2 := Z_pos inc w x hsymm hx0 hx1 hw (U \ R)
      have h3 := Z_pos inc w x hsymm hx0 hx1 hw ((U \ R).erase a)
      unfold ratio
      rw [heq U]
      field_simp
    rw [hsplit T haT, hsplit T' haT', card_insert_of_notMem ha]
    -- |q/ρ − q'/ρ'| ≤ |q − q'|/ρ + q'|ρ − ρ'|/(ρρ')
    have hkey : q / ρ - q' / ρ' = (q - q') / ρ + q' * (ρ' - ρ) / (ρ * ρ') := by
      field_simp; ring
    rw [hkey]
    set c := 1 - x
    have hc1 : c ≤ 1 := by simp only [c]; linarith
    have hpc : ∀ n : ℕ, 0 < c ^ n := fun n => pow_pos h1x n
    have hA : |(q - q') / ρ| ≤ R.card * ε / c ^ (R.card + 2) := by
      rw [abs_div, abs_of_pos hρpos, div_le_iff₀ hρpos]
      calc |q - q'| ≤ R.card * ε / c ^ (R.card + 1) := ih'
        _ = R.card * ε / c ^ (R.card + 2) * c := by
            rw [pow_succ c (R.card + 1)]; field_simp
        _ ≤ R.card * ε / c ^ (R.card + 2) * ρ := by
            apply mul_le_mul_of_nonneg_left hρ
            exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) (hpc _).le
    have hB : |q' * (ρ' - ρ) / (ρ * ρ')| ≤ ε / c ^ (R.card + 2) := by
      rw [abs_div, abs_mul, abs_of_nonneg hq'0, abs_of_pos (mul_pos hρpos hρpos'),
        div_le_div_iff₀ (mul_pos hρpos hρpos') (hpc _), abs_sub_comm]
      have hcc : c * c ≤ ρ * ρ' := mul_le_mul hρ hρ' h1x.le hρpos.le
      have hq'c : q' * c ^ R.card ≤ 1 := by
        rw [le_div_iff₀ (hpc _)] at hq'le; exact hq'le
      calc q' * |ρ - ρ'| * c ^ (R.card + 2) = (q' * c ^ R.card) * |ρ - ρ'| * (c * c) := by ring
        _ ≤ 1 * ε * (ρ * ρ') := by
            apply mul_le_mul (mul_le_mul hq'c hdρ (abs_nonneg _) zero_le_one) hcc
              (mul_nonneg h1x.le h1x.le) (by positivity)
        _ = ε * (ρ * ρ') := by ring
    calc |(q - q') / ρ + q' * (ρ' - ρ) / (ρ * ρ')|
        ≤ |(q - q') / ρ| + |q' * (ρ' - ρ) / (ρ * ρ')| := abs_add_le _ _
      _ ≤ R.card * ε / c ^ (R.card + 2) + ε / c ^ (R.card + 2) := add_le_add hA hB
      _ = ((R.card + 1 : ℕ) : ℝ) * ε / c ^ (R.card + 1 + 1) := by push_cast; ring

/-- **Exponential decay of influence.** -/
theorem ratio_decay (m : ℕ) (hm : ∀ γ, (nbhd inc γ).card ≤ m) :
    ∀ (k : ℕ) (S S' : Finset P) (γ : P), γ ∈ S → γ ∈ S' → AgreeNear inc k S S' γ →
      |ratio inc w S γ - ratio inc w S' γ| ≤
        2 * x * (x * m / (1 - x) ^ (m + 1)) ^ k := by
  have h1x : 0 < 1 - x := by linarith
  set θ := x * m / (1 - x) ^ (m + 1) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (mul_nonneg hx0 (Nat.cast_nonneg m)) (pow_pos h1x _).le
  intro k
  induction k with
  | zero =>
    intro S S' γ hS hS' _
    have b1 := ratio_bounds inc w x hsymm hx0 hx1 hw S hS
    have b2 := ratio_bounds inc w x hsymm hx0 hx1 hw S' hS'
    rw [pow_zero, mul_one, abs_le]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  | succ k ih =>
    intro S S' γ hS hS' hagree
    set T := S.erase γ with hT
    set T' := S'.erase γ with hT'
    set R := T.filter fun b => inc γ b with hR
    have hRN : R ⊆ nbhd inc γ := by
      intro b hb
      simp only [hR, hT, mem_filter, mem_erase] at hb
      simp only [nbhd, mem_filter, mem_univ, true_and]
      exact ⟨hb.1.1, hb.2⟩
    have hR' : T'.filter (fun b => inc γ b) = R := by
      ext b
      simp only [hR, hT, hT', mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨hb, hbS⟩, hi⟩
        have hbn : b ∈ nbhd inc γ := by simp [nbhd, hb, hi]
        exact ⟨⟨hb, (hagree.2 b hbn).mem.mpr hbS⟩, hi⟩
      · rintro ⟨⟨hb, hbS⟩, hi⟩
        have hbn : b ∈ nbhd inc γ := by simp [nbhd, hb, hi]
        exact ⟨⟨hb, (hagree.2 b hbn).mem.mp hbS⟩, hi⟩
    have hRT : R ⊆ T := filter_subset _ _
    have hRT' : R ⊆ T' := by rw [← hR']; exact filter_subset _ _
    -- the ratio is `1 + w γ · (peeled quotient)`
    have hform : ∀ (U : Finset P), γ ∈ U → (U.erase γ).filter (fun b => inc γ b) = R →
        ratio inc w U γ = 1 + w γ * (Z inc w (U.erase γ \ R) / Z inc w (U.erase γ)) := by
      intro U hU hUR
      have hrec := Z_recursion inc w hsymm U hU
      have hC : compat inc U γ = U.erase γ \ R := by
        rw [← hUR]; ext b; simp only [compat, mem_sdiff, mem_filter]; tauto
      rw [hC] at hrec
      have hp := Z_pos inc w x hsymm hx0 hx1 hw (U.erase γ)
      unfold ratio
      rw [hrec]; field_simp
    rw [hform S hS rfl, hform S' hS' hR', add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
    -- every peeled ratio is within the depth-`k` bound
    have hpeeled : ∀ A ⊆ R, ∀ r ∈ R, r ∉ A →
        |ratio inc w (T \ A) r - ratio inc w (T' \ A) r| ≤ 2 * x * θ ^ k := by
      intro A _ r hr hrA
      have hrn : r ∈ nbhd inc γ := hRN hr
      have hag : AgreeNear inc k (S \ insert γ A) (S' \ insert γ A) r :=
        AgreeNear.sdiff inc (insert γ A) k S S' r (hagree.2 r hrn)
      have e1 : T \ A = S \ insert γ A := by
        ext b; simp only [hT, mem_sdiff, mem_erase, mem_insert]; tauto
      have e2 : T' \ A = S' \ insert γ A := by
        ext b; simp only [hT', mem_sdiff, mem_erase, mem_insert]; tauto
      have hrT : r ∈ T \ A := mem_sdiff.mpr ⟨hRT hr, hrA⟩
      have hrT' : r ∈ T' \ A := mem_sdiff.mpr ⟨hRT' hr, hrA⟩
      rw [e1] at hrT
      rw [e2] at hrT'
      rw [e1, e2]
      exact ih _ _ r hrT hrT' hag
    have hε : 0 ≤ 2 * x * θ ^ k := by positivity
    have hq := quot_diff inc w x hsymm hx0 hx1 hw T T' _ hε R hRT hRT' hpeeled
    have hwx : |w γ| ≤ x := by
      refine (hw γ).trans ?_
      calc x * ∏ b ∈ nbhd inc γ, (1 - x) ≤ x * 1 := by
            apply mul_le_mul_of_nonneg_left _ hx0
            rw [prod_const]; exact pow_le_one₀ h1x.le (by linarith)
        _ = x := mul_one x
    -- monotonicity of `n / (1 − x)^(n+1)` in `n`
    have hRm : R.card ≤ m := (card_le_card hRN).trans (hm γ)
    have hmono : (R.card : ℝ) * (2 * x * θ ^ k) / (1 - x) ^ (R.card + 1) ≤
        m * (2 * x * θ ^ k) / (1 - x) ^ (m + 1) := by
      have hpow : (1 - x) ^ (m + 1) ≤ (1 - x) ^ (R.card + 1) :=
        pow_le_pow_of_le_one h1x.le (by linarith) (by omega)
      apply div_le_div₀ (mul_nonneg (Nat.cast_nonneg m) hε)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hRm) hε) (pow_pos h1x _) hpow
    calc |w γ| * |Z inc w (T \ R) / Z inc w T - Z inc w (T' \ R) / Z inc w T'|
        ≤ x * (m * (2 * x * θ ^ k) / (1 - x) ^ (m + 1)) :=
          mul_le_mul hwx (hq.trans hmono) (abs_nonneg _) hx0
      _ = 2 * x * θ ^ (k + 1) := by rw [pow_succ, hθ]; ring

end Bounds

end PMAction.PolymerDecay
