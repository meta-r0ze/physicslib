import PMAction.MassGap.PolymerConvergence
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
* `quot_diff`: the product step. Peeling the neighbours `R` of `γ` one at a time, the quotient
  `Z(T \ R) / Z T` differs between `T` and `T'` by at most
  `(Σ_{r∈R} ε_r / (1 − x_r)) / Π_{r∈R} (1 − x_r)` when each peeled ratio at `r` differs by at
  most `ε_r`.
* `ratio_step`: combined with Dobrushin's condition the product cancels exactly, giving the
  influence recursion `|ρ_S(γ) − ρ_{S'}(γ)| ≤ x_γ · Σ_{r incompatible with γ} ε_r / (1 − x_r)`.
* `ratio_decay`: with per-polymer `x` and a size weight `b ≥ 1` (typically `b γ = |γ|`), if
  `Σ_{r incompatible with γ} x_r b_r / (1 − x_r) ≤ θ · b_γ` for every `γ`, and `S`, `S'` agree to
  depth `k` around `γ`, then `|ρ_S(γ) − ρ_{S'}(γ)| ≤ 2 x_γ b_γ θ^k`.

For `θ < 1` this is exponential decay of influence with rate `−log θ` per incompatibility step.
The hypothesis is per polymer and weighted by size, so it holds for contour gases with contours of
every size (`PolymerBridge` derives it from `ContourCount`). Nothing depends on the number of
polymers.

## What is still open after this

Exponential decay of the ratios is the polymer-gas form of decay of correlations. To use
`GapFromDecay` the Euclidean correlation `⟨v, Tᵗ v⟩` of the transfer matrix must be written as such
a ratio for a polymer gas of spacetime contours, with `t` the time separation. That spacetime
encoding is the remaining bridge.
-/

namespace PMAction.MassGap.PolymerDecay
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
variable (x : P → ℝ) (hsymm : ∀ a b, inc a b → inc b a) (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ < 1)
  (hw : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b))

include hsymm hx0 hx1 hw

lemma Z_pos (S : Finset P) : 0 < Z inc w S :=
  (dobrushin inc w hsymm x hx0 hx1 hw S).1

lemma ratio_bounds (S : Finset P) {γ : P} (hγ : γ ∈ S) :
    1 - x γ ≤ ratio inc w S γ ∧ ratio inc w S γ ≤ 1 + x γ := by
  have hg := (dobrushin inc w hsymm x hx0 hx1 hw S).2 γ hγ
  have hp := Z_pos inc w x hsymm hx0 hx1 hw (S.erase γ)
  unfold ratio
  exact ⟨(le_div_iff₀ hp).mpr hg.1, (div_le_iff₀ hp).mpr hg.2⟩

omit [Fintype P] [DecidableEq P] hsymm hx0 hw in
lemma prodR_pos (R : Finset P) : 0 < ∏ r ∈ R, (1 - x r) :=
  prod_pos fun r _ => by linarith [hx1 r]

/-- The peeled quotient is at most `1 / Π_R (1 − x)`. -/
lemma quot_le (T R : Finset P) (hR : R ⊆ T) :
    Z inc w (T \ R) / Z inc w T ≤ 1 / ∏ r ∈ R, (1 - x r) := by
  have hpeel := peel inc w x hx1 T
    (fun U _ => dobrushin inc w hsymm x hx0 hx1 hw U) R hR
  have hT := Z_pos inc w x hsymm hx0 hx1 hw T
  have hq := prodR_pos x hx1 R
  rw [div_le_div_iff₀ hT hq, one_mul]
  linarith [hpeel]

/-- **Product step.** -/
theorem quot_diff (T T' : Finset P) (ε : P → ℝ) (hε : ∀ r, 0 ≤ ε r) :
    ∀ R : Finset P, R ⊆ T → R ⊆ T' →
      (∀ A ⊆ R, ∀ r ∈ R, r ∉ A → |ratio inc w (T \ A) r - ratio inc w (T' \ A) r| ≤ ε r) →
      |Z inc w (T \ R) / Z inc w T - Z inc w (T' \ R) / Z inc w T'| ≤
        (∑ r ∈ R, ε r / (1 - x r)) / ∏ r ∈ R, (1 - x r) := by
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
    set q := Z inc w (T \ R) / Z inc w T
    set q' := Z inc w (T' \ R) / Z inc w T'
    set ρ := ratio inc w (T \ R) a
    set ρ' := ratio inc w (T' \ R) a
    set sR := ∑ r ∈ R, ε r / (1 - x r)
    set pR := ∏ r ∈ R, (1 - x r)
    have hρ := (ratio_bounds inc w x hsymm hx0 hx1 hw (T \ R) haT).1
    have hρ' := (ratio_bounds inc w x hsymm hx0 hx1 hw (T' \ R) haT').1
    have h1x : 0 < 1 - x a := by linarith [hx1 a]
    have hρpos : 0 < ρ := lt_of_lt_of_le h1x hρ
    have hρpos' : 0 < ρ' := lt_of_lt_of_le h1x hρ'
    have hpRpos : 0 < pR := prodR_pos x hx1 R
    have hs0 : 0 ≤ sR := sum_nonneg fun r _ => div_nonneg (hε r) (by linarith [hx1 r])
    have hq'le : q' ≤ 1 / pR := quot_le inc w x hsymm hx0 hx1 hw T' R hRT₀'
    have hq'0 : 0 ≤ q' := div_nonneg (Z_pos inc w x hsymm hx0 hx1 hw _).le
      (Z_pos inc w x hsymm hx0 hx1 hw _).le
    have hdρ : |ρ - ρ'| ≤ ε a := hrat R (subset_insert a R) a (mem_insert_self a R) ha
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
    rw [hsplit T haT, hsplit T' haT', sum_insert ha, prod_insert ha]
    have hkey : q / ρ - q' / ρ' = (q - q') / ρ + q' * (ρ' - ρ) / (ρ * ρ') := by
      field_simp; ring
    rw [hkey]
    have hA : |(q - q') / ρ| ≤ (sR / pR) / (1 - x a) := by
      rw [abs_div, abs_of_pos hρpos]
      calc |q - q'| / ρ ≤ (sR / pR) / ρ := div_le_div_of_nonneg_right ih' hρpos.le
        _ ≤ (sR / pR) / (1 - x a) :=
          div_le_div_of_nonneg_left (div_nonneg hs0 hpRpos.le) h1x hρ
    have hB : |q' * (ρ' - ρ) / (ρ * ρ')| ≤ (ε a / (1 - x a)) / (pR * (1 - x a)) := by
      rw [abs_div, abs_mul, abs_of_nonneg hq'0, abs_of_pos (mul_pos hρpos hρpos'), abs_sub_comm]
      have hcc : (1 - x a) * (1 - x a) ≤ ρ * ρ' := mul_le_mul hρ hρ' h1x.le hρpos.le
      rw [div_le_div_iff₀ (mul_pos hρpos hρpos') (mul_pos hpRpos h1x)]
      have hqpR : q' * pR ≤ 1 := by rw [le_div_iff₀ hpRpos] at hq'le; exact hq'le
      have hε0 := hε a
      calc q' * |ρ - ρ'| * (pR * (1 - x a))
          = (q' * pR) * |ρ - ρ'| * (1 - x a) := by ring
        _ ≤ 1 * ε a * (1 - x a) := by
            apply mul_le_mul_of_nonneg_right _ h1x.le
            exact mul_le_mul hqpR hdρ (abs_nonneg _) zero_le_one
        _ = ε a / (1 - x a) * ((1 - x a) * (1 - x a)) := by field_simp
        _ ≤ ε a / (1 - x a) * (ρ * ρ') :=
            mul_le_mul_of_nonneg_left hcc (div_nonneg hε0 h1x.le)
    calc |(q - q') / ρ + q' * (ρ' - ρ) / (ρ * ρ')|
        ≤ |(q - q') / ρ| + |q' * (ρ' - ρ) / (ρ * ρ')| := abs_add_le _ _
      _ ≤ (sR / pR) / (1 - x a) + (ε a / (1 - x a)) / (pR * (1 - x a)) := add_le_add hA hB
      _ = (ε a / (1 - x a) + sR) / ((1 - x a) * pR) := by field_simp; ring

/-- The ratio is `1 + w γ · (peeled quotient)`. -/
lemma ratio_form (S : Finset P) {γ : P} (hγ : γ ∈ S) (R : Finset P)
    (hR : (S.erase γ).filter (fun b => inc γ b) = R) :
    ratio inc w S γ = 1 + w γ * (Z inc w (S.erase γ \ R) / Z inc w (S.erase γ)) := by
  have hrec := Z_recursion inc w hsymm S hγ
  have hC : compat inc S γ = S.erase γ \ R := by
    rw [← hR]; ext b; simp only [compat, mem_sdiff, mem_filter]; tauto
  rw [hC] at hrec
  have hp := Z_pos inc w x hsymm hx0 hx1 hw (S.erase γ)
  unfold ratio
  rw [hrec]; field_simp

/-- **Exponential decay of influence (weighted).** -/
theorem ratio_decay (b : P → ℝ) (hb : ∀ γ, 1 ≤ b γ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (H : ∀ γ, ∑ r ∈ nbhd inc γ, x r * b r / (1 - x r) ≤ θ * b γ) :
    ∀ (k : ℕ) (S S' : Finset P) (γ : P), γ ∈ S → γ ∈ S' → AgreeNear inc k S S' γ →
      |ratio inc w S γ - ratio inc w S' γ| ≤ 2 * x γ * b γ * θ ^ k := by
  intro k
  induction k with
  | zero =>
    intro S S' γ hS hS' _
    have b1 := ratio_bounds inc w x hsymm hx0 hx1 hw S hS
    have b2 := ratio_bounds inc w x hsymm hx0 hx1 hw S' hS'
    have hxb : x γ ≤ x γ * b γ := le_mul_of_one_le_right (hx0 γ) (hb γ)
    rw [pow_zero, mul_one, abs_le]
    constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2]
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
    rw [ratio_form inc w x hsymm hx0 hx1 hw S hS R rfl,
      ratio_form inc w x hsymm hx0 hx1 hw S' hS' R hR', add_sub_add_left_eq_sub, ← mul_sub,
      abs_mul]
    set ε : P → ℝ := fun r => 2 * x r * b r * θ ^ k with hεdef
    have hε : ∀ r, 0 ≤ ε r := fun r => by
      have := hx0 r; have := hb r; simp only [hεdef]; positivity
    have hpeeled : ∀ A ⊆ R, ∀ r ∈ R, r ∉ A →
        |ratio inc w (T \ A) r - ratio inc w (T' \ A) r| ≤ ε r := by
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
    have hq := quot_diff inc w x hsymm hx0 hx1 hw T T' ε hε R hRT hRT' hpeeled
    have hpR := prodR_pos x hx1 R
    -- `Π_N ≤ Π_R` since `R ⊆ N` and every factor is in `(0,1]`
    have hNR : ∏ r ∈ nbhd inc γ, (1 - x r) ≤ ∏ r ∈ R, (1 - x r) := by
      rw [← prod_sdiff hRN]
      have h1 : ∏ r ∈ nbhd inc γ \ R, (1 - x r) ≤ 1 :=
        prod_le_one₀ (fun r _ => by linarith [hx1 r]) (fun r _ => by linarith [hx0 r])
      nlinarith
    have hterm : ∀ r, 0 ≤ ε r / (1 - x r) := fun r => div_nonneg (hε r) (by linarith [hx1 r])
    have hsumRN : ∑ r ∈ R, ε r / (1 - x r) ≤ ∑ r ∈ nbhd inc γ, ε r / (1 - x r) :=
      sum_le_sum_of_subset_of_nonneg hRN fun r _ _ => hterm r
    have hsumeq : ∑ r ∈ nbhd inc γ, ε r / (1 - x r) =
        2 * θ ^ k * ∑ r ∈ nbhd inc γ, x r * b r / (1 - x r) := by
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_; simp only [hεdef]; ring
    have hs0 : 0 ≤ ∑ r ∈ R, ε r / (1 - x r) := sum_nonneg fun r _ => hterm r
    calc |w γ| * |Z inc w (T \ R) / Z inc w T - Z inc w (T' \ R) / Z inc w T'|
        ≤ (x γ * ∏ r ∈ nbhd inc γ, (1 - x r)) *
            ((∑ r ∈ R, ε r / (1 - x r)) / ∏ r ∈ R, (1 - x r)) :=
          mul_le_mul (hw γ) hq (abs_nonneg _) (mul_nonneg (hx0 γ)
            (prod_nonneg fun r _ => by linarith [hx1 r]))
      _ ≤ (x γ * ∏ r ∈ R, (1 - x r)) * ((∑ r ∈ R, ε r / (1 - x r)) / ∏ r ∈ R, (1 - x r)) := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNR (hx0 γ))
          exact div_nonneg hs0 hpR.le
      _ = x γ * ∑ r ∈ R, ε r / (1 - x r) := by field_simp
      _ ≤ x γ * ∑ r ∈ nbhd inc γ, ε r / (1 - x r) :=
          mul_le_mul_of_nonneg_left hsumRN (hx0 γ)
      _ = x γ * (2 * θ ^ k * ∑ r ∈ nbhd inc γ, x r * b r / (1 - x r)) := by rw [hsumeq]
      _ ≤ x γ * (2 * θ ^ k * (θ * b γ)) := by
          apply mul_le_mul_of_nonneg_left _ (hx0 γ)
          exact mul_le_mul_of_nonneg_left (H γ) (by positivity)
      _ = 2 * x γ * b γ * θ ^ (k + 1) := by ring

end Bounds

end PMAction.MassGap.PolymerDecay
