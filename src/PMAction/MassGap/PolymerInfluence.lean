import PMAction.MassGap.PolymerCorrelation

/-!
# Influence of a far set of polymers (supersolution form)

`PolymerDecay.ratio_decay` needs two allowed sets to agree on *every* polymer within `k`
incompatibility steps. In a contour gas that never holds: a small contour is incompatible with
arbitrarily large contours. This file replaces depth by an **influence weight**.

Setting: two allowed sets `S`, `S'` that differ only on a set `E` of polymers. A weight
`f : P → ℝ` is a **supersolution** if, for every `γ ∉ E`,
`x_γ · Σ_{r incompatible with γ} g r ≤ f γ`, where `g r = f r / (1 − x_r)` for `r ∉ E` and
`g r = 1 / (1 − x_r)` for `r ∈ E`.

* `peel_diff`: the quotient `Z(T \ N) / Z T`, with `N` the incompatible neighbours of `γ`, is
  compared between `T` and `T'` even when they differ on `N` (polymers of `E`).
* `influence`: for a supersolution `f`, every `γ ∉ E` present in both sets has
  `|ρ_S(γ) − ρ_{S'}(γ)| ≤ f γ`. The proof is strong induction on the size of the allowed sets,
  since every recursive call removes polymers.

`f` is a sum over chains of incompatible polymers from `γ` to `E`, each weighted by
`x / (1 − x)`. For a contour gas, a supersolution decaying like `μ^{distance to E}` exists once
the activity is small (`PMGap`).
-/

namespace PMAction.MassGap.PolymerInfluence
open Finset PolymerConvergence PolymerDecay PolymerCorrelation

variable {P : Type*} [Fintype P] [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc]
  (w : P → ℝ)

section Bounds
variable (x : P → ℝ) (hsymm : ∀ a b, inc a b → inc b a) (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ < 1)
  (hw : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b))

include hsymm hx0 hx1 hw

/-- Peeling one polymer: `Z(U \ {r}) / Z U` is `1 / ρ_U(r)` if `r ∈ U` and `1` otherwise. -/
lemma peel_one (U : Finset P) (r : P) :
    Z inc w (U.erase r) / Z inc w U = if r ∈ U then 1 / ratio inc w U r else 1 := by
  have hpos := Z_pos inc w x hsymm hx0 hx1 hw
  split_ifs with hr
  · unfold ratio
    have := hpos U; have := hpos (U.erase r); field_simp
  · rw [erase_eq_of_notMem hr, div_self (hpos U).ne']

lemma peel_one_bounds (U : Finset P) (r : P) :
    True ∧ Z inc w (U.erase r) / Z inc w U ≤ 1 / (1 - x r) := by
  refine ⟨trivial, ?_⟩
  rw [peel_one inc w x hsymm hx0 hx1 hw]
  have h1x : 0 < 1 - x r := by linarith [hx1 r]
  have h0 := hx0 r
  split_ifs with hr
  · have hb := ratio_bounds inc w x hsymm hx0 hx1 hw U hr
    exact div_le_div_of_nonneg_left zero_le_one h1x hb.1
  · rw [le_div_iff₀ h1x]; linarith

/-- The peeled quotient is positive. -/
lemma quot_pos (U A : Finset P) : 0 < Z inc w (U \ A) / Z inc w U :=
  div_pos (Z_pos inc w x hsymm hx0 hx1 hw _) (Z_pos inc w x hsymm hx0 hx1 hw _)

/-- The peeled quotient is at most `Π (1 − x)⁻¹`. -/
lemma quot_le' (U A : Finset P) :
    Z inc w (U \ A) / Z inc w U ≤ 1 / ∏ r ∈ A, (1 - x r) := by
  induction A using Finset.induction_on with
  | empty =>
    simp [div_self (Z_pos inc w x hsymm hx0 hx1 hw U).ne']
  | @insert a A ha ih =>
    have e : U \ insert a A = (U \ A).erase a := by
      ext y; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    have hsplit : Z inc w (U \ insert a A) / Z inc w U =
        (Z inc w ((U \ A).erase a) / Z inc w (U \ A)) * (Z inc w (U \ A) / Z inc w U) := by
      rw [e]; have := Z_pos inc w x hsymm hx0 hx1 hw (U \ A); field_simp
    rw [hsplit, prod_insert ha]
    have hb := (peel_one_bounds inc w x hsymm hx0 hx1 hw (U \ A) a).2
    have hq := quot_pos inc w x hsymm hx0 hx1 hw U A
    have h1x : 0 < 1 - x a := by linarith [hx1 a]
    have hPi : 0 < ∏ r ∈ A, (1 - x r) := prod_pos fun r _ => by linarith [hx1 r]
    calc Z inc w ((U \ A).erase a) / Z inc w (U \ A) * (Z inc w (U \ A) / Z inc w U)
        ≤ 1 / (1 - x a) * (1 / ∏ r ∈ A, (1 - x r)) :=
          mul_le_mul hb ih hq.le (by positivity)
      _ = 1 / ((1 - x a) * ∏ r ∈ A, (1 - x r)) := by field_simp

/-- **Peeling with asymmetric membership.** If each peeling step's factor differs by at most
`η r` between `T` and `T'`, the peeled quotients differ by at most
`(Σ_{r∈A} η r (1 − x_r)⁻¹ ... )` in the multiplicative form below. -/
theorem peel_diff (T T' : Finset P) (η : P → ℝ) (hη : ∀ r, 0 ≤ η r) :
    ∀ A : Finset P,
      (∀ B ⊆ A, ∀ r ∈ A, r ∉ B →
        |Z inc w ((T \ B).erase r) / Z inc w (T \ B) -
          Z inc w ((T' \ B).erase r) / Z inc w (T' \ B)| ≤ η r) →
      |Z inc w (T \ A) / Z inc w T - Z inc w (T' \ A) / Z inc w T'| ≤
        (∑ r ∈ A, η r) / ∏ r ∈ A, (1 - x r) := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _
    simp [div_self (Z_pos inc w x hsymm hx0 hx1 hw T).ne',
      div_self (Z_pos inc w x hsymm hx0 hx1 hw T').ne']
  | @insert a A ha ih =>
    intro hstep
    have ih' := ih fun B hB r hr hrB => hstep B (hB.trans (subset_insert a A)) r
      (mem_insert_of_mem hr) hrB
    have e : ∀ U : Finset P, U \ insert a A = (U \ A).erase a := by
      intro U; ext y; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    have hsplit : ∀ U : Finset P, Z inc w (U \ insert a A) / Z inc w U =
        (Z inc w ((U \ A).erase a) / Z inc w (U \ A)) * (Z inc w (U \ A) / Z inc w U) := by
      intro U; rw [e]; have := Z_pos inc w x hsymm hx0 hx1 hw (U \ A); field_simp
    rw [hsplit T, hsplit T', sum_insert ha, prod_insert ha]
    set p := Z inc w ((T \ A).erase a) / Z inc w (T \ A)
    set p' := Z inc w ((T' \ A).erase a) / Z inc w (T' \ A)
    set qq := Z inc w (T \ A) / Z inc w T
    set qq' := Z inc w (T' \ A) / Z inc w T'
    have hp := hstep A (subset_insert a A) a (mem_insert_self a A) ha
    have hpb := (peel_one_bounds inc w x hsymm hx0 hx1 hw (T \ A) a).2
    have hq'b := quot_le' inc w x hsymm hx0 hx1 hw T' A
    have hq'0 := (quot_pos inc w x hsymm hx0 hx1 hw T' A).le
    have h1x : 0 < 1 - x a := by linarith [hx1 a]
    have hPi : 0 < ∏ r ∈ A, (1 - x r) := prod_pos fun r _ => by linarith [hx1 r]
    have hs0 : 0 ≤ ∑ r ∈ A, η r := sum_nonneg fun r _ => hη r
    -- `|p qq − p' qq'| ≤ p |qq − qq'| + qq' |p − p'|`
    have hp0 : 0 ≤ p := (div_pos (Z_pos inc w x hsymm hx0 hx1 hw _)
      (Z_pos inc w x hsymm hx0 hx1 hw _)).le
    calc |p * qq - p' * qq'| = |p * (qq - qq') + qq' * (p - p')| := by ring_nf
      _ ≤ |p * (qq - qq')| + |qq' * (p - p')| := abs_add_le _ _
      _ = p * |qq - qq'| + qq' * |p - p'| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq'0]
      _ ≤ 1 / (1 - x a) * ((∑ r ∈ A, η r) / ∏ r ∈ A, (1 - x r)) +
            (1 / ∏ r ∈ A, (1 - x r)) * η a :=
          add_le_add (mul_le_mul hpb ih' (abs_nonneg _) (by positivity))
            (mul_le_mul hq'b hp (abs_nonneg _) (by positivity))
      _ = (∑ r ∈ A, η r) / ((1 - x a) * ∏ r ∈ A, (1 - x r)) + η a / ∏ r ∈ A, (1 - x r) := by
          field_simp
      _ ≤ (∑ r ∈ A, η r) / ((1 - x a) * ∏ r ∈ A, (1 - x r)) +
            η a / ((1 - x a) * ∏ r ∈ A, (1 - x r)) := by
          apply add_le_add_right
          apply div_le_div_of_nonneg_left (hη a) (by positivity)
          have hxa := hx0 a
          nlinarith
      _ = (η a + ∑ r ∈ A, η r) / ((1 - x a) * ∏ r ∈ A, (1 - x r)) := by ring

/-- The peeling factor lies in `[1/(1+x), 1/(1−x)]`. -/
lemma peel_factor_mem (U : Finset P) (r : P) :
    1 / (1 + x r) ≤ Z inc w (U.erase r) / Z inc w U ∧
      Z inc w (U.erase r) / Z inc w U ≤ 1 / (1 - x r) := by
  rw [peel_one inc w x hsymm hx0 hx1 hw]
  have h1x : 0 < 1 - x r := by linarith [hx1 r]
  have h0 := hx0 r
  split_ifs with hr
  · have hb := ratio_bounds inc w x hsymm hx0 hx1 hw U hr
    have hp : 0 < ratio inc w U r := by linarith [hb.1]
    exact ⟨div_le_div_of_nonneg_left zero_le_one hp hb.2,
      div_le_div_of_nonneg_left zero_le_one h1x hb.1⟩
  · constructor
    · rw [div_le_iff₀ (by linarith)]; linarith
    · rw [le_div_iff₀ h1x]; linarith

/-- The per-neighbour step bound: `f r / (1 − x_r)²` off `E`, `2 x_r / (1 − x_r)²` on `E`. -/
noncomputable def stepBound (E : Finset P) (f : P → ℝ) (r : P) : ℝ :=
  if r ∈ E then 2 * x r / (1 - x r) ^ 2 else f r / (1 - x r) ^ 2

omit [Fintype P] hsymm hx1 hw in
lemma stepBound_nonneg (E : Finset P) (f : P → ℝ) (hf0 : ∀ γ, 0 ≤ f γ) (r : P) :
    0 ≤ stepBound x E f r := by
  unfold stepBound
  have := hx0 r; have := hf0 r
  split_ifs <;> positivity

/-- **Influence of a far set.** If `f` is a supersolution, every polymer outside `E` present in
two allowed sets that differ only on `E` has ratios within `f γ` of each other. -/
theorem influence (E : Finset P) (f : P → ℝ) (hf0 : ∀ γ, 0 ≤ f γ)
    (hsuper : ∀ γ, γ ∉ E → x γ * ∑ r ∈ nbhd inc γ, stepBound x E f r ≤ f γ) :
    ∀ (n : ℕ) (S S' : Finset P), (S ∪ S').card ≤ n → (∀ δ, δ ∉ E → (δ ∈ S ↔ δ ∈ S')) →
      ∀ γ, γ ∈ S → γ ∈ S' → γ ∉ E → |ratio inc w S γ - ratio inc w S' γ| ≤ f γ := by
  intro n
  induction n with
  | zero =>
    intro S S' hc _ γ hγ _ _
    have : S ∪ S' = ∅ := card_eq_zero.mp (Nat.le_zero.mp hc)
    exact absurd (mem_union_left S' hγ) (by rw [this]; exact Finset.notMem_empty γ)
  | succ n ih =>
    intro S S' hc hSS γ hγ hγ' hγE
    set T := S.erase γ with hT
    set T' := S'.erase γ with hT'
    set N := nbhd inc γ with hN
    -- the ratio in terms of the peeled quotient over all of `N`
    have hform : ∀ U : Finset P, γ ∈ U →
        ratio inc w U γ = 1 + w γ * (Z inc w (U.erase γ \ N) / Z inc w (U.erase γ)) := by
      intro U hU
      have h := ratio_form inc w x hsymm hx0 hx1 hw U hU ((U.erase γ).filter fun b => inc γ b) rfl
      have e : U.erase γ \ (U.erase γ).filter (fun b => inc γ b) = U.erase γ \ N := by
        ext b
        simp only [hN, nbhd, mem_sdiff, mem_filter, mem_erase, mem_univ, true_and]
        tauto
      rw [h, e]
    rw [hform S hγ, hform S' hγ', add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
    -- the recursive calls are on strictly smaller sets
    have hsmall : ∀ B : Finset P, ((T \ B) ∪ (T' \ B)).card ≤ n := by
      intro B
      have hsub : (T \ B) ∪ (T' \ B) ⊆ (S ∪ S').erase γ := by
        intro y hy
        simp only [hT, hT', mem_union, mem_sdiff, mem_erase] at hy ⊢
        rcases hy with ⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr h2⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_union_left S' hγ)] at this
      omega
    have hstep : ∀ B ⊆ N, ∀ r ∈ N, r ∉ B →
        |Z inc w ((T \ B).erase r) / Z inc w (T \ B) -
          Z inc w ((T' \ B).erase r) / Z inc w (T' \ B)| ≤ stepBound x E f r := by
      intro B _ r _ _
      have h1x : 0 < 1 - x r := by linarith [hx1 r]
      have hxr := hx0 r
      by_cases hrE : r ∈ E
      · -- both factors lie in `[1/(1+x), 1/(1−x)]`
        have i1 := peel_factor_mem inc w x hsymm hx0 hx1 hw (T \ B) r
        have i2 := peel_factor_mem inc w x hsymm hx0 hx1 hw (T' \ B) r
        have hw2 : 1 / (1 - x r) - 1 / (1 + x r) ≤ 2 * x r / (1 - x r) ^ 2 := by
          rw [div_sub_div _ _ h1x.ne' (by linarith), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith [mul_nonneg hxr hxr]
        simp only [stepBound, hrE, ↓reduceIte]
        rw [abs_le]
        constructor <;> linarith [i1.1, i1.2, i2.1, i2.2]
      · simp only [stepBound, hrE, ↓reduceIte]
        rw [peel_one inc w x hsymm hx0 hx1 hw, peel_one inc w x hsymm hx0 hx1 hw]
        have hmem : r ∈ T \ B ↔ r ∈ T' \ B := by
          simp only [hT, hT', mem_sdiff, mem_erase]; rw [hSS r hrE]
        by_cases hr : r ∈ T \ B
        · have hr' := hmem.mp hr
          simp only [hr, hr', ↓reduceIte]
          have hSS' : ∀ δ, δ ∉ E → (δ ∈ T \ B ↔ δ ∈ T' \ B) := by
            intro δ hδ; simp only [hT, hT', mem_sdiff, mem_erase]; rw [hSS δ hδ]
          have hd := ih (T \ B) (T' \ B) (hsmall B) hSS' r hr hr' hrE
          have b1 := (ratio_bounds inc w x hsymm hx0 hx1 hw (T \ B) hr).1
          have b2 := (ratio_bounds inc w x hsymm hx0 hx1 hw (T' \ B) hr').1
          have p1 : 0 < ratio inc w (T \ B) r := by linarith
          have p2 : 0 < ratio inc w (T' \ B) r := by linarith
          rw [div_sub_div _ _ p1.ne' p2.ne', one_mul, mul_one, abs_div,
            abs_of_pos (mul_pos p1 p2), div_le_div_iff₀ (mul_pos p1 p2) (by positivity),
            abs_sub_comm]
          have hcc : (1 - x r) ^ 2 ≤ ratio inc w (T \ B) r * ratio inc w (T' \ B) r := by
            rw [sq]; exact mul_le_mul b1 b2 h1x.le p1.le
          calc |ratio inc w (T \ B) r - ratio inc w (T' \ B) r| * (1 - x r) ^ 2
              ≤ f r * (1 - x r) ^ 2 := mul_le_mul_of_nonneg_right hd (by positivity)
            _ ≤ f r * (ratio inc w (T \ B) r * ratio inc w (T' \ B) r) :=
                mul_le_mul_of_nonneg_left hcc (hf0 r)
        · have hr' : r ∉ T' \ B := fun h => hr (hmem.mpr h)
          simp only [hr, hr', ↓reduceIte, sub_self, abs_zero]
          exact div_nonneg (hf0 r) (by positivity)
    have hq := peel_diff inc w x hsymm hx0 hx1 hw T T' (stepBound x E f)
      (stepBound_nonneg x hx0 E f hf0) N hstep
    have hPi : 0 < ∏ r ∈ N, (1 - x r) := prod_pos fun r _ => by linarith [hx1 r]
    calc |w γ| * |Z inc w (T \ N) / Z inc w T - Z inc w (T' \ N) / Z inc w T'|
        ≤ (x γ * ∏ r ∈ N, (1 - x r)) *
            ((∑ r ∈ N, stepBound x E f r) / ∏ r ∈ N, (1 - x r)) :=
          mul_le_mul (hw γ) hq (abs_nonneg _) (mul_nonneg (hx0 γ) hPi.le)
      _ = x γ * ∑ r ∈ N, stepBound x E f r := by field_simp
      _ ≤ f γ := hsuper γ hγE

/-- **Toggle closeness from influence.** For a supersolution `f`, toggling `a` changes `Z` by
factors that differ by at most `η a` between two allowed sets differing only on `E`, with
`η a = f a / (1 − x_a)²` off `E` and the crude `1/(1 − x_a) − (1 − x_a)` on `E`. -/
theorem tog_close (E : Finset P) (f : P → ℝ) (hf0 : ∀ γ, 0 ≤ f γ)
    (hsuper : ∀ γ, γ ∉ E → x γ * ∑ r ∈ nbhd inc γ, stepBound x E f r ≤ f γ)
    (U U' : Finset P) (hUU : ∀ δ, δ ∉ E → (δ ∈ U ↔ δ ∈ U')) (a : P) :
    |tog inc w U a - tog inc w U' a| ≤
      if a ∈ E then 1 / (1 - x a) - (1 - x a) else f a / (1 - x a) ^ 2 := by
  have h1x : 0 < 1 - x a := by linarith [hx1 a]
  have hxa := hx0 a
  have tbounds : ∀ V : Finset P, 1 - x a ≤ tog inc w V a ∧ tog inc w V a ≤ 1 / (1 - x a) := by
    intro V
    refine ⟨tog_lower inc w x hsymm hx0 hx1 hw V a, ?_⟩
    rw [tog_eq inc w x hsymm hx0 hx1 hw]
    split_ifs with ha
    · have hb := ratio_bounds inc w x hsymm hx0 hx1 hw V ha
      exact div_le_div_of_nonneg_left zero_le_one h1x hb.1
    · have hb := ratio_bounds inc w x hsymm hx0 hx1 hw (insert a V) (mem_insert_self a V)
      rw [le_div_iff₀ h1x]; nlinarith [hb.2]
  by_cases haE : a ∈ E
  · simp only [haE, ↓reduceIte]
    have b1 := tbounds U; have b2 := tbounds U'
    rw [abs_le]; constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  · simp only [haE, ↓reduceIte]
    have hmem : a ∈ U ↔ a ∈ U' := hUU a haE
    rw [tog_eq inc w x hsymm hx0 hx1 hw, tog_eq inc w x hsymm hx0 hx1 hw]
    have hcard : ∀ V V' : Finset P, (V ∪ V').card ≤ (V ∪ V').card := fun _ _ => le_rfl
    by_cases ha : a ∈ U
    · have ha' := hmem.mp ha
      simp only [ha, ha', ↓reduceIte]
      have hd := influence inc w x hsymm hx0 hx1 hw E f hf0 hsuper _ U U' (hcard U U') hUU a ha ha'
        haE
      have b1 := (ratio_bounds inc w x hsymm hx0 hx1 hw U ha).1
      have b2 := (ratio_bounds inc w x hsymm hx0 hx1 hw U' ha').1
      have p1 : 0 < ratio inc w U a := by linarith
      have p2 : 0 < ratio inc w U' a := by linarith
      rw [div_sub_div _ _ p1.ne' p2.ne', one_mul, mul_one, abs_div, abs_of_pos (mul_pos p1 p2),
        div_le_div_iff₀ (mul_pos p1 p2) (by positivity), abs_sub_comm]
      have hcc : (1 - x a) ^ 2 ≤ ratio inc w U a * ratio inc w U' a := by
        rw [sq]; exact mul_le_mul b1 b2 h1x.le p1.le
      calc |ratio inc w U a - ratio inc w U' a| * (1 - x a) ^ 2
          ≤ f a * (1 - x a) ^ 2 := mul_le_mul_of_nonneg_right hd (by positivity)
        _ ≤ f a * (ratio inc w U a * ratio inc w U' a) := mul_le_mul_of_nonneg_left hcc (hf0 a)
    · have ha' : a ∉ U' := fun h => ha (hmem.mpr h)
      simp only [ha, ha', ↓reduceIte]
      have hUU' : ∀ δ, δ ∉ E → (δ ∈ insert a U ↔ δ ∈ insert a U') := by
        intro δ hδ; simp only [mem_insert]; rw [hUU δ hδ]
      have hd := influence inc w x hsymm hx0 hx1 hw E f hf0 hsuper _ (insert a U) (insert a U')
        (hcard _ _) hUU' a (mem_insert_self a U) (mem_insert_self a U') haE
      refine hd.trans ?_
      rw [le_div_iff₀ (by positivity)]
      have : (1 - x a) ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_right (hf0 a) this

/-- **Decay of correlations from influence.** The cross-ratio form of `cross_ratio`, with the
per-toggle closeness `η` supplied (for example by `tog_close`). -/
theorem cross_ratio_of_close (S E : Finset P) (η : P → ℝ) (hη : ∀ a, 0 ≤ η a)
    (htog : ∀ a (U U' : Finset P), (∀ δ, δ ∉ E → (δ ∈ U ↔ δ ∈ U')) →
      |tog inc w U a - tog inc w U' a| ≤ η a) :
    ∀ D : Finset P,
      |Z inc w (symmDiff (symmDiff S E) D) * Z inc w S -
          Z inc w (symmDiff S D) * Z inc w (symmDiff S E)| ≤
        (∏ a ∈ D, (1 + η a / (1 - x a)) - 1) *
          (Z inc w (symmDiff S D) * Z inc w (symmDiff S E)) := by
  have hpos := Z_pos inc w x hsymm hx0 hx1 hw
  suffices hrel : ∀ D : Finset P,
      |(Z inc w (symmDiff (symmDiff S E) D) / Z inc w (symmDiff S E)) /
          (Z inc w (symmDiff S D) / Z inc w S) - 1| ≤ ∏ a ∈ D, (1 + η a / (1 - x a)) - 1 by
    intro D
    have h := hrel D
    have p1 := hpos (symmDiff S D); have p2 := hpos (symmDiff S E); have p3 := hpos S
    have hden : 0 < Z inc w (symmDiff S D) * Z inc w (symmDiff S E) := mul_pos p1 p2
    have heq : (Z inc w (symmDiff (symmDiff S E) D) / Z inc w (symmDiff S E)) /
        (Z inc w (symmDiff S D) / Z inc w S) - 1 =
        (Z inc w (symmDiff (symmDiff S E) D) * Z inc w S -
          Z inc w (symmDiff S D) * Z inc w (symmDiff S E)) /
          (Z inc w (symmDiff S D) * Z inc w (symmDiff S E)) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hden, div_le_iff₀ hden] at h
    exact h
  intro D
  induction D using Finset.induction_on with
  | empty =>
    have e1 : ∀ U : Finset P, symmDiff U (∅ : Finset P) = U := by
      intro U; ext y; simp [Finset.mem_symmDiff]
    have p1 := hpos S; have p2 := hpos (symmDiff S E)
    rw [e1, e1, div_self p2.ne', div_self p1.ne', prod_empty]; simp
  | @insert a D ha ih =>
    set U := symmDiff S D
    set U' := symmDiff (symmDiff S E) D
    have hUU : ∀ δ, δ ∉ E → (δ ∈ U' ↔ δ ∈ U) := by
      intro δ hδ; simp only [U, U', Finset.mem_symmDiff]; tauto
    have hclose := htog a U' U hUU
    have hlow := tog_lower inc w x hsymm hx0 hx1 hw U a
    have h1x : 0 < 1 - x a := by linarith [hx1 a]
    have hgpos : 0 < tog inc w U a := lt_of_lt_of_le h1x hlow
    have hF : Z inc w (symmDiff (symmDiff S E) (insert a D)) / Z inc w (symmDiff S E) =
        (Z inc w U' / Z inc w (symmDiff S E)) * tog inc w U' a := by
      rw [symmDiff_insert ha]; unfold tog
      have := hpos U'; have := hpos (symmDiff S E); field_simp; rfl
    have hG : Z inc w (symmDiff S (insert a D)) / Z inc w S =
        (Z inc w U / Z inc w S) * tog inc w U a := by
      rw [symmDiff_insert ha]; unfold tog
      have := hpos U; have := hpos S; field_simp; rfl
    rw [hF, hG, prod_insert ha]
    set δ := η a / (1 - x a)
    have hδ0 : 0 ≤ δ := div_nonneg (hη a) h1x.le
    have hv : |tog inc w U' a / tog inc w U a - 1| ≤ δ := by
      rw [div_sub_one hgpos.ne', abs_div, abs_of_pos hgpos, div_le_iff₀ hgpos]
      calc |tog inc w U' a - tog inc w U a| ≤ η a := hclose
        _ = δ * (1 - x a) := by simp only [δ]; field_simp
        _ ≤ δ * tog inc w U a := mul_le_mul_of_nonneg_left hlow hδ0
    have hP1 : 1 ≤ ∏ c ∈ D, (1 + η c / (1 - x c)) := by
      apply one_le_prod₀
      intro c _
      have : 0 < 1 - x c := by linarith [hx1 c]
      have : 0 ≤ η c / (1 - x c) := div_nonneg (hη c) this.le
      linarith
    have hre : (Z inc w U' / Z inc w (symmDiff S E) * tog inc w U' a) /
        (Z inc w U / Z inc w S * tog inc w U a) =
        ((Z inc w U' / Z inc w (symmDiff S E)) / (Z inc w U / Z inc w S)) *
          (tog inc w U' a / tog inc w U a) := by
      have := hpos U; have := hpos S; have := hpos U'; have := hpos (symmDiff S E)
      field_simp
    rw [hre, mul_comm (1 + δ)]
    exact prod_close ih hv hδ0 hP1

end Bounds

end PMAction.MassGap.PolymerInfluence
