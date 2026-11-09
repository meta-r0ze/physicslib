import PMAction.PolymerDecay
import PMAction.ContourCount
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# From contour counting to the polymer-gas hypotheses

`PolymerConvergence.dobrushin` and `PolymerDecay.ratio_decay` take two per-polymer hypotheses.
This file derives both from **per-site** sums, and those per-site sums from the volume-independent
contour count in `ContourCount`.

Setting: polymers `P` (contours) with a support `supp γ ⊆ V` of sites and a closed neighbourhood
`near γ ⊇ supp γ`. The geometric premise `hcov` says two incompatible polymers touch: if `γ'` is
incompatible with `γ`, then `γ'` has a site in `near γ`. `fibre v` is the set of polymers through
site `v`.

* `prod_cover_ge`, `sum_cover_le`: products of factors in `[0,1]` and sums of nonnegative terms
  over a set covered by fibres, compared with the fibre-by-fibre product or sum.
* `nbhd_prod_ge`: if `Σ_{γ ∋ v} x γ ≤ s ≤ 1` at every site, then
  `Π_{γ' incompatible with γ} (1 − x γ') ≥ (1 − s)^|near γ|`.
* `dobrushin_of_activity`: with activities `|w γ| ≤ q^|γ|`, KP weights `x γ = (q c)^|γ|`,
  `|near γ| ≤ K |γ|` and `c (1 − s)^K ≥ 1`, Dobrushin's condition holds.
* `decay_of_sites`: with `Σ_{γ ∋ v} x γ |γ| ≤ s₁` and `x ≤ x̄ < 1`, the weighted decay
  hypothesis of `ratio_decay` holds with `b γ = |γ|` and `θ = K s₁ / (1 − x̄)`.
* `site_sum_le`, `site_sum_weighted_le`: for connected contours on a graph of degree `≤ D`, the
  per-site sums are at most `y / (1 − D²y)` and `y / (1 − 2D²y)` (with `y = q c`), by
  `ContourCount`.

Every constant is local (`D`, `K`, `q`, `c`), so all hypotheses hold uniformly in the volume once
`q` is small enough.
-/

namespace PMAction.PolymerBridge
open Finset PolymerConvergence

section Cover
variable {P V : Type*} [DecidableEq P] [DecidableEq V]

/-- Products of factors in `[0,1]` shrink on supersets. -/
lemma prod_superset_le (f : P → ℝ) (h0 : ∀ γ, 0 ≤ f γ) (h1 : ∀ γ, f γ ≤ 1)
    {X Y : Finset P} (hXY : X ⊆ Y) : ∏ γ ∈ Y, f γ ≤ ∏ γ ∈ X, f γ := by
  rw [← prod_sdiff hXY]
  have hA : ∏ γ ∈ Y \ X, f γ ≤ 1 := prod_le_one₀ (fun γ _ => h0 γ) (fun γ _ => h1 γ)
  have hB : 0 ≤ ∏ γ ∈ X, f γ := prod_nonneg fun γ _ => h0 γ
  nlinarith

lemma prod_union_ge (f : P → ℝ) (h0 : ∀ γ, 0 ≤ f γ) (h1 : ∀ γ, f γ ≤ 1) (X Y : Finset P) :
    (∏ γ ∈ X, f γ) * ∏ γ ∈ Y, f γ ≤ ∏ γ ∈ X ∪ Y, f γ := by
  rw [← union_sdiff_self_eq_union, prod_union disjoint_sdiff]
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun γ _ => h0 γ)
  exact prod_superset_le f h0 h1 sdiff_subset

/-- **Product over a covered set.** -/
lemma prod_cover_ge (f : P → ℝ) (h0 : ∀ γ, 0 ≤ f γ) (h1 : ∀ γ, f γ ≤ 1)
    (A : Finset P) (B : Finset V) (F : V → Finset P) (hcov : A ⊆ B.biUnion F) :
    ∏ v ∈ B, ∏ γ ∈ F v, f γ ≤ ∏ γ ∈ A, f γ := by
  refine le_trans ?_ (prod_superset_le f h0 h1 hcov)
  clear hcov
  induction B using Finset.induction_on with
  | empty => simp
  | @insert v B hv ih =>
    rw [prod_insert hv, biUnion_insert]
    calc (∏ γ ∈ F v, f γ) * ∏ u ∈ B, ∏ γ ∈ F u, f γ
        ≤ (∏ γ ∈ F v, f γ) * ∏ γ ∈ B.biUnion F, f γ :=
          mul_le_mul_of_nonneg_left ih (prod_nonneg fun γ _ => h0 γ)
      _ ≤ ∏ γ ∈ F v ∪ B.biUnion F, f γ := prod_union_ge f h0 h1 _ _

/-- **Sum over a covered set.** -/
lemma sum_cover_le (g : P → ℝ) (h0 : ∀ γ, 0 ≤ g γ)
    (A : Finset P) (B : Finset V) (F : V → Finset P) (hcov : A ⊆ B.biUnion F) :
    ∑ γ ∈ A, g γ ≤ ∑ v ∈ B, ∑ γ ∈ F v, g γ := by
  refine le_trans (sum_le_sum_of_subset_of_nonneg hcov fun γ _ _ => h0 γ) ?_
  clear hcov
  induction B using Finset.induction_on with
  | empty => simp
  | @insert v B hv ih =>
    rw [sum_insert hv, biUnion_insert]
    calc ∑ γ ∈ F v ∪ B.biUnion F, g γ
        = ∑ γ ∈ F v, g γ + ∑ γ ∈ B.biUnion F \ F v, g γ := by
          rw [← union_sdiff_self_eq_union, sum_union disjoint_sdiff]
      _ ≤ ∑ γ ∈ F v, g γ + ∑ γ ∈ B.biUnion F, g γ :=
          add_le_add (le_refl _) (sum_le_sum_of_subset_of_nonneg sdiff_subset fun γ _ _ => h0 γ)
      _ ≤ ∑ γ ∈ F v, g γ + ∑ u ∈ B, ∑ γ ∈ F u, g γ := add_le_add (le_refl _) ih

end Cover

section Polymers
variable {P V : Type*} [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]
  (inc : P → P → Prop) [DecidableRel inc] (supp near : P → Finset V)
  (hcov : ∀ γ γ', γ' ∈ nbhd inc γ → ∃ v ∈ near γ, v ∈ supp γ')

/-- Polymers through a site. -/
def fibre (v : V) : Finset P := univ.filter fun γ => v ∈ supp γ

omit [Fintype V] in
include hcov in
lemma nbhd_covered (γ : P) : nbhd inc γ ⊆ (near γ).biUnion (fibre supp) := by
  intro γ' hγ'
  obtain ⟨v, hv, hv'⟩ := hcov γ γ' hγ'
  exact mem_biUnion.mpr ⟨v, hv, by simp [fibre, hv']⟩

omit [Fintype V] in
include hcov in
/-- **Neighbour product from per-site sums.** -/
theorem nbhd_prod_ge (x : P → ℝ) (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ ≤ 1) (s : ℝ)
    (hs : ∀ v, ∑ γ ∈ fibre supp v, x γ ≤ s) (hs1 : s ≤ 1) (γ : P) :
    (1 - s) ^ (near γ).card ≤ ∏ γ' ∈ nbhd inc γ, (1 - x γ') := by
  have hcov' := nbhd_covered inc supp near hcov γ
  refine le_trans ?_ (prod_cover_ge (fun γ' => 1 - x γ') (fun γ' => by linarith [hx1 γ'])
    (fun γ' => by linarith [hx0 γ']) _ _ _ hcov')
  rw [← prod_const]
  apply prod_le_prod₀ (fun v _ => by linarith)
  intro v _
  calc 1 - s ≤ 1 - ∑ γ' ∈ fibre supp v, x γ' := by linarith [hs v]
    _ ≤ ∏ γ' ∈ fibre supp v, (1 - x γ') :=
      prod_one_sub_ge _ x (fun γ' _ => hx0 γ') (fun γ' _ => hx1 γ')

omit [Fintype V] in
include hcov in
/-- **Dobrushin's condition from activities and per-site sums.** -/
theorem dobrushin_of_activity (w : P → ℝ) (q c s : ℝ) (K : ℕ) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (hw : ∀ γ, |w γ| ≤ q ^ (supp γ).card)
    (hnear : ∀ γ, (near γ).card ≤ K * (supp γ).card)
    (hy1 : q * c ≤ 1)
    (hs : ∀ v, ∑ γ ∈ fibre supp v, (q * c) ^ (supp γ).card ≤ s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hK : 1 ≤ c * (1 - s) ^ K) (γ : P) :
    |w γ| ≤ (q * c) ^ (supp γ).card *
      ∏ γ' ∈ nbhd inc γ, (1 - (q * c) ^ (supp γ').card) := by
  set n := (supp γ).card
  have hy0 : 0 ≤ q * c := mul_nonneg hq hc
  have hprod := nbhd_prod_ge inc supp near hcov (fun γ' => (q * c) ^ (supp γ').card)
    (fun γ' => pow_nonneg hy0 _) (fun γ' => pow_le_one₀ hy0 hy1) s hs hs1 γ
  have h1s : 0 ≤ 1 - s := by linarith
  have hpow : (1 - s) ^ (K * n) ≤ (1 - s) ^ (near γ).card :=
    pow_le_pow_of_le_one h1s (by linarith) (hnear γ)
  have hcK : 1 ≤ (c * (1 - s) ^ K) ^ n := one_le_pow₀ hK
  calc |w γ| ≤ q ^ n := hw γ
    _ = q ^ n * 1 := (mul_one _).symm
    _ ≤ q ^ n * (c * (1 - s) ^ K) ^ n :=
        mul_le_mul_of_nonneg_left hcK (pow_nonneg hq _)
    _ = (q * c) ^ n * (1 - s) ^ (K * n) := by rw [mul_pow, mul_pow, ← pow_mul]; ring
    _ ≤ (q * c) ^ n * (1 - s) ^ (near γ).card :=
        mul_le_mul_of_nonneg_left hpow (pow_nonneg hy0 _)
    _ ≤ (q * c) ^ n * ∏ γ' ∈ nbhd inc γ, (1 - (q * c) ^ (supp γ').card) :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg hy0 _)

omit [Fintype V] in
include hcov in
/-- **The weighted decay hypothesis from per-site sums.** -/
theorem decay_of_sites (x : P → ℝ) (hx0 : ∀ γ, 0 ≤ x γ) (xbar : ℝ) (hxb : ∀ γ, x γ ≤ xbar)
    (hxb1 : xbar < 1) (K : ℕ) (hnear : ∀ γ, (near γ).card ≤ K * (supp γ).card) (s₁ : ℝ)
    (hs₁0 : 0 ≤ s₁) (hs₁ : ∀ v, ∑ γ ∈ fibre supp v, x γ * (supp γ).card ≤ s₁) (γ : P) :
    ∑ r ∈ nbhd inc γ, x r * ((supp r).card : ℝ) / (1 - x r) ≤
      (K * s₁ / (1 - xbar)) * (supp γ).card := by
  have h1 : 0 < 1 - xbar := by linarith
  have hnn : ∀ r, 0 ≤ x r * ((supp r).card : ℝ) := fun r => mul_nonneg (hx0 r) (Nat.cast_nonneg _)
  have hterm : ∀ r, x r * ((supp r).card : ℝ) / (1 - x r) ≤
      x r * ((supp r).card : ℝ) / (1 - xbar) := fun r =>
    div_le_div_of_nonneg_left (hnn r) h1 (by linarith [hxb r])
  calc ∑ r ∈ nbhd inc γ, x r * ((supp r).card : ℝ) / (1 - x r)
      ≤ ∑ r ∈ nbhd inc γ, x r * ((supp r).card : ℝ) / (1 - xbar) :=
        sum_le_sum fun r _ => hterm r
    _ = (∑ r ∈ nbhd inc γ, x r * ((supp r).card : ℝ)) / (1 - xbar) := by
        simp only [div_eq_mul_inv, ← sum_mul]
    _ ≤ (∑ v ∈ near γ, ∑ r ∈ fibre supp v, x r * ((supp r).card : ℝ)) / (1 - xbar) :=
        div_le_div_of_nonneg_right
          (sum_cover_le _ hnn _ _ _ (nbhd_covered inc supp near hcov γ)) h1.le
    _ ≤ (∑ _v ∈ near γ, s₁) / (1 - xbar) :=
        div_le_div_of_nonneg_right (sum_le_sum fun v _ => hs₁ v) h1.le
    _ = (near γ).card * s₁ / (1 - xbar) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((K * (supp γ).card : ℕ) : ℝ) * s₁ / (1 - xbar) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hnear γ) hs₁0) h1.le
    _ = (K * s₁ / (1 - xbar)) * (supp γ).card := by push_cast; ring

end Polymers


/-! ### Re-rooting animals -/

section Reroot
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Growing an animal along a walk that starts inside it. -/
lemma Animal.grow_walk {v : V} : ∀ {a b : V} (p : G.Walk a b) (S : Finset V),
    ContourCount.Animal G v S → a ∈ S → ContourCount.Animal G v (S ∪ p.support.toFinset) := by
  intro a b p
  induction p with
  | @nil w =>
    intro S hS ha
    have : S ∪ (SimpleGraph.Walk.nil : G.Walk w w).support.toFinset = S := by
      ext x; simp only [mem_union, SimpleGraph.Walk.support_nil, List.mem_toFinset,
        List.mem_singleton]; constructor
      · rintro (h | rfl) <;> assumption
      · exact Or.inl
    rw [this]; exact hS
  | @cons a c b hac q ih =>
    intro S hS ha
    by_cases hc : c ∈ S
    · have h := ih S hS hc
      have e : S ∪ (SimpleGraph.Walk.cons hac q).support.toFinset = S ∪ q.support.toFinset := by
        ext x; simp only [mem_union, SimpleGraph.Walk.support_cons, List.mem_toFinset,
          List.mem_cons]; constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl ha
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rw [e]; exact h
    · have hS' : ContourCount.Animal G v (insert c S) := ContourCount.Animal.grow hS ha hac hc
      have h := ih (insert c S) hS' (mem_insert_self c S)
      have e : S ∪ (SimpleGraph.Walk.cons hac q).support.toFinset =
          insert c S ∪ q.support.toFinset := by
        ext x; simp only [mem_union, mem_insert, SimpleGraph.Walk.support_cons, List.mem_toFinset,
          List.mem_cons]; constructor
        · rintro (h | rfl | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inr ha)
          · exact Or.inr h
        · rintro ((rfl | h) | h)
          · exact Or.inr (Or.inr (SimpleGraph.Walk.start_mem_support q))
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      rw [e]; exact h

/-- **Re-rooting.** An animal rooted at `u` is an animal rooted at any of its sites. -/
theorem Animal.reroot {u v : V} {S : Finset V} (h : ContourCount.Animal G u S) (hv : v ∈ S) :
    ContourCount.Animal G v S := by
  obtain ⟨p, hp, -⟩ := ContourCount.spanning_walk G h
  have hvp : v ∈ p.support := by rw [← List.mem_toFinset, hp]; exact hv
  let p' : G.Walk v v := (p.dropUntil v hvp).append (p.takeUntil v hvp)
  have hsupp : ∀ x, x ∈ p'.support ↔ x ∈ p.support := by
    intro x
    simp only [p', SimpleGraph.Walk.mem_support_append_iff]
    conv_rhs => rw [← p.take_spec hvp]
    rw [SimpleGraph.Walk.mem_support_append_iff]; tauto
  have h' := Animal.grow_walk p' {v} ContourCount.Animal.single (mem_singleton_self v)
  have e : ({v} : Finset V) ∪ p'.support.toFinset = S := by
    ext x
    simp only [mem_union, mem_singleton, List.mem_toFinset, hsupp]
    rw [← List.mem_toFinset, hp]
    constructor
    · rintro (rfl | h) <;> [exact hv; exact h]
    · exact Or.inr
  rwa [e] at h'

end Reroot

/-! ### Per-site sums for connected contours -/

section Contours
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {P : Type*} [Fintype P] [DecidableEq P] (supp : P → Finset V)

omit [DecidableRel G.Adj] [DecidableEq P] in
/-- **Per-site sums are bounded by the animal count.** If every contour is connected (an animal
grown from some site; `Animal.reroot` makes it rooted at every site) and contours are determined by their support, the sum over contours
through `v` of any nonnegative function of the size is at most the size-graded animal sum. -/
theorem site_sum_le (hconn : ∀ γ, ∃ u, ContourCount.Animal G u (supp γ))
    (hinj : Function.Injective supp) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (v : V) :
    ∑ γ ∈ fibre supp v, g (supp γ).card ≤
      ∑ k ∈ range (Fintype.card V), ((ContourCount.animals G v (k + 1)).card : ℝ) * g (k + 1) := by
  classical
  rw [← sum_image (f := fun S : Finset V => g S.card) (fun a _ b _ h => hinj h)]
  have hsub : (fibre supp v).image supp ⊆
      (range (Fintype.card V)).biUnion fun k => ContourCount.animals G v (k + 1) := by
    intro S hS
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hS
    have hv : v ∈ supp γ := by simpa [fibre] using hγ
    have hpos : 0 < (supp γ).card := card_pos.mpr ⟨v, hv⟩
    have hle : (supp γ).card ≤ Fintype.card V := card_le_univ _
    refine mem_biUnion.mpr ⟨(supp γ).card - 1, mem_range.mpr (by omega), ?_⟩
    simp only [ContourCount.animals, mem_filter, mem_univ, true_and]
    obtain ⟨u, hu⟩ := hconn γ
    exact ⟨Animal.reroot hu hv, by omega⟩
  refine (sum_cover_le (fun S : Finset V => g S.card) (fun S => hg _) _ _ _ hsub).trans ?_
  refine sum_le_sum fun k _ => ?_
  have hcard : ∀ S ∈ ContourCount.animals G v (k + 1), S.card = k + 1 := by
    intro S hS
    simp only [ContourCount.animals, mem_filter, mem_univ, true_and] at hS
    exact hS.2
  rw [sum_congr rfl fun S hS => by rw [hcard S hS], sum_const, nsmul_eq_mul]

lemma succ_le_two_pow (k : ℕ) : (k : ℝ) + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    push_cast
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]; linarith

lemma geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (M : ℕ) :
    ∑ k ∈ range M, r ^ k ≤ 1 / (1 - r) := by
  have hgeom : (∑ k ∈ range M, r ^ k) * (1 - r) = 1 - r ^ M := geom_sum_mul_neg r M
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos, hgeom]
  linarith [pow_nonneg hr0 M]

omit [DecidableEq P] in
/-- **Per-site KP sum.** Through any site, `Σ_{γ ∋ v} y^|γ| ≤ y / (1 − D²y)`. -/
theorem site_sum_pow_le (hconn : ∀ γ, ∃ u, ContourCount.Animal G u (supp γ))
    (hinj : Function.Injective supp) (D : ℕ) (hD : ∀ u, G.degree u ≤ D) {y : ℝ} (hy : 0 ≤ y)
    (hr : (D : ℝ) ^ 2 * y < 1) (v : V) :
    ∑ γ ∈ fibre supp v, y ^ (supp γ).card ≤ y / (1 - (D : ℝ) ^ 2 * y) := by
  refine (site_sum_le G supp hconn hinj (fun n => y ^ n) (fun n => pow_nonneg hy n) v).trans ?_
  exact ContourCount.polymer_sum_le G D hD v hy hr _

omit [DecidableEq P] in
/-- **Per-site size-weighted sum.** Through any site,
`Σ_{γ ∋ v} |γ| y^|γ| ≤ y / (1 − 2D²y)`. -/
theorem site_sum_weighted_le (hconn : ∀ γ, ∃ u, ContourCount.Animal G u (supp γ))
    (hinj : Function.Injective supp) (D : ℕ) (hD : ∀ u, G.degree u ≤ D) {y : ℝ} (hy : 0 ≤ y)
    (hr : 2 * (D : ℝ) ^ 2 * y < 1) (v : V) :
    ∑ γ ∈ fibre supp v, y ^ (supp γ).card * (supp γ).card ≤
      y / (1 - 2 * (D : ℝ) ^ 2 * y) := by
  refine (site_sum_le G supp hconn hinj (fun n => y ^ n * n)
    (fun n => mul_nonneg (pow_nonneg hy n) (Nat.cast_nonneg n)) v).trans ?_
  set r := 2 * (D : ℝ) ^ 2 * y
  have hr0 : 0 ≤ r := by positivity
  have hterm : ∀ k ∈ range (Fintype.card V),
      ((ContourCount.animals G v (k + 1)).card : ℝ) * (y ^ (k + 1) * ((k + 1 : ℕ) : ℝ)) ≤
        y * r ^ k := by
    intro k _
    have hc : ((ContourCount.animals G v (k + 1)).card : ℝ) ≤ (D : ℝ) ^ (2 * k) := by
      have := ContourCount.card_animals_le G D hD v (k + 1)
      simp only [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ 2 ^ k := by push_cast; exact succ_le_two_pow k
    calc ((ContourCount.animals G v (k + 1)).card : ℝ) * (y ^ (k + 1) * ((k + 1 : ℕ) : ℝ))
        ≤ (D : ℝ) ^ (2 * k) * (y ^ (k + 1) * 2 ^ k) := by
          apply mul_le_mul hc _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h2 (pow_nonneg hy _)
      _ = y * r ^ k := by simp only [r, mul_pow, ← pow_mul]; ring
  calc ∑ k ∈ range (Fintype.card V),
        ((ContourCount.animals G v (k + 1)).card : ℝ) * (y ^ (k + 1) * ((k + 1 : ℕ) : ℝ))
      ≤ ∑ k ∈ range (Fintype.card V), y * r ^ k := sum_le_sum hterm
    _ = y * ∑ k ∈ range (Fintype.card V), r ^ k := by rw [mul_sum]
    _ ≤ y * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (geom_le hr0 hr _) hy
    _ = y / (1 - r) := by ring

end Contours

end PMAction.PolymerBridge
