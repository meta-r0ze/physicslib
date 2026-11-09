import PMAction.MassGap.PolymerDecay

/-!
# Decay of correlations in the polymer gas

`PolymerDecay.ratio_decay` says a single polymer's ratio barely depends on far-away polymers. This
file turns that into **decay of correlations**: two modifications of the allowed set, one near a
region `A` and one near a far region `B`, act almost independently on the partition function.

* `Far k γ E`: every polymer within `k` incompatibility steps of `γ` lies outside `E`.
* `agree_of_far`: two allowed sets that differ only on `E` agree to depth `k` around any `γ` far
  from `E`.
* `toggle_close`: toggling one polymer `a` (adding or removing it) multiplies `Z` by a factor that
  changes by at most `2 x_a b_a θ^k / (1 − x_a)^2` when the allowed set is changed on a set `E`
  far from `a`.
* `cross_ratio`: **decay of correlations.** Toggle a set `D` (near `A`) and a set `E` (near
  `B`). If every `a ∈ D` is at depth `k_a` from `E`, then
  `|Z(S∆E∆D) Z(S) − Z(S∆D) Z(S∆E)| ≤ (Π_{a∈D} (1 + δ_a) − 1) · Z(S∆D) Z(S∆E)`
  with `δ_a = 2 x_a b_a θ^{k_a} / (1 − x_a)^3`.

So the connected (truncated) part of any pair of modifications is bounded by a sum of terms
`θ^{distance}`. Signed activity changes (the parity observables of the transfer matrix) reduce to
allowed-set toggles by giving each polymer a sign twin, so this covers them too.
-/

namespace PMAction.MassGap.PolymerCorrelation
open Finset PolymerConvergence PolymerDecay

variable {P : Type*} [Fintype P] [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc]
  (w : P → ℝ)

/-- `γ` is at depth `k` from `E`: no polymer within `k` incompatibility steps lies in `E`. -/
def Far : ℕ → P → Finset P → Prop
  | 0, γ, E => γ ∉ E
  | k + 1, γ, E => γ ∉ E ∧ ∀ δ ∈ nbhd inc γ, Far k δ E

/-- Sets differing only on `E` agree to depth `k` around any `γ` at depth `k` from `E`. -/
theorem agree_of_far (E : Finset P) :
    ∀ (k : ℕ) (U U' : Finset P) (γ : P), (∀ δ, δ ∉ E → (δ ∈ U ↔ δ ∈ U')) →
      Far inc k γ E → AgreeNear inc k U U' γ := by
  intro k
  induction k with
  | zero => intro U U' γ h hf; exact h γ hf
  | succ k ih =>
    intro U U' γ h hf
    exact ⟨h γ hf.1, fun δ hδ => ih U U' δ h (hf.2 δ hδ)⟩

/-- The factor by which toggling `a` multiplies `Z`. -/
noncomputable def tog (U : Finset P) (a : P) : ℝ := Z inc w (symmDiff U {a}) / Z inc w U

section Pure
variable {P : Type*} [DecidableEq P]

lemma symmDiff_single_mem {U : Finset P} {a : P} (ha : a ∈ U) : symmDiff U {a} = U.erase a := by
  ext y; by_cases hy : y = a <;> simp [Finset.mem_symmDiff, hy, ha]

lemma symmDiff_single_not_mem {U : Finset P} {a : P} (ha : a ∉ U) :
    symmDiff U {a} = insert a U := by
  ext y; by_cases hy : y = a <;> simp [Finset.mem_symmDiff, hy, ha]

lemma symmDiff_insert {U D : Finset P} {a : P} (ha : a ∉ D) :
    symmDiff U (insert a D) = symmDiff (symmDiff U D) {a} := by
  ext y
  by_cases hy : y = a
  · subst hy; simp [Finset.mem_symmDiff, ha]
  · simp [Finset.mem_symmDiff, hy]

/-- Products of factors close to `1`. -/
lemma prod_close {u v δ P' : ℝ} (hu : |u - 1| ≤ P' - 1) (hv : |v - 1| ≤ δ) (_hδ : 0 ≤ δ)
    (hP : 1 ≤ P') : |u * v - 1| ≤ P' * (1 + δ) - 1 := by
  have hv1 : |v| ≤ 1 + δ := by
    calc |v| = |(v - 1) + 1| := by ring_nf
      _ ≤ |v - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ δ + 1 := by rw [abs_one]; linarith
      _ = 1 + δ := by ring
  calc |u * v - 1| = |(u - 1) * v + (v - 1)| := by ring_nf
    _ ≤ |(u - 1) * v| + |v - 1| := abs_add_le _ _
    _ = |u - 1| * |v| + |v - 1| := by rw [abs_mul]
    _ ≤ (P' - 1) * (1 + δ) + δ :=
        add_le_add (mul_le_mul hu hv1 (abs_nonneg _) (by linarith)) hv
    _ = P' * (1 + δ) - 1 := by ring

end Pure

section Bounds
variable (x : P → ℝ) (hsymm : ∀ a b, inc a b → inc b a) (hx0 : ∀ γ, 0 ≤ x γ) (hx1 : ∀ γ, x γ < 1)
  (hw : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b))
  (b : P → ℝ) (hb : ∀ γ, 1 ≤ b γ) (θ : ℝ) (hθ0 : 0 ≤ θ)
  (H : ∀ γ, ∑ r ∈ nbhd inc γ, x r * b r / (1 - x r) ≤ θ * b γ)

include hsymm hx0 hx1 hw

/-- The toggle factor in terms of ratios. -/
lemma tog_eq (U : Finset P) (a : P) :
    tog inc w U a = if a ∈ U then 1 / ratio inc w U a else ratio inc w (insert a U) a := by
  have hpos := Z_pos inc w x hsymm hx0 hx1 hw
  unfold tog ratio
  split_ifs with ha
  · rw [symmDiff_single_mem ha]
    have h1 := hpos U; have h2 := hpos (U.erase a)
    field_simp
  · rw [symmDiff_single_not_mem ha, erase_insert ha]

lemma tog_lower (U : Finset P) (a : P) : 1 - x a ≤ tog inc w U a := by
  rw [tog_eq inc w x hsymm hx0 hx1 hw]
  have h1 := hx1 a; have h0 := hx0 a
  split_ifs with ha
  · have hb := ratio_bounds inc w x hsymm hx0 hx1 hw U ha
    have hp : 0 < ratio inc w U a := by linarith [hb.1]
    rw [le_div_iff₀ hp]
    nlinarith [hb.2]
  · exact (ratio_bounds inc w x hsymm hx0 hx1 hw (insert a U) (mem_insert_self a U)).1

include hb hθ0 H in
/-- **One toggle, two far-apart environments.** -/
theorem toggle_close (E : Finset P) (U U' : Finset P) (hUU : ∀ δ, δ ∉ E → (δ ∈ U ↔ δ ∈ U'))
    (a : P) (k : ℕ) (hfar : Far inc k a E) :
    |tog inc w U a - tog inc w U' a| ≤ 2 * x a * b a * θ ^ k / (1 - x a) ^ 2 := by
  have h1x : 0 < 1 - x a := by linarith [hx1 a]
  have hε0 : 0 ≤ 2 * x a * b a * θ ^ k := by
    have := hx0 a; have := hb a; positivity
  have haE : a ∉ E := by cases k <;> [exact hfar; exact hfar.1]
  have hmem : a ∈ U ↔ a ∈ U' := hUU a haE
  rw [tog_eq inc w x hsymm hx0 hx1 hw, tog_eq inc w x hsymm hx0 hx1 hw]
  by_cases ha : a ∈ U
  · have ha' : a ∈ U' := hmem.mp ha
    simp only [ha, ha', ↓reduceIte]
    have hag := agree_of_far inc E k U U' a hUU hfar
    have hd := ratio_decay inc w x hsymm hx0 hx1 hw b hb θ hθ0 H k U U' a ha ha' hag
    have b1 := (ratio_bounds inc w x hsymm hx0 hx1 hw U ha).1
    have b2 := (ratio_bounds inc w x hsymm hx0 hx1 hw U' ha').1
    have p1 : 0 < ratio inc w U a := by linarith
    have p2 : 0 < ratio inc w U' a := by linarith
    rw [div_sub_div _ _ p1.ne' p2.ne', one_mul, mul_one, abs_div, abs_of_pos (mul_pos p1 p2),
      div_le_div_iff₀ (mul_pos p1 p2) (pow_pos h1x 2), abs_sub_comm]
    have hcc : (1 - x a) ^ 2 ≤ ratio inc w U a * ratio inc w U' a := by
      rw [sq]; exact mul_le_mul b1 b2 h1x.le p1.le
    calc |ratio inc w U a - ratio inc w U' a| * (1 - x a) ^ 2
        ≤ (2 * x a * b a * θ ^ k) * (1 - x a) ^ 2 :=
          mul_le_mul_of_nonneg_right hd (by positivity)
      _ ≤ (2 * x a * b a * θ ^ k) * (ratio inc w U a * ratio inc w U' a) :=
          mul_le_mul_of_nonneg_left hcc hε0
  · have ha' : a ∉ U' := fun h => ha (hmem.mpr h)
    simp only [ha, ha', ↓reduceIte]
    have hUU' : ∀ δ, δ ∉ E → (δ ∈ insert a U ↔ δ ∈ insert a U') := by
      intro δ hδ; simp only [mem_insert]; rw [hUU δ hδ]
    have hag := agree_of_far inc E k (insert a U) (insert a U') a hUU' hfar
    have hd := ratio_decay inc w x hsymm hx0 hx1 hw b hb θ hθ0 H k _ _ a
      (mem_insert_self a U) (mem_insert_self a U') hag
    refine hd.trans ?_
    have hp : (1 - x a) ^ 2 ≤ 1 := by
      have := hx0 a; nlinarith
    rw [le_div_iff₀ (pow_pos h1x 2)]
    exact mul_le_of_le_one_right hε0 hp

include hb hθ0 H in
/-- **Decay of correlations.** -/
theorem cross_ratio (S E : Finset P) (kk : P → ℕ) :
    ∀ D : Finset P, (∀ a ∈ D, Far inc (kk a) a E) →
      |Z inc w (symmDiff (symmDiff S E) D) * Z inc w S -
          Z inc w (symmDiff S D) * Z inc w (symmDiff S E)| ≤
        (∏ a ∈ D, (1 + 2 * x a * b a * θ ^ kk a / (1 - x a) ^ 3) - 1) *
          (Z inc w (symmDiff S D) * Z inc w (symmDiff S E)) := by
  have hpos := Z_pos inc w x hsymm hx0 hx1 hw
  -- work with `F / G − 1`
  suffices hrel : ∀ D : Finset P, (∀ a ∈ D, Far inc (kk a) a E) →
      |(Z inc w (symmDiff (symmDiff S E) D) / Z inc w (symmDiff S E)) /
          (Z inc w (symmDiff S D) / Z inc w S) - 1| ≤
        ∏ a ∈ D, (1 + 2 * x a * b a * θ ^ kk a / (1 - x a) ^ 3) - 1 by
    intro D hD
    have h := hrel D hD
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
    intro _
    have e1 : ∀ U : Finset P, symmDiff U (∅ : Finset P) = U := by
      intro U; ext y; simp [Finset.mem_symmDiff]
    have p1 := hpos S; have p2 := hpos (symmDiff S E)
    rw [e1, e1, div_self p2.ne', div_self p1.ne', prod_empty]; simp
  | @insert a D ha ih =>
    intro hD
    have ih' := ih fun c hc => hD c (mem_insert_of_mem hc)
    set U := symmDiff S D
    set U' := symmDiff (symmDiff S E) D
    have hUU : ∀ δ, δ ∉ E → (δ ∈ U' ↔ δ ∈ U) := by
      intro δ hδ; simp only [U, U', Finset.mem_symmDiff]; tauto
    have hclose := toggle_close inc w x hsymm hx0 hx1 hw b hb θ hθ0 H E U' U hUU a (kk a)
      (hD a (mem_insert_self a D))
    have hlow := tog_lower inc w x hsymm hx0 hx1 hw U a
    have h1x : 0 < 1 - x a := by linarith [hx1 a]
    have hgpos : 0 < tog inc w U a := lt_of_lt_of_le h1x hlow
    -- the new quotient is the old one times `tog U' a / tog U a`
    have hF : Z inc w (symmDiff (symmDiff S E) (insert a D)) / Z inc w (symmDiff S E) =
        (Z inc w U' / Z inc w (symmDiff S E)) * tog inc w U' a := by
      rw [symmDiff_insert ha]; unfold tog
      have := hpos U'; have := hpos (symmDiff S E); field_simp; rfl
    have hG : Z inc w (symmDiff S (insert a D)) / Z inc w S =
        (Z inc w U / Z inc w S) * tog inc w U a := by
      rw [symmDiff_insert ha]; unfold tog
      have := hpos U; have := hpos S; field_simp; rfl
    rw [hF, hG, prod_insert ha]
    set δ := 2 * x a * b a * θ ^ kk a / (1 - x a) ^ 3
    have hδ0 : 0 ≤ δ := by have := hx0 a; have := hb a; positivity
    have hv : |tog inc w U' a / tog inc w U a - 1| ≤ δ := by
      rw [div_sub_one hgpos.ne', abs_div, abs_of_pos hgpos, div_le_iff₀ hgpos]
      calc |tog inc w U' a - tog inc w U a| ≤ 2 * x a * b a * θ ^ kk a / (1 - x a) ^ 2 := hclose
        _ = δ * (1 - x a) := by simp only [δ]; field_simp
        _ ≤ δ * tog inc w U a := mul_le_mul_of_nonneg_left hlow hδ0
    have hP1 : 1 ≤ ∏ c ∈ D, (1 + 2 * x c * b c * θ ^ kk c / (1 - x c) ^ 3) := by
      apply one_le_prod₀
      intro c _
      have := hx0 c; have := hb c; have : 0 < 1 - x c := by linarith [hx1 c]
      have : 0 ≤ 2 * x c * b c * θ ^ kk c / (1 - x c) ^ 3 := by positivity
      linarith
    have hpU := hpos U; have hpS := hpos S; have hpU' := hpos U'; have hpSE := hpos (symmDiff S E)
    have hre : (Z inc w U' / Z inc w (symmDiff S E) * tog inc w U' a) /
        (Z inc w U / Z inc w S * tog inc w U a) =
        ((Z inc w U' / Z inc w (symmDiff S E)) / (Z inc w U / Z inc w S)) *
          (tog inc w U' a / tog inc w U a) := by
      field_simp
    rw [hre, mul_comm (1 + δ)]
    exact prod_close ih' hv hδ0 hP1

end Bounds

end PMAction.MassGap.PolymerCorrelation
