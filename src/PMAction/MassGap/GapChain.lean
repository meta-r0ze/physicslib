import PMAction.MassGap.PolymerBridge
import PMAction.MassGap.GapFromDecay
import PMAction.MassGap.SpacetimeCost

/-!
# The gap chain, assembled

This file puts the contour route together into one explicit, volume-uniform statement and names
the single link still open.

## What is proved

`contour_decay` (fully proved). Take any gas of contours: polymers `γ` with a connected support
`supp γ` in a graph of degree `≤ D` (the contour adjacency graph), a neighbourhood
`|near γ| ≤ K |supp γ|` that every incompatible contour touches, activities `|w γ| ≤ q^|supp γ|`,
and `q` small:
`8 D² q ≤ 1`, `16 K q ≤ 3`, `4 q ≤ 1`.
Then for **every** finite volume and every pair of allowed sets agreeing to depth `k` around `γ`,
`|ρ_S(γ) − ρ_{S'}(γ)| ≤ 2 (2q)^|γ| · |γ| · θ^k` with `θ = 4 K q / (1 − 2 q) ≤ 8 K q`.

In PM the activity is not free. `SpacetimeCost.history_weight` shows every boundary edge, spatial
or temporal, carries the same factor `q = e^{−β}`. So the condition is `β ≥ log(8K) + …` and the
influence decays at rate `−log θ ≈ β − log(8K)` per incompatibility step.

`gap_of_euclidean_decay` (fully proved, from `GapFromDecay`). If the transfer matrix has Euclidean
decay at rate `λ` on its excited sector, every excited eigenvalue is at most `λ`.

## The open link

`EuclideanDecay T λ` is what connects the two. It requires the **contour representation** of
the PM spacetime model:
1. every closed set of spacetime boundary edges is the boundary of exactly one history with the
   vacuum boundary condition, so `Z` is the polymer partition function of connected closed
   contours with activity `q^|γ|` (a cohomology statement on the spacetime box);
2. the Euclidean correlation `⟨v, Tᵗ v⟩` of an excited vector is a difference of polymer ratios
   between allowed sets that agree up to the time separation `t`, so `contour_decay` bounds it by
   `C · θ^{t/r}` with `r` the contour range.

Both steps are geometry and combinatorics of the low-temperature expansion. They contain no
physics choice. They are stated here as the named hypothesis `EuclideanDecay`, the same way
`ResponseMatching.matching_frontier` names its open step.
-/

namespace PMAction.MassGap.GapChain
open Finset PolymerConvergence PolymerDecay PolymerBridge

section Contours
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {P : Type*} [Fintype P] [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc]
  (supp near : P → Finset V) (w : P → ℝ)

/-- **Volume-uniform decay of influence for a small-activity contour gas.** -/
theorem contour_decay
    (hsymm : ∀ a b, inc a b → inc b a)
    (hcov : ∀ γ γ', γ' ∈ nbhd inc γ → ∃ v ∈ near γ, v ∈ supp γ')
    (hconn : ∀ γ, ∃ u, ContourCount.Animal G u (supp γ))
    (hinj : Function.Injective supp)
    (D K : ℕ) (hD : ∀ u, G.degree u ≤ D) (hnear : ∀ γ, (near γ).card ≤ K * (supp γ).card)
    (q : ℝ) (hq : 0 ≤ q) (hw : ∀ γ, |w γ| ≤ q ^ (supp γ).card)
    (hqD : 8 * (D : ℝ) ^ 2 * q ≤ 1) (hqK : 16 * (K : ℝ) * q ≤ 3) (hq4 : 4 * q ≤ 1) :
    ∀ (k : ℕ) (S S' : Finset P) (γ : P), γ ∈ S → γ ∈ S' → AgreeNear inc k S S' γ →
      |ratio inc w S γ - ratio inc w S' γ| ≤
        2 * (2 * q) ^ (supp γ).card * (supp γ).card * (K * (4 * q) / (1 - 2 * q)) ^ k := by
  set y : ℝ := 2 * q with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 2 := by linarith
  have hDy : 4 * (D : ℝ) ^ 2 * y ≤ 1 := by rw [hy]; linarith
  have hD2 : 0 ≤ (D : ℝ) ^ 2 := by positivity
  -- supports are nonempty
  have hne : ∀ γ, 1 ≤ (supp γ).card := by
    intro γ
    obtain ⟨u, hu⟩ := hconn γ
    exact card_pos.mpr ⟨u, hu.root_mem⟩
  -- KP weights `x γ = y^|γ|`
  set x : P → ℝ := fun γ => y ^ (supp γ).card with hx
  have hx0 : ∀ γ, 0 ≤ x γ := fun γ => pow_nonneg hy0 _
  have hxy : ∀ γ, x γ ≤ y := fun γ => by
    simp only [hx]
    calc y ^ (supp γ).card ≤ y ^ 1 := pow_le_pow_of_le_one hy0 (by linarith) (hne γ)
      _ = y := pow_one y
  have hx1 : ∀ γ, x γ < 1 := fun γ => by linarith [hxy γ]
  -- per-site sums
  set s : ℝ := y / (1 - (D : ℝ) ^ 2 * y) with hs
  have hden1 : (3 : ℝ) / 4 ≤ 1 - (D : ℝ) ^ 2 * y := by nlinarith
  have hs0 : 0 ≤ s := div_nonneg hy0 (by linarith)
  have hsle : s ≤ 4 / 3 * y := by
    rw [hs, div_le_iff₀ (by linarith)]; nlinarith
  have hsite : ∀ v, ∑ γ ∈ fibre supp v, (q * 2) ^ (supp γ).card ≤ s := by
    intro v
    have h := site_sum_pow_le G supp hconn hinj D hD hy0 (by nlinarith) v
    rw [hs]
    simpa [hy, mul_comm] using h
  have hs1 : s ≤ 1 := by linarith
  -- `2 (1 − s)^K ≥ 1` by Bernoulli
  have hKs : (K : ℝ) * s ≤ 1 / 2 := by
    have : (K : ℝ) * s ≤ K * (4 / 3 * y) := mul_le_mul_of_nonneg_left hsle (Nat.cast_nonneg K)
    rw [hy] at this; nlinarith
  have hbern : 1 - (K : ℝ) * s ≤ (1 - s) ^ K := by
    have h := one_add_mul_le_pow (a := -s) (by linarith) K
    simpa [sub_eq_add_neg, mul_neg] using h
  have hcK : 1 ≤ 2 * (1 - s) ^ K := by linarith
  -- Dobrushin's condition
  have hdob : ∀ γ, |w γ| ≤ x γ * ∏ b ∈ nbhd inc γ, (1 - x b) := by
    intro γ
    have h := dobrushin_of_activity inc supp near hcov w q 2 s K hq (by norm_num) hw hnear
      (by linarith) hsite hs0 hs1 hcK γ
    simpa [hx, hy, mul_comm] using h
  -- the weighted decay hypothesis
  set s₁ : ℝ := y / (1 - 2 * (D : ℝ) ^ 2 * y) with hs₁
  have hden2 : (1 : ℝ) / 2 ≤ 1 - 2 * (D : ℝ) ^ 2 * y := by nlinarith
  have hs₁le : s₁ ≤ 2 * y := by
    rw [hs₁, div_le_iff₀ (by linarith)]; nlinarith
  have hs₁0 : 0 ≤ s₁ := div_nonneg hy0 (by linarith)
  have hsite₁ : ∀ v, ∑ γ ∈ fibre supp v, x γ * (supp γ).card ≤ 2 * y := by
    intro v
    have h := site_sum_weighted_le G supp hconn hinj D hD hy0 (by nlinarith) v
    exact (by simpa [hx] using h : _ ≤ s₁).trans hs₁le
  have hH : ∀ γ, ∑ r ∈ nbhd inc γ, x r * ((supp r).card : ℝ) / (1 - x r) ≤
      (K * (2 * y) / (1 - y)) * (supp γ).card :=
    decay_of_sites inc supp near hcov x hx0 y hxy (by linarith) K hnear (2 * y) (by positivity)
      hsite₁
  have hθ0 : 0 ≤ K * (2 * y) / (1 - y) := div_nonneg (by positivity) (by linarith)
  intro k S S' γ hS hS' hag
  have h := ratio_decay inc w x hsymm hx0 hx1 hdob (fun γ => ((supp γ).card : ℝ))
    (fun γ => by exact_mod_cast hne γ) _ hθ0 hH k S S' γ hS hS' hag
  have e : K * (2 * y) / (1 - y) = K * (4 * q) / (1 - 2 * q) := by rw [hy]; ring
  rw [e] at h
  simpa [hx, hy] using h

/-- The rate is at most `8 K q` once `4 q ≤ 1`. -/
theorem rate_le (K : ℕ) {q : ℝ} (hq : 0 ≤ q) (hq4 : 4 * q ≤ 1) :
    (K : ℝ) * (4 * q) / (1 - 2 * q) ≤ 8 * K * q := by
  have h : (0 : ℝ) < 1 - 2 * q := by linarith
  rw [div_le_iff₀ h]
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith [mul_nonneg hK hq]

end Contours

/-! ### The open link and the conditional gap -/

open Matrix

/-- **Euclidean decay at rate `λ` on the excited sector** of a transfer matrix. For the PM
spacetime model this is what the contour representation must deliver from `contour_decay`. -/
def EuclideanDecay {n : Type*} [Fintype n] (T : Matrix n n ℝ) (excited : (n → ℝ) → Prop)
    (lam : ℝ) : Prop :=
  ∀ v, excited v → ∃ C, ∀ t : ℕ, v ⬝ᵥ (T.mulVec)^[t] v ≤ C * lam ^ t

/-- **Conditional gap.** Given Euclidean decay at rate `λ`, every excited eigenvalue is at most
`λ` in absolute value. -/
theorem gap_of_euclidean_decay {n : Type*} [Fintype n] (T : Matrix n n ℝ)
    (excited : (n → ℝ) → Prop) (lam : ℝ) (hlam : 0 < lam) (h : EuclideanDecay T excited lam)
    (v : n → ℝ) (hv0 : v ≠ 0) (hex : excited v) (μ : ℝ) (hv : T *ᵥ v = μ • v) : |μ| ≤ lam :=
  GapFromDecay.gap_of_decay T excited lam hlam h v hv0 hex μ hv

end PMAction.MassGap.GapChain
