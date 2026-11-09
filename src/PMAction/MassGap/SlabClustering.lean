import PMAction.MassGap.SlabTime
import PMAction.MassGap.TwinGas
import PMAction.MassGap.PolymerInfluence
import PMAction.MassGap.PolymerBridge
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Euclidean clustering on the PM slab

This is the volume-uniform **exponential clustering** (the Euclidean form of the mass gap) for
PM's spacetime slab, at the level of the contour gas.

Setting: the slab `G □ path(L+1)` with its plaquettes, contours with edge-weight activity
`w γ = Π_{e∈γ} ω e` and `|ω| ≤ q`; two sign patterns `εA` (on edges of slice `0`) and `εB` (on
edges of slice `L`). A contour's sign under `εA` is `+` iff it contains an even number of
`εA`-edges. `Z_A` is the gas with the `εA` signs, `Z_B` with the `εB` signs, `Z_AB` with both, and
`Z₀` with none. These are the parity correlations of the history sum (`ParitySigns`,
`HistorySum`).

* `slab_clustering`: with `y = 2q`, any rate `μ ∈ (0,1]` with `z = y/μ` small enough and plaquette
  degree `≤ D`,
  `|Z_AB Z₀ − Z_A Z_B| ≤ C₁ e^{C₁} μᴸ · Z_A Z_B`, where `C₁ = 8 |εA| s_z/(1 − y)^3` depends on
  the slice-0 support of the observable, not on `L`. The rate `μ` does not depend on the volume.

The proof uses the twin gas (`TwinGas`), Dobrushin's condition (`PolymerBridge`), the influence
supersolution `f(a) = 2 x_a |a| μ^{L − M(a)}` (`PolymerInfluence`, `SlabTime`), and the
cross-ratio (`cross_ratio_of_close`).
-/

namespace PMAction.MassGap.SlabClustering
open Finset SimpleGraph ContourRepresentation ContourGas SlabGeometry SlabTime TwinGas
  PolymerConvergence PolymerDecay PolymerCorrelation PolymerInfluence PolymerBridge

noncomputable section
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (L : ℕ)
  (plaqG : Finset (Finset (Sym2 V)))

local notation "X" => V × Fin (L + 1)
local notation "Γ" => slab G L
local notation "PQ" => slabPlaq G L plaqG
local notation "Ctr" => Contour (slab G L) (slabPlaq G L plaqG)

/-- The closed neighbourhood of a contour in the plaquette graph. -/
def near (γ : Finset (Sym2 X)) : Finset (Sym2 X) :=
  γ ∪ γ.biUnion fun e => (plaqGraph PQ).neighborFinset e

lemma near_card (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D) (γ : Finset (Sym2 X)) :
    (near G L plaqG γ).card ≤ (D + 1) * γ.card := by
  unfold near
  calc (γ ∪ γ.biUnion fun e => (plaqGraph PQ).neighborFinset e).card
      ≤ γ.card + (γ.biUnion fun e => (plaqGraph PQ).neighborFinset e).card := card_union_le _ _
    _ ≤ γ.card + ∑ e ∈ γ, ((plaqGraph PQ).neighborFinset e).card :=
        Nat.add_le_add_left card_biUnion_le _
    _ ≤ γ.card + ∑ _e ∈ γ, D := by
        apply Nat.add_le_add_left; apply sum_le_sum; intro e _
        rw [card_neighborFinset_eq_degree]; exact hD e
    _ = (D + 1) * γ.card := by rw [sum_const, smul_eq_mul]; ring

lemma incompat_cov {a b : Ctr} (h : Incompat (slab G L) PQ a b) :
    ∃ e ∈ near G L plaqG a.1, e ∈ b.1 := by
  rcases h with hd | ⟨e, he, f, hf, hadj⟩
  · obtain ⟨e, hea, heb⟩ := Finset.not_disjoint_iff.mp hd
    exact ⟨e, mem_union_left _ hea, heb⟩
  · refine ⟨f, mem_union_right _ (mem_biUnion.mpr ⟨e, he, ?_⟩), hf⟩
    rw [mem_neighborFinset]; exact hadj

/-- Contours are rooted animals in the plaquette graph. -/
lemma ctr_conn (γ : Ctr) : ∃ u, ContourCount.Animal (plaqGraph PQ) u γ.1 := γ.2.2.2.1

lemma ctr_card_pos (γ : Ctr) : 1 ≤ γ.1.card := card_pos.mpr γ.2.1

/-- The latest tick of a contour. -/
def M (γ : Ctr) : ℕ := γ.1.sup (tau L)

lemma tau_le_M (γ : Ctr) {e : Sym2 X} (he : e ∈ γ.1) : tau L e ≤ M G L plaqG γ :=
  le_sup (f := tau L) he

lemma M_le_L (γ : Ctr) : M G L plaqG γ ≤ L := Finset.sup_le fun e _ => tau_le L e

/-- An incompatible contour reaches at most `|r|` ticks beyond the latest tick of `a`. -/
lemma M_incompat {a r : Ctr} (h : Incompat (slab G L) PQ a r) :
    M G L plaqG r ≤ M G L plaqG a + r.1.card := by
  obtain ⟨e, he, hall⟩ := tau_incompat G L plaqG (slab G L) h
  apply Finset.sup_le
  intro e' he'
  have := hall e' he'
  have := tau_le_M G L plaqG a he
  omega

/-- A contour with an edge at tick `0` ends by tick `|γ| − 1`. -/
lemma M_of_zero {γ : Ctr} {e : Sym2 X} (he : e ∈ γ.1) (h0 : tau L e = 0) :
    M G L plaqG γ + 1 ≤ γ.1.card := by
  apply Nat.succ_le_of_lt
  have hlt : ∀ e' ∈ γ.1, tau L e' < γ.1.card := by
    intro e' he'
    have := contour_span G L plaqG (slab G L) γ he he'
    omega
  have hne := γ.2.1
  rw [M, Finset.sup_lt_iff (by rw [Nat.bot_eq_zero]; exact ctr_card_pos G L plaqG γ)]
  exact hlt

/-- A contour with edges at ticks `0` and `L` has at least `L + 1` edges. -/
lemma card_of_span {γ : Ctr} {e e' : Sym2 X} (he : e ∈ γ.1) (he' : e' ∈ γ.1) (h0 : tau L e = 0)
    (hL : tau L e' = L) : L + 1 ≤ γ.1.card := by
  have := contour_span G L plaqG (slab G L) γ he he'
  omega

/-! ### The twin gas of slab contours -/

section Twin
variable (ω : Sym2 (V × Fin (L + 1)) → ℝ)

/-- Contour activity from an edge weight. -/
def wc (γ : Ctr) : ℝ := ∏ e ∈ γ.1, ω e

lemma wc_bound {q : ℝ} (hω : ∀ e, |ω e| ≤ q) (γ : Ctr) :
    |wc G L plaqG ω γ| ≤ q ^ γ.1.card := by
  unfold wc
  rw [abs_prod]
  calc ∏ e ∈ γ.1, |ω e| ≤ ∏ _e ∈ γ.1, q :=
        prod_le_prod₀ (fun e _ => abs_nonneg _) (fun e _ => hω e)
    _ = q ^ γ.1.card := prod_const q

/-- Twin support: the contour's edges. -/
def supp2 (a : Ctr × Bool) : Finset (Sym2 (V × Fin (L + 1))) := a.1.1

/-- Twin per-edge sums are twice the contour per-edge sums. -/
lemma twin_site_sum (g : ℕ → ℝ) (e : Sym2 (V × Fin (L + 1))) :
    ∑ a ∈ fibre (supp2 G L plaqG) e, g (supp2 G L plaqG a).card =
      2 * ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, g γ.1.card := by
  have hf : fibre (supp2 G L plaqG) e = fibre (fun γ : Ctr => γ.1) e ×ˢ (univ : Finset Bool) := by
    ext ⟨γ, b⟩
    rw [mem_product, fibre, fibre, mem_filter, mem_filter]
    simp [supp2]
  rw [hf, sum_product]
  simp only [supp2, sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [mul_sum]; push_cast; ring_nf

end Twin

/-! ### Dobrushin's condition for the twin gas -/

section Dob
variable (ω : Sym2 (V × Fin (L + 1)) → ℝ)

/-- Contour per-edge sums from `ContourCount`. -/
lemma ctr_site_pow (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D) {y : ℝ} (hy : 0 ≤ y)
    (hr : (D : ℝ) ^ 2 * y < 1) (e : Sym2 (V × Fin (L + 1))) :
    ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, y ^ γ.1.card ≤ y / (1 - (D : ℝ) ^ 2 * y) :=
  site_sum_pow_le (plaqGraph PQ) (fun γ : Ctr => γ.1) (ctr_conn G L plaqG) Subtype.val_injective
    D hD hy hr e

lemma ctr_site_weighted (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D) {z : ℝ} (hz : 0 ≤ z)
    (hr : 2 * (D : ℝ) ^ 2 * z < 1) (e : Sym2 (V × Fin (L + 1))) :
    ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, z ^ γ.1.card * γ.1.card ≤
      z / (1 - 2 * (D : ℝ) ^ 2 * z) :=
  site_sum_weighted_le (plaqGraph PQ) (fun γ : Ctr => γ.1) (ctr_conn G L plaqG)
    Subtype.val_injective D hD hz hr e

lemma inc2_symm : ∀ a b : Ctr × Bool, inc2 (Incompat (slab G L) PQ) a b →
    inc2 (Incompat (slab G L) PQ) b a :=
  fun a b h => incompat_symm (slab G L) PQ a.1 b.1 h

/-- **Dobrushin's condition for the twin gas.** -/
theorem twin_dobrushin (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D) (q : ℝ) (hq : 0 ≤ q)
    (hω : ∀ e, |ω e| ≤ q) (hy1 : 2 * q ≤ 1) (hDy : (D : ℝ) ^ 2 * (2 * q) < 1)
    (hs1 : 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q))) ≤ 1)
    (hK : 1 ≤ 2 * (1 - 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q)))) ^ (D + 1))
    (a : Ctr × Bool) :
    |w2 (wc G L plaqG ω) a| ≤ (2 * q) ^ (supp2 G L plaqG a).card *
      ∏ b ∈ nbhd (inc2 (Incompat (slab G L) PQ)) a,
        (1 - (2 * q) ^ (supp2 G L plaqG b).card) := by
  set y := 2 * q
  have hy0 : 0 ≤ y := by positivity
  have hden : 0 < 1 - (D : ℝ) ^ 2 * y := by linarith
  have hs0 : 0 ≤ 2 * (y / (1 - (D : ℝ) ^ 2 * y)) := by positivity
  have hcov : ∀ a a', a' ∈ nbhd (inc2 (Incompat (slab G L) PQ)) a →
      ∃ v ∈ near G L plaqG (supp2 G L plaqG a), v ∈ supp2 G L plaqG a' := by
    intro a a' h
    simp only [nbhd, mem_filter, mem_univ, true_and] at h
    exact incompat_cov G L plaqG h.2
  have hw : ∀ a : Ctr × Bool, |w2 (wc G L plaqG ω) a| ≤ q ^ (supp2 G L plaqG a).card := by
    intro a
    unfold w2 supp2
    split_ifs
    · exact wc_bound G L plaqG ω hω a.1
    · rw [abs_neg]; exact wc_bound G L plaqG ω hω a.1
  have hnear : ∀ a : Ctr × Bool,
      (near G L plaqG (supp2 G L plaqG a)).card ≤ (D + 1) * (supp2 G L plaqG a).card :=
    fun a => near_card G L plaqG D hD _
  have hsite : ∀ e, ∑ a ∈ fibre (supp2 G L plaqG) e, (q * 2) ^ (supp2 G L plaqG a).card ≤
      2 * (y / (1 - (D : ℝ) ^ 2 * y)) := by
    intro e
    rw [twin_site_sum G L plaqG (fun n => (q * 2) ^ n) e]
    have h := ctr_site_pow G L plaqG D hD hy0 hDy e
    have e2 : q * 2 = y := by ring
    rw [e2]
    linarith
  have h := dobrushin_of_activity (inc2 (Incompat (slab G L) PQ)) (supp2 G L plaqG)
    (fun a => near G L plaqG (supp2 G L plaqG a)) hcov (w2 (wc G L plaqG ω)) q 2 _ (D + 1) hq
    (by norm_num) hw hnear (by linarith) hsite hs0 hs1 hK a
  have e2 : q * 2 = y := by ring
  simpa only [e2] using h

end Dob

/-! ### Signs and the time-decaying supersolution -/

section Super

/-- A contour's sign under a sign pattern: `true` (`+`) iff it has an even number of marked
edges. -/
def sgnC (ε : Sym2 (V × Fin (L + 1)) → Bool) (γ : Ctr) : Bool :=
  decide (Even (γ.1.filter fun e => ε e = true).card)

/-- Contours whose sign flips. -/
def flipSet (ε : Sym2 (V × Fin (L + 1)) → Bool) : Finset Ctr :=
  univ.filter fun γ => sgnC G L plaqG ε γ = false

lemma flip_edge {ε : Sym2 (V × Fin (L + 1)) → Bool} {γ : Ctr} (h : γ ∈ flipSet G L plaqG ε) :
    ∃ e ∈ γ.1, ε e = true := by
  simp only [flipSet, sgnC, mem_filter, mem_univ, true_and, decide_eq_false_iff_not] at h
  by_contra hc
  push Not at hc
  apply h
  have : (γ.1.filter fun e => ε e = true) = ∅ := by
    rw [filter_eq_empty_iff]; intro e he; simp [hc e he]
  rw [this]; exact ⟨0, rfl⟩

/-- KP weights of twins. -/
def x2 (y : ℝ) (a : Ctr × Bool) : ℝ := y ^ (supp2 G L plaqG a).card

/-- The supersolution. -/
def fsup (y μ : ℝ) (a : Ctr × Bool) : ℝ :=
  2 * x2 G L plaqG y a * (supp2 G L plaqG a).card * μ ^ (L - M G L plaqG a.1)

lemma x2_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (a : Ctr × Bool) : x2 G L plaqG y a ≤ y := by
  unfold x2
  calc y ^ (supp2 G L plaqG a).card ≤ y ^ 1 :=
        pow_le_pow_of_le_one hy0 hy1 (ctr_card_pos G L plaqG a.1)
    _ = y := pow_one y

lemma pow_split {y μ : ℝ} (hμ : 0 < μ) (n : ℕ) : y ^ n = (y / μ) ^ n * μ ^ n := by
  rw [div_pow, div_mul_cancel₀ _ (pow_pos hμ n).ne']

/-- **The per-neighbour bound.** -/
lemma step_le (εB : Sym2 (V × Fin (L + 1)) → Bool) (hBL : ∀ e, εB e = true → tau L e = L)
    {y μ : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    {a r : Ctr × Bool} (hr : Incompat (slab G L) PQ a.1 r.1) :
    stepBound (x2 G L plaqG y) (twins (flipSet G L plaqG εB)) (fsup G L plaqG y μ) r ≤
      2 / (1 - y) ^ 2 * ((supp2 G L plaqG r).card * (y / μ) ^ (supp2 G L plaqG r).card) *
        μ ^ (L - M G L plaqG a.1) := by
  set n := (supp2 G L plaqG r).card with hn
  have hn1 : 1 ≤ n := ctr_card_pos G L plaqG r.1
  have hMr := M_incompat G L plaqG hr
  have hxr := x2_le G L plaqG hy0 hy1.le r
  have hxr0 : 0 ≤ x2 G L plaqG y r := pow_nonneg hy0 _
  have h1y : 0 < 1 - y := by linarith
  have h1x : 1 - y ≤ 1 - x2 G L plaqG y r := by linarith
  have hsq : (1 - y) ^ 2 ≤ (1 - x2 G L plaqG y r) ^ 2 := pow_le_pow_left₀ h1y.le h1x 2
  have hz0 : 0 ≤ y / μ := div_nonneg hy0 hμ0.le
  have hsplit : x2 G L plaqG y r = (y / μ) ^ n * μ ^ n := pow_split hμ0 n
  have hzn : 0 ≤ (y / μ) ^ n := pow_nonneg hz0 n
  unfold stepBound
  split_ifs with hE
  · -- `r` reaches slice `L`
    have hrF : r.1 ∈ flipSet G L plaqG εB := (mem_product.mp hE).1
    obtain ⟨e, he, heB⟩ := flip_edge G L plaqG hrF
    have hML : M G L plaqG r.1 = L := le_antisymm (M_le_L G L plaqG r.1)
      (by have h1 := tau_le_M G L plaqG r.1 he; rw [hBL e heB] at h1; exact h1)
    have hpow : μ ^ n ≤ μ ^ (L - M G L plaqG a.1) :=
      pow_le_pow_of_le_one hμ0.le hμ1 (by simp only [hn, supp2] at hMr ⊢; omega)
    have hnum : 2 * x2 G L plaqG y r ≤
        2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) := by
      rw [hsplit]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have : (y / μ) ^ n * μ ^ n ≤ n * (y / μ) ^ n * μ ^ (L - M G L plaqG a.1) := by
        calc (y / μ) ^ n * μ ^ n ≤ (y / μ) ^ n * μ ^ (L - M G L plaqG a.1) :=
              mul_le_mul_of_nonneg_left hpow hzn
          _ = 1 * (y / μ) ^ n * μ ^ (L - M G L plaqG a.1) := by ring
          _ ≤ n * (y / μ) ^ n * μ ^ (L - M G L plaqG a.1) := by
              apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn' hzn)
              positivity
      linarith
    calc 2 * x2 G L plaqG y r / (1 - x2 G L plaqG y r) ^ 2
        ≤ 2 * x2 G L plaqG y r / (1 - y) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ ≤ 2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) / (1 - y) ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 2 / (1 - y) ^ 2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) := by ring
  · unfold fsup
    have hpow : μ ^ n * μ ^ (L - M G L plaqG r.1) ≤ μ ^ (L - M G L plaqG a.1) := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hμ0.le hμ1 (by simp only [hn, supp2] at hMr ⊢; omega)
    have hnum : 2 * x2 G L plaqG y r * n * μ ^ (L - M G L plaqG r.1) ≤
        2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) := by
      rw [hsplit]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc 2 * ((y / μ) ^ n * μ ^ n) * n * μ ^ (L - M G L plaqG r.1)
          = 2 * (n * (y / μ) ^ n) * (μ ^ n * μ ^ (L - M G L plaqG r.1)) := by ring
        _ ≤ 2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    calc 2 * x2 G L plaqG y r * n * μ ^ (L - M G L plaqG r.1) / (1 - x2 G L plaqG y r) ^ 2
        ≤ 2 * x2 G L plaqG y r * n * μ ^ (L - M G L plaqG r.1) / (1 - y) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
      _ ≤ 2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) / (1 - y) ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 2 / (1 - y) ^ 2 * (n * (y / μ) ^ n) * μ ^ (L - M G L plaqG a.1) := by ring

lemma twin_cov : ∀ a a' : Ctr × Bool, a' ∈ nbhd (inc2 (Incompat (slab G L) PQ)) a →
    ∃ v ∈ near G L plaqG (supp2 G L plaqG a), v ∈ supp2 G L plaqG a' := by
  intro a a' h
  simp only [nbhd, mem_filter, mem_univ, true_and] at h
  exact incompat_cov G L plaqG h.2

/-- Size-weighted sums over the incompatible neighbours of a twin. -/
lemma nbhd_weighted (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D) {z : ℝ} (hz0 : 0 ≤ z)
    (hz : 2 * (D : ℝ) ^ 2 * z < 1) (a : Ctr × Bool) :
    ∑ r ∈ nbhd (inc2 (Incompat (slab G L) PQ)) a,
        ((supp2 G L plaqG r).card * z ^ (supp2 G L plaqG r).card) ≤
      (D + 1) * (supp2 G L plaqG a).card * (2 * (z / (1 - 2 * (D : ℝ) ^ 2 * z))) := by
  have hcov := nbhd_covered (inc2 (Incompat (slab G L) PQ)) (supp2 G L plaqG)
    (fun a => near G L plaqG (supp2 G L plaqG a)) (twin_cov G L plaqG) a
  refine (sum_cover_le (fun r => ((supp2 G L plaqG r).card * z ^ (supp2 G L plaqG r).card : ℝ))
    (fun r => by positivity) _ _ _ hcov).trans ?_
  have hsz0 : 0 ≤ z / (1 - 2 * (D : ℝ) ^ 2 * z) := div_nonneg hz0 (by linarith)
  calc ∑ e ∈ near G L plaqG (supp2 G L plaqG a), ∑ r ∈ fibre (supp2 G L plaqG) e,
        ((supp2 G L plaqG r).card * z ^ (supp2 G L plaqG r).card : ℝ)
      ≤ ∑ _e ∈ near G L plaqG (supp2 G L plaqG a), 2 * (z / (1 - 2 * (D : ℝ) ^ 2 * z)) := by
        apply sum_le_sum; intro e _
        rw [twin_site_sum G L plaqG (fun n => (n : ℝ) * z ^ n) e]
        have h := ctr_site_weighted G L plaqG D hD hz0 hz e
        have : ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, ((γ.1.card : ℝ) * z ^ γ.1.card) =
            ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, z ^ γ.1.card * γ.1.card :=
          sum_congr rfl fun γ _ => mul_comm _ _
        rw [this]; linarith
    _ = (near G L plaqG (supp2 G L plaqG a)).card * (2 * (z / (1 - 2 * (D : ℝ) ^ 2 * z))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (D + 1) * (supp2 G L plaqG a).card * (2 * (z / (1 - 2 * (D : ℝ) ^ 2 * z))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast near_card G L plaqG D hD _

/-- **The time-decaying supersolution.** -/
theorem twin_super (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D)
    (εB : Sym2 (V × Fin (L + 1)) → Bool) (hBL : ∀ e, εB e = true → tau L e = L)
    {y μ : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (hz : 2 * (D : ℝ) ^ 2 * (y / μ) < 1)
    (hcond : 2 * (D + 1) * ((y / μ) / (1 - 2 * (D : ℝ) ^ 2 * (y / μ))) ≤ (1 - y) ^ 2) :
    ∀ a, a ∉ twins (flipSet G L plaqG εB) →
      x2 G L plaqG y a * ∑ r ∈ nbhd (inc2 (Incompat (slab G L) PQ)) a,
        stepBound (x2 G L plaqG y) (twins (flipSet G L plaqG εB)) (fsup G L plaqG y μ) r ≤
      fsup G L plaqG y μ a := by
  intro a _
  set z := y / μ
  have hz0 : 0 ≤ z := div_nonneg hy0 hμ0.le
  have h1y : 0 < 1 - y := by linarith
  set N := nbhd (inc2 (Incompat (slab G L) PQ)) a
  set T := μ ^ (L - M G L plaqG a.1)
  have hT0 : 0 ≤ T := pow_nonneg hμ0.le _
  have hstep : ∀ r ∈ N, stepBound (x2 G L plaqG y) (twins (flipSet G L plaqG εB))
      (fsup G L plaqG y μ) r ≤
        2 / (1 - y) ^ 2 * ((supp2 G L plaqG r).card * z ^ (supp2 G L plaqG r).card) * T := by
    intro r hr
    simp only [N, nbhd, mem_filter, mem_univ, true_and] at hr
    exact step_le G L plaqG εB hBL hy0 hy1 hμ0 hμ1 hr.2
  have hsum := nbhd_weighted G L plaqG D hD hz0 hz a
  have hxa : 0 ≤ x2 G L plaqG y a := pow_nonneg hy0 _
  set na : ℝ := ((supp2 G L plaqG a).card : ℝ)
  have hna : 0 ≤ na := Nat.cast_nonneg _
  calc x2 G L plaqG y a * ∑ r ∈ N, stepBound (x2 G L plaqG y) (twins (flipSet G L plaqG εB))
        (fsup G L plaqG y μ) r
      ≤ x2 G L plaqG y a * ∑ r ∈ N,
          2 / (1 - y) ^ 2 * (((supp2 G L plaqG r).card : ℝ) * z ^ (supp2 G L plaqG r).card) * T :=
        mul_le_mul_of_nonneg_left (sum_le_sum hstep) hxa
    _ = x2 G L plaqG y a * (2 / (1 - y) ^ 2 * T) *
          ∑ r ∈ N, (((supp2 G L plaqG r).card : ℝ) * z ^ (supp2 G L plaqG r).card) := by
        simp only [mul_sum]; refine sum_congr rfl fun r _ => ?_; ring
    _ ≤ x2 G L plaqG y a * (2 / (1 - y) ^ 2 * T) *
          ((D + 1) * na * (2 * (z / (1 - 2 * (D : ℝ) ^ 2 * z)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * x2 G L plaqG y a * na * T *
          ((2 * (D + 1) * (z / (1 - 2 * (D : ℝ) ^ 2 * z))) / (1 - y) ^ 2) := by
        field_simp
    _ ≤ 2 * x2 G L plaqG y a * na * T * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one (by positivity)]; exact hcond
    _ = fsup G L plaqG y μ a := by simp only [fsup, mul_one, na, T]

end Super

/-! ### The clustering theorem -/

section Clustering

/-- An edge weight with signs on the marked edges. -/
def sw (ε : Sym2 (V × Fin (L + 1)) → Bool) (ω : Sym2 (V × Fin (L + 1)) → ℝ)
    (e : Sym2 (V × Fin (L + 1))) : ℝ :=
  (if ε e = true then -1 else 1) * ω e

lemma wc_sw (ε : Sym2 (V × Fin (L + 1)) → Bool) (ω : Sym2 (V × Fin (L + 1)) → ℝ) (γ : Ctr) :
    wc G L plaqG (sw L ε ω) γ =
      if sgnC G L plaqG ε γ then wc G L plaqG ω γ else -wc G L plaqG ω γ := by
  unfold wc sw sgnC
  rw [prod_mul_distrib, prod_ite, prod_const_one, mul_one, prod_const]
  split_ifs with h
  · rw [(decide_eq_true_iff.mp h).neg_one_pow, one_mul]
  · have hodd : Odd (γ.1.filter fun e => ε e = true).card := by
      rw [← Nat.not_even_iff_odd]; simpa using h
    rw [hodd.neg_one_pow, neg_one_mul]

lemma one_add_prod_le (D' : Finset (Ctr × Bool)) (t : Ctr × Bool → ℝ) (ht : ∀ a, 0 ≤ t a) :
    ∏ a ∈ D', (1 + t a) - 1 ≤ (∑ a ∈ D', t a) * Real.exp (∑ a ∈ D', t a) := by
  have hexp : ∏ a ∈ D', (1 + t a) ≤ Real.exp (∑ a ∈ D', t a) := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ (fun a _ => by linarith [ht a])
      (fun a _ => by linarith [Real.add_one_le_exp (t a)])
  have hmain : ∀ D'' : Finset (Ctr × Bool),
      ∏ a ∈ D'', (1 + t a) - 1 ≤ (∑ a ∈ D'', t a) * ∏ a ∈ D'', (1 + t a) := by
    intro D''
    induction D'' using Finset.induction_on with
    | empty => simp
    | @insert b D'' hb ih =>
      rw [prod_insert hb, sum_insert hb]
      have hP : 1 ≤ ∏ a ∈ D'', (1 + t a) := one_le_prod₀ fun a _ => by linarith [ht a]
      have hS : 0 ≤ ∑ a ∈ D'', t a := sum_nonneg fun a _ => ht a
      set Pp := ∏ a ∈ D'', (1 + t a)
      set Ss := ∑ a ∈ D'', t a
      have htb := ht b
      have h1 : t b * Pp ≤ t b * ((1 + t b) * Pp) := by
        apply mul_le_mul_of_nonneg_left _ htb; nlinarith
      have h2 : Ss * Pp ≤ Ss * ((1 + t b) * Pp) := by
        apply mul_le_mul_of_nonneg_left _ hS; nlinarith
      calc (1 + t b) * Pp - 1 = (Pp - 1) + t b * Pp := by ring
        _ ≤ Ss * Pp + t b * Pp := by linarith
        _ ≤ Ss * ((1 + t b) * Pp) + t b * ((1 + t b) * Pp) := by linarith
        _ = (t b + Ss) * ((1 + t b) * Pp) := by ring
  have hS : 0 ≤ ∑ a ∈ D', t a := sum_nonneg fun a _ => ht a
  exact (hmain D').trans (mul_le_mul_of_nonneg_left hexp hS)


set_option maxHeartbeats 1000000 in
/-- The toggle term of one contour touching slice `0`. -/
lemma toggle_term (εA εB : Sym2 (V × Fin (L + 1)) → Bool)
    (hA0 : ∀ e, εA e = true → tau L e = 0) (hBL : ∀ e, εB e = true → tau L e = L)
    {y μ : ℝ} (hy0 : 0 ≤ y) (hy1' : y < 1) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1)
    (a : Ctr × Bool) (ha : a ∈ twins (flipSet G L plaqG εA)) :
    (if a ∈ twins (flipSet G L plaqG εB) then
        1 / (1 - x2 G L plaqG y a) - (1 - x2 G L plaqG y a)
      else fsup G L plaqG y μ a / (1 - x2 G L plaqG y a) ^ 2) / (1 - x2 G L plaqG y a) ≤
      2 / (1 - y) ^ 3 * (((supp2 G L plaqG a).card : ℝ) * (y / μ) ^ (supp2 G L plaqG a).card) *
        μ ^ L := by
  set z := y / μ
  set x := x2 G L plaqG y
  have hz0 : 0 ≤ z := div_nonneg hy0 hμ0.le
  have h1y : 0 < 1 - y := by linarith
  have hx0 : ∀ a, 0 ≤ x a := fun a => pow_nonneg hy0 _
  have hxy : ∀ a, x a ≤ y := fun a => x2_le G L plaqG hy0 hy1'.le a
  have hx1 : ∀ a, x a < 1 := fun a => lt_of_le_of_lt (hxy a) hy1'
  have haF : a.1 ∈ flipSet G L plaqG εA := (mem_product.mp ha).1
  obtain ⟨e, he, heA⟩ := flip_edge G L plaqG haF
  have hM := M_of_zero G L plaqG he (hA0 e heA)
  set n := (supp2 G L plaqG a).card with hn
  have hxa : x a = z ^ n * μ ^ n := pow_split hμ0 n
  have h1x : 1 - y ≤ 1 - x a := by linarith [hxy a]
  have h1xp : 0 < 1 - x a := by linarith [hx1 a]
  have hzn : 0 ≤ z ^ n := pow_nonneg hz0 n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast ctr_card_pos G L plaqG a.1
  have hy3 : (1 - y) ^ 3 ≤ (1 - y) ^ 2 := by
    have : (1 - y) ^ 3 = (1 - y) ^ 2 * (1 - y) := by ring
    rw [this]; exact mul_le_of_le_one_right (by positivity) (by linarith)
  split_ifs with hE
  · have hbF : a.1 ∈ flipSet G L plaqG εB := (mem_product.mp hE).1
    obtain ⟨e', he', heB⟩ := flip_edge G L plaqG hbF
    have hspan := card_of_span G L plaqG he he' (hA0 e heA) (hBL e' heB)
    have hpow : μ ^ n ≤ μ ^ L :=
      pow_le_pow_of_le_one hμ0.le hμ1 (by simp only [hn, supp2]; omega)
    have hx2 : (1 / (1 - x a) - (1 - x a)) / (1 - x a) ≤ 2 * x a / (1 - x a) ^ 2 := by
      rw [div_le_div_iff₀ h1xp (by positivity)]
      have h0 : (1 / (1 - x a) - (1 - x a)) * (1 - x a) = 1 - (1 - x a) ^ 2 := by
        field_simp
      have e : (1 / (1 - x a) - (1 - x a)) * (1 - x a) ^ 2 =
          (1 - (1 - x a) ^ 2) * (1 - x a) := by rw [sq, ← mul_assoc, h0]; ring
      rw [e]
      nlinarith [mul_nonneg (mul_nonneg (hx0 a) (hx0 a)) h1xp.le]
    calc (1 / (1 - x a) - (1 - x a)) / (1 - x a) ≤ 2 * x a / (1 - x a) ^ 2 := hx2
      _ ≤ 2 * x a / (1 - y) ^ 2 :=
        div_le_div_of_nonneg_left (by linarith [hx0 a]) (by positivity)
          (pow_le_pow_left₀ h1y.le h1x 2)
      _ ≤ 2 * x a / (1 - y) ^ 3 :=
        div_le_div_of_nonneg_left (by linarith [hx0 a]) (by positivity) hy3
      _ ≤ 2 / (1 - y) ^ 3 * (n * z ^ n) * μ ^ L := by
        have hxle : x a ≤ n * z ^ n * μ ^ L := by
          rw [hxa]
          calc z ^ n * μ ^ n ≤ z ^ n * μ ^ L := mul_le_mul_of_nonneg_left hpow hzn
            _ = 1 * z ^ n * μ ^ L := by ring
            _ ≤ n * z ^ n * μ ^ L := by
              apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn1 hzn)
              positivity
        have e : 2 / (1 - y) ^ 3 * (n * z ^ n) * μ ^ L = 2 * (n * z ^ n * μ ^ L) / (1 - y) ^ 3 := by
          ring
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · simp only [fsup]
    have hpow : μ ^ n * μ ^ (L - M G L plaqG a.1) ≤ μ ^ L := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hμ0.le hμ1 (by simp only [hn, supp2] at hM ⊢; omega)
    have hfx : 2 * x2 G L plaqG y a * (supp2 G L plaqG a).card *
        μ ^ (L - M G L plaqG a.1) ≤ 2 * (n * z ^ n) * μ ^ L := by
      show 2 * x a * n * μ ^ (L - M G L plaqG a.1) ≤ _
      rw [hxa]
      calc 2 * (z ^ n * μ ^ n) * n * μ ^ (L - M G L plaqG a.1)
          = 2 * (n * z ^ n) * (μ ^ n * μ ^ (L - M G L plaqG a.1)) := by ring
        _ ≤ 2 * (n * z ^ n) * μ ^ L := mul_le_mul_of_nonneg_left hpow (by positivity)
    have h3 : (1 - y) ^ 3 ≤ (1 - x a) ^ 3 := pow_le_pow_left₀ h1y.le h1x 3
    calc 2 * x2 G L plaqG y a * (supp2 G L plaqG a).card * μ ^ (L - M G L plaqG a.1) /
          (1 - x a) ^ 2 / (1 - x a)
        = 2 * x2 G L plaqG y a * (supp2 G L plaqG a).card * μ ^ (L - M G L plaqG a.1) /
          (1 - x a) ^ 3 := by rw [div_div, ← pow_succ]
      _ ≤ 2 * (n * z ^ n) * μ ^ L / (1 - x a) ^ 3 :=
        div_le_div_of_nonneg_right hfx (by positivity)
      _ ≤ 2 * (n * z ^ n) * μ ^ L / (1 - y) ^ 3 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h3
      _ = 2 / (1 - y) ^ 3 * (n * z ^ n) * μ ^ L := by ring


/-- The size-weighted sum over the toggles near slice `0`. -/
lemma sumDA (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D)
    (εA : Sym2 (V × Fin (L + 1)) → Bool) {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 * (D : ℝ) ^ 2 * z < 1) :
    ∑ a ∈ twins (flipSet G L plaqG εA),
        (((supp2 G L plaqG a).card : ℝ) * z ^ (supp2 G L plaqG a).card) ≤
      ((univ : Finset (Sym2 (V × Fin (L + 1)))).filter fun e => εA e = true).card *
        (2 * (z / (1 - 2 * (D : ℝ) ^ 2 * z))) := by
  set sz := z / (1 - 2 * (D : ℝ) ^ 2 * z) with hszdef
  set EA := (univ : Finset (Sym2 (V × Fin (L + 1)))).filter fun e => εA e = true
  have hcovA : twins (flipSet G L plaqG εA) ⊆ EA.biUnion (fibre (supp2 G L plaqG)) := by
    intro a ha
    obtain ⟨e, he, heA⟩ := flip_edge G L plaqG (mem_product.mp ha).1
    refine mem_biUnion.mpr ⟨e, by simp [EA, heA], ?_⟩
    rw [fibre, mem_filter]; exact ⟨mem_univ _, he⟩
  refine (sum_cover_le (fun a => (((supp2 G L plaqG a).card : ℝ) * z ^ (supp2 G L plaqG a).card))
    (fun a => by positivity) _ _ _ hcovA).trans ?_
  calc ∑ e ∈ EA, ∑ a ∈ fibre (supp2 G L plaqG) e,
        (((supp2 G L plaqG a).card : ℝ) * z ^ (supp2 G L plaqG a).card)
      ≤ ∑ _e ∈ EA, 2 * sz := by
        apply sum_le_sum; intro e _
        rw [twin_site_sum G L plaqG (fun n => (n : ℝ) * z ^ n) e]
        have h := ctr_site_weighted G L plaqG D hD hz0 hz e
        rw [← hszdef] at h
        have : ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, ((γ.1.card : ℝ) * z ^ γ.1.card) =
            ∑ γ ∈ fibre (fun γ : Ctr => γ.1) e, z ^ γ.1.card * γ.1.card :=
          sum_congr rfl fun γ _ => mul_comm _ _
        rw [this]; linarith
    _ = EA.card * (2 * sz) := by rw [sum_const, nsmul_eq_mul]

set_option maxHeartbeats 1000000 in
/-- **Euclidean clustering on the PM slab.** -/
theorem slab_clustering (D : ℕ) (hD : ∀ e, (plaqGraph PQ).degree e ≤ D)
    (ω : Sym2 (V × Fin (L + 1)) → ℝ) (q μ : ℝ) (hq : 0 ≤ q) (hω : ∀ e, |ω e| ≤ q)
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (εA εB : Sym2 (V × Fin (L + 1)) → Bool)
    (hA0 : ∀ e, εA e = true → tau L e = 0) (hBL : ∀ e, εB e = true → tau L e = L)
    (hy1 : 2 * q ≤ 1 / 2) (hDy : (D : ℝ) ^ 2 * (2 * q) < 1)
    (hs1 : 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q))) ≤ 1)
    (hK : 1 ≤ 2 * (1 - 2 * ((2 * q) / (1 - (D : ℝ) ^ 2 * (2 * q)))) ^ (D + 1))
    (hz : 2 * (D : ℝ) ^ 2 * ((2 * q) / μ) < 1)
    (hcond : 2 * (D + 1) * (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) ≤
      (1 - 2 * q) ^ 2) :
    let ZAB := Z (Incompat (slab G L) PQ) (wc G L plaqG (sw L εA (sw L εB ω))) univ
    let ZA := Z (Incompat (slab G L) PQ) (wc G L plaqG (sw L εA ω)) univ
    let ZB := Z (Incompat (slab G L) PQ) (wc G L plaqG (sw L εB ω)) univ
    let Z0 := Z (Incompat (slab G L) PQ) (wc G L plaqG ω) univ
    let C₁ := 4 * ((univ.filter fun e => εA e = true).card : ℝ) *
      (((2 * q) / μ) / (1 - 2 * (D : ℝ) ^ 2 * ((2 * q) / μ))) / (1 - 2 * q) ^ 3
    |ZAB * Z0 - ZA * ZB| ≤ C₁ * Real.exp C₁ * μ ^ L * (ZA * ZB) := by
  intro ZAB ZA ZB Z0 C₁
  set y := 2 * q with hy
  set z := y / μ with hzdef
  have hy0 : 0 ≤ y := by positivity
  have hy1' : y < 1 := by linarith
  have h1y : 0 < 1 - y := by linarith
  have hz0 : 0 ≤ z := div_nonneg hy0 hμ0.le
  set sz := z / (1 - 2 * (D : ℝ) ^ 2 * z) with hszdef
  have hsz0 : 0 ≤ sz := div_nonneg hz0 (by linarith)
  -- the twin gas
  let inc' := inc2 (Incompat (slab G L) PQ)
  let w' := w2 (wc G L plaqG ω)
  let x := x2 G L plaqG y
  have hx0 : ∀ a, 0 ≤ x a := fun a => pow_nonneg hy0 _
  have hxy : ∀ a, x a ≤ y := fun a => x2_le G L plaqG hy0 hy1'.le a
  have hx1 : ∀ a, x a < 1 := fun a => lt_of_le_of_lt (hxy a) hy1'
  have hsymm := inc2_symm G L plaqG
  have hw : ∀ a, |w' a| ≤ x a * ∏ b ∈ nbhd inc' a, (1 - x b) :=
    twin_dobrushin G L plaqG ω D hD q hq hω (by linarith) hDy hs1 hK
  let E := twins (flipSet G L plaqG εB)
  let DA := twins (flipSet G L plaqG εA)
  let S0 : Finset (Ctr × Bool) := sel fun _ => true
  let f := fsup G L plaqG y μ
  have hf0 : ∀ a, 0 ≤ f a := fun a => by
    have := hx0 a; simp only [f, fsup]; positivity
  have hsuper := twin_super G L plaqG D hD εB hBL hy0 hy1' hμ0 hμ1 hz hcond
  let η : Ctr × Bool → ℝ := fun a =>
    if a ∈ E then 1 / (1 - x a) - (1 - x a) else f a / (1 - x a) ^ 2
  have hη : ∀ a, 0 ≤ η a := by
    intro a
    have h1 : 0 < 1 - x a := by linarith [hx1 a]
    simp only [η]
    split_ifs
    · rw [sub_nonneg, le_div_iff₀ h1]; nlinarith [hx0 a]
    · exact div_nonneg (hf0 a) (by positivity)
  have htog : ∀ a (U U' : Finset (Ctr × Bool)), (∀ δ, δ ∉ E → (δ ∈ U ↔ δ ∈ U')) →
      |tog inc' w' U a - tog inc' w' U' a| ≤ η a := fun a U U' hUU =>
    tog_close inc' w' x hsymm hx0 hx1 hw E f hf0 hsuper U U' hUU a
  have cr := cross_ratio_of_close inc' w' x hsymm hx0 hx1 hw S0 E η hη htog DA
  -- identify the four partition functions
  have hsel : ∀ s : Ctr → Bool,
      Z inc' w' (sel s) = Z (Incompat (slab G L) PQ)
        (fun γ => if s γ then wc G L plaqG ω γ else -wc G L plaqG ω γ) univ :=
    fun s => Z_sel (Incompat (slab G L) PQ) (wc G L plaqG ω) s
  have eA : Z inc' w' (symmDiff S0 DA) = ZA := by
    rw [show symmDiff S0 DA = sel (sgnC G L plaqG εA) from (sel_eq_symmDiff _).symm, hsel]
    simp only [ZA]; congr 1; funext γ; rw [wc_sw]
  have eB : Z inc' w' (symmDiff S0 E) = ZB := by
    rw [show symmDiff S0 E = sel (sgnC G L plaqG εB) from (sel_eq_symmDiff _).symm, hsel]
    simp only [ZB]; congr 1; funext γ; rw [wc_sw]
  have e0 : Z inc' w' S0 = Z0 := by
    rw [hsel]; simp only [Z0, ↓reduceIte]
  have eAB : Z inc' w' (symmDiff (symmDiff S0 E) DA) = ZAB := by
    have hset : symmDiff (symmDiff S0 E) DA =
        sel (fun γ => sgnC G L plaqG εA γ == sgnC G L plaqG εB γ) := by
      rw [sel_eq_symmDiff, symmDiff_assoc, twins_symmDiff]
      congr 2
      ext γ
      simp only [flipSet, Finset.mem_symmDiff, mem_filter, mem_univ, true_and]
      cases sgnC G L plaqG εA γ <;> cases sgnC G L plaqG εB γ <;> simp
    rw [hset, hsel]
    simp only [ZAB]; congr 1; funext γ
    rw [wc_sw, wc_sw]
    cases sgnC G L plaqG εA γ <;> cases sgnC G L plaqG εB γ <;> simp
  rw [eAB, e0, eA, eB] at cr
  -- the toggle sum
  have hZA : 0 < ZA := eA ▸ Z_pos inc' w' x hsymm hx0 hx1 hw _
  have hZB : 0 < ZB := eB ▸ Z_pos inc' w' x hsymm hx0 hx1 hw _
  let t : Ctr × Bool → ℝ := fun a => η a / (1 - x a)
  have ht0 : ∀ a, 0 ≤ t a := fun a => div_nonneg (hη a) (by linarith [hx1 a])
  have hbound : ∀ a ∈ DA, t a ≤ 2 / (1 - y) ^ 3 *
      (((supp2 G L plaqG a).card : ℝ) * z ^ (supp2 G L plaqG a).card) * μ ^ L :=
    fun a ha => toggle_term G L plaqG εA εB hA0 hBL hy0 hy1' hμ0 hμ1 a ha
  -- sum over the toggles near slice `0`
  set EA := (univ : Finset (Sym2 (V × Fin (L + 1)))).filter fun e => εA e = true
  have hsumDA := sumDA G L plaqG D hD εA hz0 hz
  rw [← hszdef] at hsumDA
  have hμL : μ ^ L ≤ 1 := pow_le_one₀ hμ0.le hμ1
  have hμL0 : 0 ≤ μ ^ L := pow_nonneg hμ0.le L
  have hC : C₁ = 4 * (EA.card : ℝ) * sz / (1 - y) ^ 3 := rfl
  have hC0 : 0 ≤ C₁ := by
    rw [hC]; exact div_nonneg (mul_nonneg (by positivity) hsz0) (by positivity)
  have hT : ∑ a ∈ DA, t a ≤ C₁ * μ ^ L := by
    calc ∑ a ∈ DA, t a ≤ ∑ a ∈ DA, 2 / (1 - y) ^ 3 *
          (((supp2 G L plaqG a).card : ℝ) * z ^ (supp2 G L plaqG a).card) * μ ^ L :=
          sum_le_sum hbound
      _ = 2 / (1 - y) ^ 3 * μ ^ L *
          ∑ a ∈ DA, (((supp2 G L plaqG a).card : ℝ) * z ^ (supp2 G L plaqG a).card) := by
          rw [mul_sum]; refine sum_congr rfl fun a _ => ?_; ring
      _ ≤ 2 / (1 - y) ^ 3 * μ ^ L * (EA.card * (2 * sz)) :=
          mul_le_mul_of_nonneg_left hsumDA (by positivity)
      _ = C₁ * μ ^ L := by rw [hC]; ring
  have hT0 : 0 ≤ ∑ a ∈ DA, t a := sum_nonneg fun a _ => ht0 a
  have hprod := one_add_prod_le G L plaqG DA t ht0
  have hexp : Real.exp (∑ a ∈ DA, t a) ≤ Real.exp C₁ :=
    Real.exp_le_exp.mpr (hT.trans (mul_le_of_le_one_right hC0 hμL))
  have hfin : ∏ a ∈ DA, (1 + t a) - 1 ≤ C₁ * Real.exp C₁ * μ ^ L := by
    calc ∏ a ∈ DA, (1 + t a) - 1 ≤ (∑ a ∈ DA, t a) * Real.exp (∑ a ∈ DA, t a) := hprod
      _ ≤ (C₁ * μ ^ L) * Real.exp C₁ :=
          mul_le_mul hT hexp (Real.exp_pos _).le (mul_nonneg hC0 hμL0)
      _ = C₁ * Real.exp C₁ * μ ^ L := mul_right_comm C₁ (μ ^ L) (Real.exp C₁)
  calc |ZAB * Z0 - ZA * ZB| ≤ (∏ a ∈ DA, (1 + η a / (1 - x a)) - 1) * (ZA * ZB) := cr
    _ ≤ C₁ * Real.exp C₁ * μ ^ L * (ZA * ZB) :=
        mul_le_mul_of_nonneg_right hfin (mul_pos hZA hZB).le

end Clustering

end

end PMAction.MassGap.SlabClustering
