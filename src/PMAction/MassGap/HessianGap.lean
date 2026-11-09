import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Hessian gap: a vacuum-bounded region has a gauge-covariant spectral gap

`GaugeFluctuation.hess` is the Yang–Mills fluctuation operator `K = −D² + 2[F,·]`. Its kinetic
part `−D²` is the quadratic form `Σ_edges ‖a(head) − U·a(tail)‖²` with unitary parallel
transports `U`. This file proves a lower bound for that form that holds

* for **every** link configuration (any background, any compact gauge group), and
* **independently of the total volume**,

provided the fluctuation lives in a region whose sites reach the vacuum along short paths.
That proviso is where PM enters. A persisting defect's envelope has causal diameter at most `Δ`
(`PMSubstrate.Capacity.CausalDiameter`, `width_le`: a signal must cross and return within one
cycle), and outside it the state is the vacuum (`DefectGap.cost_le_of_defect_subset`: local
defects cost locally). So every site of a defect reaches the vacuum within `Δ` steps.

## Results

* `diamagnetic`: for a norm-preserving transport `U`, `|‖y‖ − ‖x‖| ≤ ‖y − U x‖`. The covariant
  difference dominates the difference of norms (lattice Kato inequality).
* `path_poincare`: canonical-path Poincaré inequality. If every site `x` has a path `P x` of at
  most `L` edges along which `f` telescopes to the vacuum, and no edge carries more than `K`
  paths, then `Σ f² ≤ L·K·Σ (df)²`.
* `covariant_gap`: combining the two, for any unitary links,
  `Σ_x ‖a x‖² ≤ L·K · Σ_e ‖a(head e) − U_e a(tail e)‖²`. The covariant kinetic form has gap
  `≥ 1/(L·K)`.
* `chain_poincare`, `covariant_chain_gap`: the concrete one-dimensional instance with the
  vacuum at one end: `Σ_{k<n} ‖A(k+1)‖² ≤ n² Σ_{k<n} ‖A(k+1) − U_k A k‖²`.
* `causal_hessian_gap`: at `n = Δ`, the covariant kinetic form on a causal line has gap
  `≥ 1/Δ²` (in lattice units), for any links.
* `hessian_gap_with_curvature`: adding the curvature term `2[F,·]` as a form perturbation
  bounded by `ε‖a‖²` leaves a gap `≥ m − ε`.
* `no_gap_without_vacuum`: without the vacuum boundary there is no gap. A nonzero constant field
  with trivial links on a graph with no vacuum edges has zero kinetic energy.

## What this does and does not show

The bound is a statement about fluctuations confined to a region with vacuum outside. In standard
quantum Yang–Mills there is no such region given in advance. On a periodic box the free Hessian's
lowest nonzero eigenvalue is `≈ (2π/L)²`, which goes to zero with the volume (massless gluons at
tree level; `no_gap_without_vacuum` is the extreme case). The vacuum boundary at the causal
diameter acts as an infrared cutoff. PM derives that cutoff from persistence (one-cycle refresh)
rather than putting it in by hand. That is the PM-specific input, and it is the step a
QFT reader will examine. It does not address the Clay problem.
-/

namespace PMAction.MassGap.HessianGap
open Finset

/-! ## Diamagnetic inequality -/

/-- **Lattice diamagnetic (Kato) inequality.** A norm-preserving transport cannot make the
covariant difference smaller than the difference of norms. -/
theorem diamagnetic {W : Type*} [SeminormedAddCommGroup W] (U : W → W)
    (hU : ∀ w, ‖U w‖ = ‖w‖) (x y : W) : |‖y‖ - ‖x‖| ≤ ‖y - U x‖ := by
  rw [← hU x]
  exact abs_norm_sub_norm_le y (U x)

/-- From `|s| ≤ c` to `s² ≤ c²`. -/
lemma sq_le_sq_of_abs_le {s c : ℝ} (h : |s| ≤ c) : s ^ 2 ≤ c ^ 2 := by
  have hc : 0 ≤ c := (abs_nonneg s).trans h
  have := mul_le_mul h h (abs_nonneg s) hc
  nlinarith [sq_abs s]

/-! ## Canonical-path Poincaré inequality -/

section Paths
variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- Exchanging the order of summation over sites and the edges of their paths. -/
lemma sum_paths_swap (P : X → Finset E) (g : E → ℝ) :
    ∑ x, ∑ e ∈ P x, g e = ∑ e, ((univ.filter fun x => e ∈ P x).card : ℝ) * g e := by
  calc ∑ x, ∑ e ∈ P x, g e = ∑ x, ∑ e, if e ∈ P x then g e else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ e, ∑ x, if e ∈ P x then g e else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **Canonical-path Poincaré inequality.** -/
theorem path_poincare (f : X → ℝ) (d : E → ℝ) (P : X → Finset E) (L K : ℕ)
    (htel : ∀ x, |f x| ≤ ∑ e ∈ P x, |d e|)
    (hL : ∀ x, (P x).card ≤ L)
    (hK : ∀ e, (univ.filter fun x => e ∈ P x).card ≤ K) :
    ∑ x, f x ^ 2 ≤ (L * K : ℝ) * ∑ e, d e ^ 2 := by
  have hx : ∀ x, f x ^ 2 ≤ (L : ℝ) * ∑ e ∈ P x, d e ^ 2 := by
    intro x
    have h1 := sq_le_sq_of_abs_le (htel x)
    have h2 := sq_sum_le_card_mul_sum_sq (s := P x) (f := fun e => |d e|)
    have h3 : ((P x).card : ℝ) ≤ L := by exact_mod_cast hL x
    have h4 : 0 ≤ ∑ e ∈ P x, d e ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
    simp only [sq_abs] at h2
    calc f x ^ 2 ≤ (∑ e ∈ P x, |d e|) ^ 2 := h1
      _ ≤ (P x).card * ∑ e ∈ P x, d e ^ 2 := h2
      _ ≤ L * ∑ e ∈ P x, d e ^ 2 := mul_le_mul_of_nonneg_right h3 h4
  calc ∑ x, f x ^ 2 ≤ ∑ x, (L : ℝ) * ∑ e ∈ P x, d e ^ 2 := Finset.sum_le_sum fun x _ => hx x
    _ = (L : ℝ) * ∑ e, ((univ.filter fun x => e ∈ P x).card : ℝ) * d e ^ 2 := by
        rw [← Finset.mul_sum, sum_paths_swap]
    _ ≤ (L : ℝ) * ∑ e, (K : ℝ) * d e ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg L)
        refine Finset.sum_le_sum fun e _ => ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK e) (sq_nonneg _)
    _ = (L * K : ℝ) * ∑ e, d e ^ 2 := by rw [← Finset.mul_sum]; ring

end Paths

/-! ## Gauge-covariant gap on a vacuum-bounded region -/

section Region
variable {X E W : Type*} [Fintype X] [Fintype E] [DecidableEq E] [SeminormedAddCommGroup W]

/-- A region: sites `X`, edges `E` with endpoints in `X` or in the vacuum (`none`). -/
structure Region (X E : Type*) where
  head : E → Option X
  tail : E → Option X

/-- A field on the region, extended by the vacuum value `0` outside it. -/
def ext {V : Type*} [Zero V] (a : X → V) (o : Option X) : V := o.elim 0 a

/-- Covariant difference along an edge with transport `U e`. -/
def covDiff (R : Region X E) (U : E → W → W) (a : X → W) (e : E) : W :=
  ext a (R.head e) - U e (ext a (R.tail e))

/-- Scalar difference along an edge. -/
def scalarDiff (R : Region X E) (g : X → ℝ) (e : E) : ℝ :=
  ext g (R.head e) - ext g (R.tail e)

/-- A canonical path system to the vacuum: every scalar field vanishing outside the region
telescopes along `P x` from `x` to the vacuum. -/
structure PathSystem (R : Region X E) (L K : ℕ) where
  P : X → Finset E
  tel : ∀ (g : X → ℝ) (x : X), |g x| ≤ ∑ e ∈ P x, |scalarDiff R g e|
  len : ∀ x, (P x).card ≤ L
  load : ∀ e, (univ.filter fun x => e ∈ P x).card ≤ K

omit [Fintype X] [Fintype E] [DecidableEq E] in
lemma norm_ext (a : X → W) (o : Option X) : ‖ext a o‖ = ext (fun x => ‖a x‖) o := by
  cases o <;> simp [ext]

omit [Fintype X] [Fintype E] [DecidableEq E] in
/-- The norm difference along an edge is dominated by the covariant difference. -/
lemma scalar_le_cov (R : Region X E) (U : E → W → W) (hU : ∀ e w, ‖U e w‖ = ‖w‖)
    (a : X → W) (e : E) :
    |scalarDiff R (fun x => ‖a x‖) e| ≤ ‖covDiff R U a e‖ := by
  unfold scalarDiff covDiff
  rw [← norm_ext, ← norm_ext]
  exact diamagnetic (U e) (hU e) _ _

/-- **The covariant Hessian gap.** For any norm-preserving links, the gauge-covariant kinetic
form on a region with a path system to the vacuum bounds the field norm:
`Σ ‖a‖² ≤ L·K · Σ ‖D a‖²`. The bound does not depend on the links or on anything outside the
region. -/
theorem covariant_gap (R : Region X E) {L K : ℕ} (S : PathSystem R L K) (U : E → W → W)
    (hU : ∀ e w, ‖U e w‖ = ‖w‖) (a : X → W) :
    ∑ x, ‖a x‖ ^ 2 ≤ (L * K : ℝ) * ∑ e, ‖covDiff R U a e‖ ^ 2 := by
  have h := path_poincare (fun x => ‖a x‖) (scalarDiff R fun x => ‖a x‖) S.P L K
    (S.tel _) S.len S.load
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => ?_) (by positivity))
  exact sq_le_sq_of_abs_le (scalar_le_cov R U hU a e)

omit [Fintype X] [DecidableEq E] in
/-- **No gap without a vacuum boundary.** If no edge reaches the vacuum and the links are
trivial, a nonzero constant field has zero covariant kinetic energy. -/
theorem no_gap_without_vacuum (R : Region X E) (hh : ∀ e, (R.head e).isSome)
    (ht : ∀ e, (R.tail e).isSome) (c : W) :
    ∑ e, ‖covDiff R (fun _ w => w) (fun _ => c) e‖ ^ 2 = 0 := by
  refine Finset.sum_eq_zero fun e _ => ?_
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hh e)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (ht e)
  simp [covDiff, ext, hx, hy]

end Region

/-! ## The causal line -/

/-- **One-dimensional Poincaré inequality with the vacuum at one end.** -/
theorem chain_poincare (n : ℕ) (G : ℕ → ℝ) (h0 : G 0 = 0) :
    ∑ k ∈ range n, G (k + 1) ^ 2 ≤ (n : ℝ) ^ 2 * ∑ k ∈ range n, (G (k + 1) - G k) ^ 2 := by
  have hD : 0 ≤ ∑ k ∈ range n, (G (k + 1) - G k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hk : ∀ k ∈ range n, G (k + 1) ^ 2 ≤ (n : ℝ) * ∑ j ∈ range n, (G (j + 1) - G j) ^ 2 := by
    intro k hk
    have hkn : k + 1 ≤ n := Finset.mem_range.mp hk
    have htel : G (k + 1) = ∑ j ∈ range (k + 1), (G (j + 1) - G j) := by
      rw [Finset.sum_range_sub, h0, sub_zero]
    have hcs := sq_sum_le_card_mul_sum_sq (s := range (k + 1)) (f := fun j => G (j + 1) - G j)
    rw [Finset.card_range] at hcs
    have hsub : ∑ j ∈ range (k + 1), (G (j + 1) - G j) ^ 2 ≤
        ∑ j ∈ range n, (G (j + 1) - G j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkn)
        (fun j _ _ => sq_nonneg _)
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
    rw [htel]
    calc (∑ j ∈ range (k + 1), (G (j + 1) - G j)) ^ 2
        ≤ ((k + 1 : ℕ) : ℝ) * ∑ j ∈ range (k + 1), (G (j + 1) - G j) ^ 2 := hcs
      _ ≤ (n : ℝ) * ∑ j ∈ range n, (G (j + 1) - G j) ^ 2 :=
        mul_le_mul hcast hsub (Finset.sum_nonneg fun j _ => sq_nonneg _) (Nat.cast_nonneg n)
  calc ∑ k ∈ range n, G (k + 1) ^ 2
      ≤ ∑ _k ∈ range n, (n : ℝ) * ∑ j ∈ range n, (G (j + 1) - G j) ^ 2 := Finset.sum_le_sum hk
    _ = (n : ℝ) ^ 2 * ∑ k ∈ range n, (G (k + 1) - G k) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Covariant gap on a line with the vacuum at one end**, for any norm-preserving links. -/
theorem covariant_chain_gap {W : Type*} [SeminormedAddCommGroup W] (n : ℕ) (A : ℕ → W)
    (h0 : A 0 = 0) (U : ℕ → W → W) (hU : ∀ k w, ‖U k w‖ = ‖w‖) :
    ∑ k ∈ range n, ‖A (k + 1)‖ ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ k ∈ range n, ‖A (k + 1) - U k (A k)‖ ^ 2 := by
  have h := chain_poincare n (fun k => ‖A k‖) (by simp [h0])
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (by positivity))
  exact sq_le_sq_of_abs_le (diamagnetic (U k) (hU k) (A k) (A (k + 1)))

/-- **The causal Hessian gap.** On a line of `Δ` sites ending in the vacuum (a defect's causal
diameter), the covariant kinetic form is at least `1/Δ²` times the field norm, for any links. -/
theorem causal_hessian_gap {W : Type*} [SeminormedAddCommGroup W] (Δ : ℕ) (hΔ : 0 < Δ)
    (A : ℕ → W) (h0 : A 0 = 0) (U : ℕ → W → W) (hU : ∀ k w, ‖U k w‖ = ‖w‖) :
    (1 / (Δ : ℝ) ^ 2) * ∑ k ∈ range Δ, ‖A (k + 1)‖ ^ 2 ≤
      ∑ k ∈ range Δ, ‖A (k + 1) - U k (A k)‖ ^ 2 := by
  have h := covariant_chain_gap Δ A h0 U hU
  have hpos : (0 : ℝ) < (Δ : ℝ) ^ 2 := by positivity
  rw [one_div, inv_mul_le_iff₀ hpos]
  exact h

/-! ## Adding the curvature term -/

/-- **Curvature as a bounded perturbation.** If the kinetic form `Q` has gap `m` and the
curvature form `C` (from `2[F,·]`) satisfies `|C a| ≤ ε‖a‖²`, then `Q + C` has gap `m − ε`. -/
theorem hessian_gap_with_curvature (m ε Q C N : ℝ) (hQ : m * N ≤ Q) (hC : |C| ≤ ε * N) :
    (m - ε) * N ≤ Q + C := by
  have := (abs_le.mp hC).1
  rw [sub_mul]
  linarith

end PMAction.MassGap.HessianGap
