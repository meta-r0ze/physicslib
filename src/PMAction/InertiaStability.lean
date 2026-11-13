import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The number of negative modes is locally constant on invertible Hermitian operators

This is the analytic step that lets the substrate's own transfer count (`WallTransfer`) serve as
the integer charge of `PMConstants.WindingWeights` without importing Lüscher's construction.

For a Hermitian matrix `A`, `negCount` is the number of its negative eigenvalues (filled modes
below the gap). Sylvester's law of inertia, in the form needed here:

* `form`, `apply_span`: on the span of eigenvectors the quadratic form is `Σ λᵢ |cᵢ|²`.
* `err_bound`: a perturbation `E` changes the form by at most `(Σᵢⱼ ‖Eᵢⱼ‖) ‖x‖²`.
* `count_le`: if `A` is `δ`-negative on `S` eigenvectors and `B` is nonnegative on `T`
  eigenvectors, and `B − A` is smaller than `δ`, the two families are independent, so
  `|S| + |T| ≤ n`.
* `negCount_stable`: hence an invertible `A` has a neighbourhood of Hermitian `B` with the same
  number of negative eigenvalues.
* `negCount_locallyConstant`: along any continuous family of invertible Hermitian matrices, the
  negative-mode count is locally constant.

So the count changes only where the operator stops being invertible (a mode crosses zero): the
substrate's exceptional set, of measure zero.
-/

noncomputable section
namespace PMAction.InertiaStability
open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An eigenvector of a Hermitian matrix, as a plain vector. -/
def vec {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) : n → ℂ := ⇑(hA.eigenvectorBasis i)

lemma ortho {A : Matrix n n ℂ} (hA : A.IsHermitian) (i j : n) :
    star (vec hA i) ⬝ᵥ vec hA j = if i = j then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self hA.eigenvectorUnitary) i) j
  simp only [Matrix.mul_apply, Matrix.star_apply, IsHermitian.eigenvectorUnitary_apply,
    Matrix.one_apply] at h
  simpa [dotProduct, vec] using h

lemma eig {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    A *ᵥ vec hA i = (hA.eigenvalues i : ℂ) • vec hA i := by
  rw [vec, hA.mulVec_eigenvectorBasis]
  ext k
  simp [Complex.real_smul]

/-- **The form on a span of eigenvectors.** -/
lemma form {A : Matrix n n ℂ} (hA : A.IsHermitian) (s : Finset n) (c d : n → ℂ) :
    star (∑ i ∈ s, c i • vec hA i) ⬝ᵥ (∑ j ∈ s, d j • vec hA j) = ∑ i ∈ s, star (c i) * d i := by
  rw [star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dotProduct_sum]
  simp only [star_smul, smul_dotProduct, dotProduct_smul, ortho, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, hi, ite_true]
  ring

lemma apply_span {A : Matrix n n ℂ} (hA : A.IsHermitian) (s : Finset n) (c : n → ℂ) :
    A *ᵥ (∑ i ∈ s, c i • vec hA i) = ∑ i ∈ s, (c i * hA.eigenvalues i) • vec hA i := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, eig, smul_smul]

lemma term_re (z : ℂ) (r : ℝ) : (star z * (z * r)).re = r * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

omit [DecidableEq n] in
lemma self_re (x : n → ℂ) : (star x ⬝ᵥ x).re = ∑ k, ‖x k‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := term_re (x k) 1
  simpa using this

omit [DecidableEq n] in
/-- **A perturbation moves the form by at most its entry sum.** -/
lemma err_bound (E : Matrix n n ℂ) (x : n → ℂ) :
    ‖star x ⬝ᵥ (E *ᵥ x)‖ ≤ (∑ i, ∑ j, ‖E i j‖) * ∑ k, ‖x k‖ ^ 2 := by
  have hN : ∀ i, ‖x i‖ ^ 2 ≤ ∑ k, ‖x k‖ ^ 2 := fun i =>
    Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  have hxx : ∀ i j, ‖x i‖ * ‖x j‖ ≤ ∑ k, ‖x k‖ ^ 2 := fun i j => by
    nlinarith [hN i, hN j, sq_nonneg (‖x i‖ - ‖x j‖), norm_nonneg (x i), norm_nonneg (x j)]
  calc ‖star x ⬝ᵥ (E *ᵥ x)‖ = ‖∑ i, star (x i) * ∑ j, E i j * x j‖ := by
        simp only [dotProduct, mulVec, Pi.star_apply]
    _ ≤ ∑ i, ‖star (x i) * ∑ j, E i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖E i j‖ * (‖x i‖ * ‖x j‖) := by
        gcongr with i
        calc ‖star (x i) * ∑ j, E i j * x j‖ = ‖x i‖ * ‖∑ j, E i j * x j‖ := by
              rw [norm_mul, norm_star]
          _ ≤ ‖x i‖ * ∑ j, ‖E i j * x j‖ := by gcongr; exact norm_sum_le _ _
          _ = ∑ j, ‖E i j‖ * (‖x i‖ * ‖x j‖) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [norm_mul]; ring
    _ ≤ ∑ i, ∑ j, ‖E i j‖ * ∑ k, ‖x k‖ ^ 2 := by
        gcongr with i _ j _
        exact hxx i j
    _ = (∑ i, ∑ j, ‖E i j‖) * ∑ k, ‖x k‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

omit [Fintype n] in
lemma sum_subtype (S : Finset n) (g : S → ℂ) (f : n → n → ℂ) :
    ∑ i : S, g i • f i = ∑ i ∈ S, (if h : i ∈ S then g ⟨i, h⟩ else 0) • f i := by
  rw [← Finset.sum_coe_sort S]
  refine Fintype.sum_congr _ _ fun i => ?_
  simp [i.2]

/-- **Negative and nonnegative eigen-families are independent when the operators are close.** -/
theorem count_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (σ δ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (_hδ : 0 < δ) (S T : Finset n)
    (hS : ∀ i ∈ S, σ * hA.eigenvalues i ≤ -δ) (hT : ∀ j ∈ T, 0 ≤ σ * hB.eigenvalues j)
    (hE : (∑ i, ∑ j, ‖(B - A) i j‖) < δ) : S.card + T.card ≤ Fintype.card n := by
  let M : Matrix n (S ⊕ T) ℂ := fun k => Sum.elim (fun i : S => vec hA i k) (fun j : T => vec hB j k)
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    let c : n → ℂ := fun i => if h : i ∈ S then g (Sum.inl ⟨i, h⟩) else 0
    let d : n → ℂ := fun j => if h : j ∈ T then g (Sum.inr ⟨j, h⟩) else 0
    set x := ∑ i ∈ S, c i • vec hA i with hx
    set y := ∑ j ∈ T, d j • vec hB j with hy
    have hsum : M *ᵥ g = x + y := by
      have e1 : M *ᵥ g = (∑ i : S, g (Sum.inl i) • vec hA i) + ∑ j : T, g (Sum.inr j) • vec hB j := by
        funext k
        simp only [mulVec, dotProduct, Fintype.sum_sum_type, Pi.add_apply, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, M, Sum.elim_inl, Sum.elim_inr]
        congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> ring
      rw [e1, sum_subtype S (fun i => g (Sum.inl i)) (vec hA),
        sum_subtype T (fun j => g (Sum.inr j)) (vec hB)]
    have hxy : y = -x := by
      have : x + y = 0 := by rw [← hsum]; exact hg
      exact eq_neg_of_add_eq_zero_right this
    -- the norms
    have hNx : (star x ⬝ᵥ x).re = ∑ i ∈ S, ‖c i‖ ^ 2 := by
      rw [hx, form, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := term_re (c i) 1; simpa using this
    have hNy : (star y ⬝ᵥ y).re = ∑ j ∈ T, ‖d j‖ ^ 2 := by
      rw [hy, form, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := term_re (d j) 1; simpa using this
    -- the form of A on x
    have hqA : σ * (star x ⬝ᵥ (A *ᵥ x)).re ≤ -δ * (star x ⬝ᵥ x).re := by
      rw [hNx, hx, apply_span, form, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [term_re]
      have := hS i hi
      nlinarith [sq_nonneg ‖c i‖]
    -- the form of B on y, hence on x
    have hqB : 0 ≤ σ * (star x ⬝ᵥ (B *ᵥ x)).re := by
      have e : star x ⬝ᵥ (B *ᵥ x) = star y ⬝ᵥ (B *ᵥ y) := by
        rw [hxy]; simp [Matrix.mulVec_neg]
      rw [e, hy, apply_span, form, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_nonneg fun j hj => ?_
      rw [term_re]
      have := hT j hj
      nlinarith [sq_nonneg ‖d j‖]
    -- the perturbation
    have hsplit : star x ⬝ᵥ (B *ᵥ x) = star x ⬝ᵥ (A *ᵥ x) + star x ⬝ᵥ ((B - A) *ᵥ x) := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel]
    have herr : σ * (star x ⬝ᵥ ((B - A) *ᵥ x)).re ≤
        (∑ i, ∑ j, ‖(B - A) i j‖) * (star x ⬝ᵥ x).re := by
      rw [self_re]
      have h1 := err_bound (B - A) x
      have h2 : |(star x ⬝ᵥ ((B - A) *ᵥ x)).re| ≤ ‖star x ⬝ᵥ ((B - A) *ᵥ x)‖ :=
        Complex.abs_re_le_norm _
      rcases hσ with rfl | rfl
      · have := le_abs_self (star x ⬝ᵥ ((B - A) *ᵥ x)).re; nlinarith
      · have := neg_abs_le (star x ⬝ᵥ ((B - A) *ᵥ x)).re; nlinarith
    have hN0 : 0 ≤ (star x ⬝ᵥ x).re := by rw [self_re]; positivity
    have hx0 : (star x ⬝ᵥ x).re = 0 := by
      rw [hsplit, Complex.add_re, mul_add] at hqB
      nlinarith
    have hc0 : ∀ i ∈ S, c i = 0 := by
      intro i hi
      have hsum0 : ∑ i ∈ S, ‖c i‖ ^ 2 = 0 := by rw [← hNx, hx0]
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hsum0 i hi
      simpa using this
    have hyx : (star y ⬝ᵥ y).re = 0 := by
      rw [hxy]; simp only [star_neg, neg_dotProduct, dotProduct_neg, neg_neg]; exact hx0
    have hd0 : ∀ j ∈ T, d j = 0 := by
      intro j hj
      have hsum0 : ∑ j ∈ T, ‖d j‖ ^ 2 = 0 := by rw [← hNy, hyx]
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 hsum0 j hj
      simpa using this
    funext ι
    rcases ι with ⟨i, hi⟩ | ⟨j, hj⟩
    · have := hc0 i hi
      simpa [c, hi] using this
    · have := hd0 j hj
      simpa [d, hj] using this
  have hrank : Fintype.card (S ⊕ T) = M.rank := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hle := M.rank_le_card_height
  rw [← hrank, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at hle
  exact hle

/-- Negative eigenvalues: filled modes below the gap. -/
def negCount {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℕ :=
  (univ.filter fun i => hA.eigenvalues i < 0).card

/-- Positive eigenvalues. -/
def posCount {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℕ :=
  (univ.filter fun i => 0 < hA.eigenvalues i).card

lemma neg_add_pos_le {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    negCount hA + posCount hA ≤ Fintype.card n := by
  unfold negCount posCount
  rw [← Finset.card_union_of_disjoint]
  · exact (Finset.card_le_univ _)
  · rw [Finset.disjoint_filter]; intro i _ h1 h2; linarith

lemma eig_ne_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0) (i : n) :
    hA.eigenvalues i ≠ 0 := by
  intro h
  apply hdet
  rw [hA.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

lemma neg_add_pos_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    negCount hA + posCount hA = Fintype.card n := by
  unfold negCount posCount
  rw [← Finset.card_union_of_disjoint]
  · rw [← Finset.card_univ]; congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases lt_or_gt_of_ne (eig_ne_zero hA hdet i) with h | h
    · left; exact h
    · right; exact h
  · rw [Finset.disjoint_filter]; intro i _ h1 h2; linarith

lemma exists_gap {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    ∃ δ > 0, ∀ i, δ ≤ |hA.eigenvalues i| := by
  by_cases hne : (univ : Finset n).Nonempty
  · refine ⟨univ.inf' hne fun i => |hA.eigenvalues i|, ?_, fun i => Finset.inf'_le _ (mem_univ i)⟩
    show 0 < _
    rw [Finset.lt_inf'_iff]
    exact fun i _ => abs_pos.2 (eig_ne_zero hA hdet i)
  · refine ⟨1, one_pos, fun i => absurd ⟨i, mem_univ i⟩ hne⟩

/-- **The negative-mode count is stable near an invertible Hermitian matrix.** -/
theorem negCount_stable {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    ∃ ε > 0, ∀ (B : Matrix n n ℂ) (hB : B.IsHermitian),
      (∑ i, ∑ j, ‖(B - A) i j‖) < ε → negCount hB = negCount hA := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hA hdet
  refine ⟨δ, hδ, fun B hB hE => ?_⟩
  have h1 := count_le hA hB 1 δ (Or.inl rfl) hδ (univ.filter fun i => hA.eigenvalues i < 0)
    (univ.filter fun j => 0 ≤ hB.eigenvalues j)
    (fun i hi => by
      have h := (Finset.mem_filter.1 hi).2
      have := hgap i; rw [abs_of_neg h] at this; linarith)
    (fun j hj => by have := (Finset.mem_filter.1 hj).2; linarith) hE
  have h2 := count_le hA hB (-1) δ (Or.inr rfl) hδ (univ.filter fun i => 0 < hA.eigenvalues i)
    (univ.filter fun j => hB.eigenvalues j ≤ 0)
    (fun i hi => by
      have h := (Finset.mem_filter.1 hi).2
      have := hgap i; rw [abs_of_pos h] at this; linarith)
    (fun j hj => by have := (Finset.mem_filter.1 hj).2; linarith) hE
  have c1 := Finset.card_filter_add_card_filter_not (s := univ) (fun j => hB.eigenvalues j < 0)
  have c2 := Finset.card_filter_add_card_filter_not (s := univ) (fun j => 0 < hB.eigenvalues j)
  simp only [not_lt] at c1 c2
  have hA' := neg_add_pos_eq hA hdet
  have hB' := neg_add_pos_le hB
  unfold negCount posCount at *
  rw [Finset.card_univ] at c1 c2
  omega

/-- **Along a continuous family of invertible Hermitian matrices the count is locally constant.** -/
theorem negCount_locallyConstant {X : Type*} [TopologicalSpace X] (H : X → Matrix n n ℂ)
    (hc : Continuous H) (hherm : ∀ x, (H x).IsHermitian) (hdet : ∀ x, (H x).det ≠ 0) :
    IsLocallyConstant fun x => negCount (hherm x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨ε, hε, hstab⟩ := negCount_stable (hherm x) (hdet x)
  have hent : ∀ i j, Continuous fun y => H y i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hc)
  have hcont : Continuous fun y => ∑ i, ∑ j, ‖(H y - H x) i j‖ := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    simp only [Matrix.sub_apply]
    exact ((hent i j).sub continuous_const).norm
  have h0 : (∑ i, ∑ j, ‖(H x - H x) i j‖) < ε := by simpa using hε
  filter_upwards [(hcont.tendsto x).eventually (gt_mem_nhds h0)] with y hy
  exact hstab (H y) (hherm y) hy

end PMAction.InertiaStability
