import PMAction.CommonResponse

/-!
# Flat links are the most persistent

`CommonResponse` prices every transport readout at the common toll: a carrier `φ` carried around
a loop with holonomy `U` raises a flag with probability `stateFlag U φ = ‖φ − Uφ‖²/4`, and each
flag costs `toll · m`. This file proves that the total cost is minimized exactly by flat links.

* `nsq_eq_sum`, `nsq_eq_zero`: the squared norm is the sum of `|xᵢ|²` and vanishes only at zero.
* `flag_nonneg`, `flag_zero_iff`: a flag probability is nonnegative and vanishes exactly when the
  holonomy fixes the carrier.
* `cost_nonneg`, `total_cost_zero_iff`: for positive toll and repair length, the summed cost over
  any family of loop readouts is nonnegative, and zero exactly when every holonomy fixes its
  carrier.
* `flat_of_basis`: a holonomy that fixes every basis carrier is the identity.
* `flat_iff`: probing each loop with every colour basis carrier, the total cost is zero exactly
  when every holonomy is `1`, that is, when the links are flat.

So the minimum-cost (most persistent) link configuration is the flat one, by the same
positive-change-price argument as `PersistentBackground` and `CompletionSelection`. For the
hadron this means: with no mean colour source (three carriers in one mode form a singlet, whose
mean colour density vanishes at every site), the persistent links carry no colour field, so
colour-magnetic coupling to spin enters only through fluctuations, which cost toll. The singlet
statement and the fluctuation size are not proved here.
-/

noncomputable section
namespace PMAction.FlatPersistence
open Matrix Finset PMAction.CommonResponse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma nsq_eq_sum (x : ι → ℂ) : nsq x = ∑ i, Complex.normSq (x i) := by
  unfold nsq dotProduct
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

omit [DecidableEq ι] in
lemma nsq_eq_zero (x : ι → ℂ) : nsq x = 0 ↔ x = 0 := by
  rw [nsq_eq_sum, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)]
  constructor
  · intro h; funext i; exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · rintro rfl i _; simp

omit [DecidableEq ι] in
lemma flag_nonneg (U : Matrix ι ι ℂ) (φ : ι → ℂ) : 0 ≤ stateFlag U φ := by
  unfold stateFlag
  rw [nsq_eq_sum]
  exact div_nonneg (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) (by norm_num)

omit [DecidableEq ι] in
/-- A flag is never raised exactly when the holonomy fixes the carrier. -/
theorem flag_zero_iff (U : Matrix ι ι ℂ) (φ : ι → ℂ) : stateFlag U φ = 0 ↔ U *ᵥ φ = φ := by
  unfold stateFlag
  rw [div_eq_zero_iff, or_iff_left (by norm_num : (4 : ℝ) ≠ 0), nsq_eq_zero, sub_eq_zero,
    eq_comm]

omit [DecidableEq ι] in
theorem cost_nonneg {P : Type*} [Fintype P] (toll : ℝ) (htoll : 0 < toll) (m : ℕ)
    (U : P → Matrix ι ι ℂ) (φ : P → ι → ℂ) :
    0 ≤ ∑ p, responseCost toll m (stateFlag (U p) (φ p)) := by
  refine Finset.sum_nonneg fun p _ => ?_
  unfold responseCost
  exact mul_nonneg (mul_nonneg htoll.le (Nat.cast_nonneg m)) (flag_nonneg _ _)

omit [DecidableEq ι] in
/-- **Zero total cost iff every holonomy fixes its carrier.** -/
theorem total_cost_zero_iff {P : Type*} [Fintype P] (toll : ℝ) (htoll : 0 < toll) (m : ℕ)
    (hm : 0 < m) (U : P → Matrix ι ι ℂ) (φ : P → ι → ℂ) :
    (∑ p, responseCost toll m (stateFlag (U p) (φ p))) = 0 ↔ ∀ p, U p *ᵥ φ p = φ p := by
  have hc : 0 < toll * (m : ℝ) := mul_pos htoll (by exact_mod_cast hm)
  simp only [responseCost]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg hc.le (flag_nonneg _ _))]
  constructor
  · intro h p
    have h' := h p (Finset.mem_univ p)
    rw [mul_eq_zero, or_iff_right hc.ne'] at h'
    exact (flag_zero_iff _ _).mp h'
  · intro h p _
    rw [(flag_zero_iff _ _).mpr (h p), mul_zero]

/-- A holonomy fixing every basis carrier is the identity. -/
theorem flat_of_basis (U : Matrix ι ι ℂ) (hU : ∀ a, U *ᵥ Pi.single a 1 = Pi.single a 1) :
    U = 1 := by
  ext i j
  have h := congrFun (hU j) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h

/-- **Flat links are the most persistent.** Probing every loop with every colour basis
carrier, the total cost (which is never negative, `cost_nonneg`) is zero exactly when every
holonomy is the identity. -/
theorem flat_iff {P : Type*} [Fintype P] (toll : ℝ) (htoll : 0 < toll) (m : ℕ) (hm : 0 < m)
    (U : P → Matrix ι ι ℂ) :
    (∑ q : P × ι, responseCost toll m (stateFlag (U q.1) (Pi.single q.2 1))) = 0 ↔
      ∀ p, U p = 1 := by
  refine (total_cost_zero_iff toll htoll m hm (fun q : P × ι => U q.1)
    (fun q : P × ι => Pi.single q.2 1)).trans ?_
  constructor
  · intro h p
    exact flat_of_basis (U p) (fun a => h (p, a))
  · intro h q
    show U q.1 *ᵥ Pi.single q.2 1 = Pi.single q.2 1
    rw [h q.1, one_mulVec]

end PMAction.FlatPersistence
