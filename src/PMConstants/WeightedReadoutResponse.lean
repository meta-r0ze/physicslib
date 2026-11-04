import PMConstants.MeanTraceResponse

/-! The event/response map for supplied nonnegative preparation or work weights.
No equal sector normalization or uniform ensemble is inserted. -/
noncomputable section
namespace PMConstants.WeightedReadoutResponse
open Matrix Finset PMAction PMAction.InterferenceReadout
open LinkSpectralResponse LinkSpectralResponse.HermitianTransport
variable {n : Type*} [Fintype n] [DecidableEq n]

def score (p : n → ℝ) (U : Matrix n n ℂ) : ℝ := ∑ i, p i*flagProbability U i
def trace (p : n → ℝ) (X : Matrix n n ℂ) : ℝ := ∑ i, p i*(X i i).re

/-- Nonnegative normalized preparation gives a valid probability for the
existing squared-amplitude comparison, with no uniform-law hypothesis. -/
theorem score_bounds (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, p i=1)
    (U : Matrix n n ℂ) (hu : U ∈ unitary _) : 0 ≤ score p U ∧ score p U ≤ 1 := by
  constructor
  · exact sum_nonneg (fun i _ => mul_nonneg (hp i) (flag_nonneg U i))
  · calc
      score p U ≤ ∑ i, p i*1 := sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (flag_bounds U hu i).2 (hp i))
      _ = 1 := by simpa using hn

theorem trace_formula (p : n → ℝ) (U : Matrix n n ℂ) (hu : U ∈ unitary _) :
    score p U=((∑ i, p i)-trace p U)/2 := by
  calc
    score p U = ∑ i, (p i-p i*(U i i).re)/2 := by
      apply sum_congr rfl
      intro i _; rw [flag_formula U hu]; ring
    _ = ((∑ i, p i)-trace p U)/2 := by rw [← sum_div,sum_sub_distrib]; rfl

/-- A common toll and repair length price the actual weighted flags. Distinct
repair lengths or refresh densities must instead be included in their weights. -/
theorem repair_pricing (p : n → ℝ) (toll : ℝ) (m : ℕ) (U : Matrix n n ℂ) :
    (∑ i, p i*CommonResponse.responseCost toll m (flagProbability U i))=
      toll*m*score p U := by
  simp only [CommonResponse.responseCost,score,mul_sum]
  apply sum_congr rfl
  intro i _; ring

lemma basis_energy (H : Matrix n n ℂ) (i : n) :
    CommonResponse.nsq (H*ᵥ Pi.single i 1)=((Hᴴ*H) i i).re := by
  simp [CommonResponse.nsq,dotProduct,Matrix.col_apply,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum]

variable {H : Matrix n n ℂ}

def coefficient (p : n → ℝ) (h : H.IsHermitian) : ℝ :=
  ∑ i, p i*HermitianTransport.coefficient h (Pi.single i 1)/4

lemma coefficient_nonneg (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (h : H.IsHermitian) :
    0 ≤ coefficient p h := by
  exact sum_nonneg (fun i _ => div_nonneg
    (mul_nonneg (hp i) (HermitianTransport.coefficient_nonneg h _)) (by norm_num))

lemma basis_controlled (h : H.IsHermitian) (i : n) {ε : ℝ} (he : |ε| ≤ radius h) :
    |flagProbability (transport h ε) i-ε^2*((H*H) i i).re/4| ≤
      HermitianTransport.coefficient h (Pi.single i 1)/4*ε^4 := by
  have hb := controlled_response h (Pi.single i 1) he
  rw [basis_energy,h.eq] at hb
  rw [← CommonResponse.basis_case _ (transport_unitary h ε) i]
  unfold CommonResponse.stateFlag
  calc
    _ = |CommonResponse.nsq (Pi.single i 1-transport h ε*ᵥ Pi.single i 1)-
        ε^2*((H*H) i i).re|/4 := by rw [← sub_div,abs_div]; norm_num
    _ ≤ (HermitianTransport.coefficient h (Pi.single i 1)*ε^4)/4 :=
      div_le_div_of_nonneg_right hb (by norm_num)
    _ = _ := by ring

/-- A controlled weighted quadratic response, with an automatically supplied
spectral radius and error coefficient. The weights need not sum to one if they
represent work intensities rather than probabilities. -/
theorem controlled (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (h : H.IsHermitian)
    {ε : ℝ} (he : |ε| ≤ radius h) :
    |score p (transport h ε)-ε^2*trace p (H*H)/4| ≤ coefficient p h*ε^4 := by
  have heq : score p (transport h ε)-ε^2*trace p (H*H)/4=
      ∑ i, p i*(flagProbability (transport h ε) i-ε^2*((H*H) i i).re/4) := by
    rw [score,trace,mul_sum,sum_div,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _; ring
  rw [heq]
  calc
    _ ≤ ∑ i, |p i*(flagProbability (transport h ε) i-ε^2*((H*H) i i).re/4)| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ i, p i*|flagProbability (transport h ε) i-ε^2*((H*H) i i).re/4| := by
      simp only [abs_mul,abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i*(HermitianTransport.coefficient h (Pi.single i 1)/4*ε^4) :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (basis_controlled h i he) (hp i))
    _ = coefficient p h*ε^4 := by
      simp only [coefficient,sum_mul]
      apply sum_congr rfl
      intro i _; ring

theorem exponential (p : n → ℝ) (hp : ∀ i, 0 ≤ p i) (h : H.IsHermitian)
    {ε : ℝ} (he : |ε| ≤ radius h) :
    |score p (NormedSpace.exp (((ε : ℂ)*Complex.I) • H))-ε^2*trace p (H*H)/4| ≤
      coefficient p h*ε^4 := by
  rw [← LinkEvolution.transport_eq_exp h ε]
  exact controlled p hp h he

end PMConstants.WeightedReadoutResponse
