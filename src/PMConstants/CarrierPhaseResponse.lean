import PMConstants.CarrierActions

/-! Hypercharge-sensitive carrier readout. The existing charge/axis premises
are inherited. A neutral reference's maintenance is not inferred from charge support. -/
noncomputable section
namespace PMConstants.CarrierPhaseResponse
open Matrix Finset CarrierActions
open PMAction.InterferenceReadout

/-- Existing endpoint-charge assignment on the actual carrier packet. -/
def charge (v : Packet) : ℚ := RequirementTable.hyper Hypercharge.standard (channelType v)

def link (θ : ℝ) : Matrix Packet Packet ℂ :=
  diagonal (fun v => Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I))

lemma phase_unit (x : ℝ) :
    star (Complex.exp ((x : ℂ)*Complex.I))*Complex.exp ((x : ℂ)*Complex.I)=1 := by
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem link_unitary (θ : ℝ) : link θ ∈ unitary (Matrix Packet Packet ℂ) := by
  constructor
  · change (link θ)ᴴ*link θ=1
    simp only [link, diagonal_conjTranspose, diagonal_mul_diagonal]
    change diagonal (fun v => star (Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I))*
      Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I))=1
    simp only [phase_unit, diagonal_one]
  · change link θ*(link θ)ᴴ=1
    simp only [link, diagonal_conjTranspose, diagonal_mul_diagonal]
    change diagonal (fun v => Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I)*
      star (Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I)))=1
    simpa only [mul_comm] using (show diagonal (fun v : Packet =>
      star (Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I))*
        Complex.exp (((θ*(charge v : ℝ) : ℝ) : ℂ)*Complex.I))=1 by
      simp only [phase_unit, diagonal_one])

theorem flag_response (θ : ℝ) (v : Packet) :
    flagProbability (link θ) v=(1-Real.cos (θ*(charge v : ℝ)))/2 := by
  rw [flag_formula _ (link_unitary θ)]
  simp only [link, diagonal_apply_eq, Complex.exp_ofReal_mul_I_re]

lemma charge_bound (v : Packet) : |(charge v : ℝ)| ≤ 2 := by
  cases h : channelType v <;> norm_num [charge, h, RequirementTable.hyper, Hypercharge.standard]

/-- A nonzero sufficiently small probe angle detects exactly nonzero charge. -/
theorem flag_zero_iff (θ : ℝ) (hθ : θ ≠ 0) (hsmall : |θ| < Real.pi) (v : Packet) :
    flagProbability (link θ) v=0 ↔ charge v=0 := by
  have hb : |θ*(charge v : ℝ)| < 2*Real.pi := by
    calc
      _ = |θ| * |(charge v : ℝ)| := abs_mul _ _
      _ ≤ |θ| * 2 := mul_le_mul_of_nonneg_left (charge_bound v) (abs_nonneg θ)
      _ < 2*Real.pi := by linarith
  rw [flag_response]
  constructor
  · intro h
    have hc : Real.cos (θ*(charge v : ℝ))=1 := by linarith
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt (neg_lt_of_abs_lt hb) (lt_of_abs_lt hb)).mp hc
    have hq : (charge v : ℝ)=0 := (mul_eq_zero.mp hz).resolve_left hθ
    exact_mod_cast hq
  · intro h; simp [h]

def charged : Finset Packet := univ.filter (fun v => charge v ≠ 0)
def neutral : Finset Packet := univ.filter (fun v => charge v = 0)

theorem charge_counts : charged.card=15 ∧ neutral.card=1 := by
  constructor <;> decide +kernel

theorem neutral_is_reference : ∀ v : Packet, charge v=0 ↔ index v=15 := by decide +kernel

/-- The neutral label has no phase flag for any angle, even outside the small-angle domain. -/
theorem neutral_no_flag (θ : ℝ) (v : Packet) (h : v ∈ neutral) :
    flagProbability (link θ) v=0 := by
  have hq : charge v=0 := (mem_filter.mp h).2
  rw [flag_response, hq]
  simp

theorem flag_positive_iff (θ : ℝ) (hθ : θ ≠ 0) (hsmall : |θ| < Real.pi) (v : Packet) :
    0 < flagProbability (link θ) v ↔ v ∈ charged := by
  have hn := flag_nonneg (link θ) v
  have he := flag_zero_iff θ hθ hsmall v
  simp only [charged, mem_filter, mem_univ, true_and]
  constructor
  · intro hp hz; have := he.mpr hz; linarith
  · intro hq
    have hne : flagProbability (link θ) v ≠ 0 := fun h => hq (he.mp h)
    exact lt_of_le_of_ne hn (Ne.symm hne)

def flagged (θ : ℝ) : Finset Packet := by
  classical
  exact univ.filter (fun v => 0 < flagProbability (link θ) v)

/-- In this direct phase-readout contract exactly fifteen carrier labels respond. -/
theorem flagged_card (θ : ℝ) (hθ : θ ≠ 0) (hsmall : |θ| < Real.pi) :
    (flagged θ).card=15 := by
  classical
  have he : univ.filter (fun v => 0 < flagProbability (link θ) v)=charged := by
    ext v; simp [flag_positive_iff θ hθ hsmall]
  change (univ.filter (fun v => 0 < flagProbability (link θ) v)).card=15
  rw [he]
  exact charge_counts.1

end PMConstants.CarrierPhaseResponse
