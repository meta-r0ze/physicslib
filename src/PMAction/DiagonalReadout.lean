import PMAction.Machine.InterferenceReadout
import PMAction.LinkEvolution
import PMAction.TollAmplitude
import PMAction.CommonResponse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Readouts of a charge-diagonal transport

Many readouts compare a phase transport `exp(i t Q)` with its reference, where `Q` is diagonal
in the channel basis (a hypercharge, a colour phase, a clock phase). This module does that
calculation once.

* `flag x = (1 − cos x)/2 = sin²(x/2)` (`flag_eq_sin_sq`), in `[0, 1]` (`flag_bounds`), even
  (`flag_neg`).
* `transport_eq_diagonal`: for Hermitian `H = diag(q)` the transport is
  `diag(exp(i t q_c))`.
* `transport_flag`: for Hermitian `H = diag(q)`, the flag of the transport `exp(i t H)` on
  channel `c` is `flag (t q_c)`. Only the channel's own charge enters.
* `state_flag`: on a superposition the flag is the `|φ_c|²`-weighted mean of the channel flags.
* `flag_mul`: the flag at `n x` is the Chebyshev polynomial `(1 − T_n(1 − 2f))/2` of the flag
  `f` at `x`, for every integer `n`. So on charges that are integer multiples of one unit, one
  flag fixes every other. `flag_two`: `4f(1 − f)`; `flag_three`: `f(3 − 4f)²`.
* `toll`, `toll_sub`: a schedule of steps `tᵢ` with counts `wᵢ` charges a channel of charge
  `q` the Toll `floor + Σᵢ wᵢ flag(tᵢ q)`; differences between channels do not depend on the
  floor. `amplitude_ratio`: the amplitude ratio is `exp(−ΔT/2)`
  (`TollAmplitude.amplitude_ratio`).
-/

noncomputable section
namespace PMAction.DiagonalReadout
open Real Matrix

/-- The flag of a phase `x`. -/
def flag (x : ℝ) : ℝ := (1 - cos x) / 2

theorem flag_eq_sin_sq (x : ℝ) : flag x = sin (x / 2) ^ 2 := by
  have h := cos_sq (x / 2)
  have h2 := sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  unfold flag; linarith

theorem flag_bounds (x : ℝ) : 0 ≤ flag x ∧ flag x ≤ 1 := by
  unfold flag; constructor <;> linarith [cos_le_one x, neg_one_le_cos x]

@[simp] theorem flag_neg (x : ℝ) : flag (-x) = flag x := by simp [flag]

@[simp] theorem flag_zero : flag 0 = 0 := by simp [flag]

theorem flag_pi : flag π = 1 := by norm_num [flag]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator in
/-- **A diagonal generator transports by phases.** -/
theorem transport_eq_diagonal {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (q : ι → ℝ)
    (hd : H = diagonal fun i => (q i : ℂ)) (t : ℝ) :
    HermitianTransport.transport hH t =
      diagonal fun i => Complex.exp (((t * q i : ℝ) : ℂ) * Complex.I) := by
  rw [LinkEvolution.transport_eq_exp, hd, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring

/-- **The flag of a diagonal transport.** -/
theorem transport_flag {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (q : ι → ℝ)
    (hd : H = diagonal fun i => (q i : ℂ)) (t : ℝ) (c : ι) :
    InterferenceReadout.flagProbability (HermitianTransport.transport hH t) c = flag (t * q c) := by
  rw [InterferenceReadout.flag_formula _ (HermitianTransport.transport_unitary hH t),
    transport_eq_diagonal hH q hd, Matrix.diagonal_apply_eq, Complex.exp_ofReal_mul_I_re, flag]

/-- `|1 − e^{iθ}|² = 4 flag θ`. -/
theorem normSq_one_sub_exp (θ : ℝ) :
    Complex.normSq (1 - Complex.exp ((θ : ℂ) * Complex.I)) = 4 * flag θ := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im,
    Complex.one_im, Complex.add_im, Complex.mul_im]
  unfold flag
  nlinarith [sin_sq_add_cos_sq θ]

/-- **The flag of a superposition.** For a diagonal generator, a state's flag is the
`|φ_c|²`-weighted mean of its channels' flags: channels do not interfere in the readout. -/
theorem state_flag {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (q : ι → ℝ)
    (hd : H = diagonal fun i => (q i : ℂ)) (t : ℝ) (φ : ι → ℂ) :
    CommonResponse.stateFlag (HermitianTransport.transport hH t) φ =
      ∑ c, Complex.normSq (φ c) * flag (t * q c) := by
  rw [CommonResponse.stateFlag, transport_eq_diagonal hH q hd, LinkExpansion.nsq_eq,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.sub_apply, mulVec_diagonal]
  have : φ c - Complex.exp (((t * q c : ℝ) : ℂ) * Complex.I) * φ c =
      (1 - Complex.exp (((t * q c : ℝ) : ℂ) * Complex.I)) * φ c := by ring
  rw [this, Complex.normSq_mul, normSq_one_sub_exp]
  ring

/-- The flag at an integer multiple, as a Chebyshev polynomial of the flag. -/
def chebFlag (n : ℤ) (f : ℝ) : ℝ := (1 - (Polynomial.Chebyshev.T ℝ n).eval (1 - 2 * f)) / 2

/-- **Multiples.** `flag (n x) = (1 − T_n(1 − 2 flag x))/2`. -/
theorem flag_mul (n : ℤ) (x : ℝ) : flag (n * x) = chebFlag n (flag x) := by
  have h : 1 - 2 * flag x = cos x := by unfold flag; ring
  rw [chebFlag, h, Polynomial.Chebyshev.T_real_cos, flag]

/-- `flag (2x) = 4f(1 − f)`. -/
theorem flag_two (x : ℝ) : flag (2 * x) = 4 * flag x * (1 - flag x) := by
  unfold flag; rw [cos_two_mul]; ring_nf

/-- `flag (3x) = f(3 − 4f)²`. -/
theorem flag_three (x : ℝ) : flag (3 * x) = flag x * (3 - 4 * flag x) ^ 2 := by
  unfold flag; rw [cos_three_mul]; ring

/-- A schedule's Toll on a channel of charge `q`. -/
def toll {κ : Type*} [Fintype κ] (floor : ℝ) (w t : κ → ℝ) (q : ℝ) : ℝ :=
  floor + ∑ i, w i * flag (t i * q)

/-- Toll differences do not depend on the floor. -/
theorem toll_sub {κ : Type*} [Fintype κ] (floor : ℝ) (w t : κ → ℝ) (q q' : ℝ) :
    toll floor w t q - toll floor w t q' = ∑ i, w i * (flag (t i * q) - flag (t i * q')) := by
  simp only [toll, mul_sub, Finset.sum_sub_distrib]; ring

/-- **Amplitude ratios** of two channels under one schedule. -/
theorem amplitude_ratio {κ : Type*} [Fintype κ] (floor : ℝ) (w t : κ → ℝ) (q q' : ℝ) :
    TollAmplitude.wireAmplitude (toll floor w t q) / TollAmplitude.wireAmplitude (toll floor w t q')
      = exp (-(∑ i, w i * (flag (t i * q) - flag (t i * q'))) / 2) := by
  rw [toll, toll, TollAmplitude.amplitude_ratio, ← toll_sub floor w t q q', toll, toll]
  congr 1; ring

end PMAction.DiagonalReadout
