import PMKAutomaton.Machine.RootTransfer
import PMAction.InvolutionSpectral

/-!
# Coherent phase evolution reconstructed from the lazy root transfer

The supplied attempt rate determines the gap -2 log(1-2p). The positive
two-tick transfer is exactly the Euclidean exponential of this Hermitian
generator. Its coherent phase evolution reaches the root quarter-pulse at
a proved positive real time, with its phase retained. At twice that time
the phase is exactly the root permutation; a serial word of such pulses
has the ordered permutation product. Integer clock matching still
requires selecting the attempt rate.
-/
noncomputable section
namespace PMAction.RootTransferPhase
open Matrix InvolutionSpectral
variable {n : Type*} [Fintype n] [DecidableEq n]

def residual (p : ℝ) : ℝ := 1-2*p
def gap (p : ℝ) : ℝ := -2 * Real.log (residual p)

def transfer (e : Equiv.Perm n) (p : ℝ) : Matrix n n ℂ :=
  fun i j => (RootTransfer.transfer e p i j : ℂ)

lemma permutation_square (e : Equiv.Perm n) (he : Function.Involutive e) :
    e.permMatrix ℂ * e.permMatrix ℂ = 1 := by
  have hsq : e*e=1 := by ext x; exact he x
  rw [← permMatrix_mul, hsq, permMatrix_one]

omit [Fintype n] in
lemma permutation_hermitian (e : Equiv.Perm n) (he : Function.Involutive e) :
    (e.permMatrix ℂ).IsHermitian := by
  change (e.permMatrix ℂ)ᴴ=e.permMatrix ℂ
  rw [conjTranspose_permMatrix, RootTransfer.inverse_self e he]

omit [Fintype n] in
/-- The complex operator is the entrywise complexification of the real transfer. -/
lemma complexification (e : Equiv.Perm n) (p : ℝ) (i j : n) :
    transfer e p i j = (RootTransfer.transfer e p i j : ℂ) := rfl

omit [Fintype n] in
/-- The complex form of the lazy transfer, for operator calculations. -/
lemma transfer_eq_sum (e : Equiv.Perm n) (p : ℝ) :
    transfer e p = ((1-p : ℝ) : ℂ) • 1 + (p : ℂ) • e.permMatrix ℂ := by
  ext i j
  simp [transfer, RootTransfer.transfer, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype n] in
lemma sectors (e : Equiv.Perm n) (p : ℝ) :
    transfer e p = plus (e.permMatrix ℂ) + (residual p : ℂ) • minus (e.permMatrix ℂ) := by
  rw [transfer_eq_sum]
  unfold plus minus residual
  push_cast
  module

lemma square (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ) :
    transfer e p * transfer e p = plus (e.permMatrix ℂ) +
      ((residual p : ℂ)^2) • minus (e.permMatrix ℂ) := by
  rw [sectors]
  have h := products _ (permutation_square e he)
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h.1, h.2.1,
    h.2.2.1, h.2.2.2, smul_zero, add_zero, zero_add, smul_smul, pow_two]

lemma residual_positive (p : ℝ) (hp : p < 1/2) : 0 < residual p := by unfold residual; linarith

lemma gap_positive (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) : 0 < gap p := by
  have h0 := residual_positive p hp1
  have h1 : residual p < 1 := by unfold residual; linarith
  have hl := Real.log_neg h0 h1
  unfold gap
  linarith

lemma heat_scalar (p : ℝ) (hp : p < 1/2) : Real.exp (-gap p) = residual p ^ 2 := by
  have h : -gap p = Real.log (residual p) + Real.log (residual p) := by unfold gap; ring
  rw [h, Real.exp_add, Real.exp_log (residual_positive p hp), pow_two]

lemma complex_heat_scalar (p : ℝ) (hp : p < 1/2) :
    Complex.exp (-(gap p : ℂ)) = (residual p : ℂ)^2 := by
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, heat_scalar p hp, Complex.ofReal_pow]

def generator (e : Equiv.Perm n) (p : ℝ) : Matrix n n ℂ :=
  (gap p : ℂ) • minus (e.permMatrix ℂ)

omit [Fintype n] in
lemma generator_hermitian (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ) :
    (generator e p).IsHermitian := by
  change (generator e p)ᴴ=generator e p
  simp [generator, minus, conjTranspose_smul, conjTranspose_sub,
    (permutation_hermitian e he).eq]

open scoped Matrix.Norms.Operator in
/-- The logarithmic Hamiltonian is verified against the actual two-tick transfer. -/
theorem heat_matches (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ) (hp : p < 1/2) :
    NormedSpace.exp (-generator e p) = transfer e p * transfer e p := by
  have h : -generator e p = (0 : ℂ) • plus (e.permMatrix ℂ) +
      (-(gap p : ℂ)) • minus (e.permMatrix ℂ) := by simp [generator]
  rw [h, exp_sectors _ (permutation_square e he), Complex.exp_zero, one_smul,
    complex_heat_scalar p hp, square e he p]

open scoped Matrix.Norms.Operator in
def phase (e : Equiv.Perm n) (p t : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp ((((-t : ℝ) : ℂ) * Complex.I) • generator e p)

open scoped Matrix.Norms.Operator in
theorem phase_unitary (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) :
    phase e p t ∈ unitary (Matrix n n ℂ) := by
  rw [phase, ← LinkEvolution.transport_eq_exp (generator_hermitian e he p) (-t)]
  exact HermitianTransport.transport_unitary _ _

open scoped Matrix.Norms.Operator in
lemma phase_formula (e : Equiv.Perm n) (he : Function.Involutive e) (p t : ℝ) :
    phase e p t = plus (e.permMatrix ℂ) +
      Complex.exp (-(gap p * t : ℝ) * Complex.I) • minus (e.permMatrix ℂ) := by
  have h : ((((-t : ℝ) : ℂ) * Complex.I) • generator e p) =
      (0 : ℂ) • plus (e.permMatrix ℂ) +
        (-(gap p * t : ℝ) * Complex.I) • minus (e.permMatrix ℂ) := by
    simp only [generator, zero_smul, zero_add, smul_smul]
    congr 1
    push_cast
    ring
  rw [phase, h, exp_sectors _ (permutation_square e he), Complex.exp_zero, one_smul]

def quarterTime (p : ℝ) : ℝ := Real.pi / (2 * gap p)

theorem quarterTime_positive (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) : 0 < quarterTime p := by
  unfold quarterTime
  exact div_pos Real.pi_pos (mul_pos (by norm_num) (gap_positive p hp hp1))

open scoped Matrix.Norms.Operator in
/-- Reconstruction produces the required coherent root pulse, including its scalar phase. -/
theorem quarter_pulse (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    phase e p (quarterTime p) = Complex.exp (-(Real.pi/4 : ℝ) * Complex.I) •
      LocalUnitary.rotation (e.permMatrix ℂ) (Real.pi/4) := by
  have hn : gap p ≠ 0 := ne_of_gt (gap_positive p hp hp1)
  have ht : gap p * quarterTime p = Real.pi/2 := by
    unfold quarterTime
    field_simp [hn]
  rw [phase_formula e he p, ht]
  have h := phase_rotation (e.permMatrix ℂ) (Real.pi/4)
  rw [show 2*(Real.pi/4 : ℝ)=Real.pi/2 by ring] at h
  exact h

/-- A half-period pulse implements the root permutation with its exact phase. -/
theorem half_pulse (e : Equiv.Perm n) (he : Function.Involutive e) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    phase e p (2 * quarterTime p) = e.permMatrix ℂ := by
  have ht : gap p * (2 * quarterTime p) = Real.pi := by
    rw [quarterTime]
    field_simp [(gap_positive p hp hp1).ne']
  rw [phase_formula e he p, ht]
  have hexp : Complex.exp (-(Real.pi : ℂ) * Complex.I) = -1 := by simp
  rw [hexp]
  simp only [InvolutionSpectral.plus, InvolutionSpectral.minus, neg_one_smul]
  module

/-- An ordered word of involutive root permutations is realized by a serial
half-pulse word. The time sum counts serial execution on the common clock. -/
theorem half_pulse_word (word : List (Equiv.Perm n))
    (hword : ∀ e ∈ word, Function.Involutive e) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1/2) :
    (word.map (fun e => phase e p (2 * quarterTime p))).prod =
      (word.map (fun e => e.permMatrix ℂ)).prod ∧
    (word.map (fun _ => 2 * quarterTime p)).sum =
      (word.length : ℝ) * (2 * quarterTime p) := by
  constructor
  · congr 1
    apply List.map_congr_left
    intro e he
    exact half_pulse e (hword e he) p hp hp1
  · induction word with
    | nil => simp
    | cons e es ih =>
        have htail := ih (fun f hf => hword f (List.mem_cons_of_mem e hf))
        simp only [List.map_cons, List.sum_cons, htail, List.length_cons, Nat.cast_add,
          Nat.cast_one]
        ring

/-- With unit-duration integer ticks, principal-quarter matching imposes an
additional exact rate/clock calibration. It is not a consequence of stationarity. -/
theorem integer_tick_calibration (p : ℝ) (hp : p < 1/2) (N : ℕ) (hN : 0 < N)
    (hclock : gap p * N = Real.pi/2) :
    residual p = Real.exp (-Real.pi / (4*N)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hl : Real.log (residual p) = -Real.pi / (4*N) := by
    apply (eq_div_iff (by positivity : (4 : ℝ)*N ≠ 0)).mpr
    unfold gap at hclock
    nlinarith
  rw [← Real.exp_log (residual_positive p hp), hl]

end PMAction.RootTransferPhase
