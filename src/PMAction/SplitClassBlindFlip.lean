import PMAction.ClassBlindFlip
import PMTransport.Machine.CarrierVacuumSector
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The shorter quarter-aligned class-blind flip

A split of the signed block uses twelve forward root pulses. The exact
finite carrier certificate uses Gaussian integers, with one factor of two
per primitive pulse to clear its denominators.
-/

noncomputable section
namespace PMAction.SplitClassBlindFlip
open Matrix CarrierEvents CarrierParity PairedRootFlip

private abbrev Instruction := Fin 3 × Fin 4 × Bool

/-- The root index and whether to use three quarter-times instead of one. -/
private def word : List Instruction :=
  [(1,0,false), (1,2,false), (0,0,true), (0,1,true), (0,2,true), (0,3,true),
   (1,1,true), (1,3,true), (0,3,false), (0,2,false), (0,1,false), (0,0,false)]

private def quarters (ins : Instruction) : ℕ := if ins.2.2 then 3 else 1

private def step (c : Fin 3) (p : ℝ) (ins : Instruction) :=
  RootTransferPhase.phase (rootEvent c ins.1 ins.2.1) p
    ((quarters ins : ℝ) * RootTransferPhase.quarterTime p)

def pulse (c : Fin 3) (p : ℝ) : Matrix (Carrier c) (Carrier c) ℂ :=
  (word.map (step c p)).prod

def duration (p : ℝ) : ℝ :=
  (word.map fun i => (quarters i : ℝ) * RootTransferPhase.quarterTime p).sum

theorem duration_eq (p : ℝ) : duration p = 24 * RootTransferPhase.quarterTime p := by
  simp [duration, word, quarters]
  ring

private def imag : GaussianInt := ⟨0,1⟩

private def scaledStep (c : Fin 3) (ins : Instruction) (v : Carrier c → GaussianInt) :
    Carrier c → GaussianInt :=
  let z := if ins.2.2 then imag else -imag
  fun i => let j := rootEvent c ins.1 ins.2.1 i
    if j = i then 2 * v i else (1 + z) * v i + (1 - z) * v j

private def basis (c : Fin 3) (j : Carrier c) (i : Carrier c) : GaussianInt :=
  if i = j then 1 else 0

private def target (c : Fin 3) (v : Carrier c → GaussianInt) (i : Carrier c) : GaussianInt :=
  v i + v (antipode c i) + imag *
    (v (CarrierWeyl.lookup c 0 i) - v (antipode c (CarrierWeyl.lookup c 0 i)))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem certificate : ∀ c : Fin 3, ∀ i j : Carrier c,
    (word.foldr (scaledStep c) (basis c j)) i =
      2048 * target c (basis c j) i := by
  decide +kernel

private theorem imag_complex : (imag : ℂ) = Complex.I := by
  simp [imag, GaussianInt.toComplex_def']

private theorem scaledStep_complex (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (ins : Instruction) (v : Carrier c → GaussianInt) :
    (fun i => (scaledStep c ins v i : ℂ)) = (2 : ℂ) • (step c p ins *ᵥ fun i => (v i : ℂ)) := by
  obtain ⟨a,j,s⟩ := ins
  rw [step, RootTransferPhase.phase_formula _ (root_twice c a j)]
  have hphase : Complex.exp
      (-(RootTransferPhase.gap p * ((quarters (a,j,s) : ℝ) *
        RootTransferPhase.quarterTime p) : ℝ) * Complex.I) =
      ((if s then imag else -imag : GaussianInt) : ℂ) := by
    cases s
    · simp only [quarters, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, one_mul,
        quarter_coeff p hp hp1, GaussianInt.toComplex_neg, imag_complex]
    · simpa only [quarters, ↓reduceIte, Nat.cast_ofNat, imag_complex] using
        EvenRootPhase.phaseI_coefficient c p hp hp1
  rw [hphase]
  funext i
  simp only [InvolutionSpectral.plus, InvolutionSpectral.minus, add_mulVec,
    sub_mulVec, smul_mulVec, one_mulVec, permMatrix_mulVec, Function.comp_apply, Pi.smul_apply,
    Pi.add_apply, Pi.sub_apply, smul_eq_mul, scaledStep]
  by_cases heq : rootEvent c a j i = i
  · simp [heq, map_ofNat, GaussianInt.toComplex_mul]
    ring
  · simp [heq, GaussianInt.toComplex_add, GaussianInt.toComplex_sub,
      GaussianInt.toComplex_mul, GaussianInt.toComplex_one]
    ring

private theorem word_complex (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (program : List Instruction) (v : Carrier c → GaussianInt) :
    (fun i => (program.foldr (scaledStep c) v i : ℂ)) =
      (2 : ℂ) ^ program.length • ((program.map (step c p)).prod *ᵥ fun i => (v i : ℂ)) := by
  induction program with
  | nil => simp
  | cons ins tail ih =>
      rw [List.foldr_cons, scaledStep_complex c p hp hp1, ih, mulVec_smul, smul_smul]
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ← mulVec_mulVec]
      rw [mul_comm (2 : ℂ)]

/-- The twelve-pulse circuit realizes the same completed certain flip. -/
theorem pulse_completed (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    pulse c p = IsometricDynamics.extend (embedding c) (Complex.I • ConcreteFermion.beta) := by
  classical
  have hemb := CarrierVacuumSector.beta_intertwining c
  have hb : CarrierVacuumSector.beta c * (embedding c * (embedding c)ᴴ) =
      embedding c * ConcreteFermion.beta * (embedding c)ᴴ := by
    rw [← Matrix.mul_assoc, hemb]
  have htarget :
      (2 : ℂ) • IsometricDynamics.extend (embedding c) (Complex.I • ConcreteFermion.beta) =
        1 + (antipode c).permMatrix ℂ +
          Complex.I • (CarrierVacuumSector.beta c * (1 - (antipode c).permMatrix ℂ)) := by
    have hB : embedding c * (Complex.I • ConcreteFermion.beta) * (embedding c)ᴴ =
        (Complex.I * (1 / 2) : ℂ) •
          (CarrierVacuumSector.beta c * (1 - (antipode c).permMatrix ℂ)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, ← hb, projector, Matrix.mul_smul, smul_smul]
    rw [IsometricDynamics.extend, IsometricDynamics.complement, hB, projector]
    module
  ext i j
  let v := basis c j
  have hv : (fun k => (v k : ℂ)) = Pi.single j 1 := by
    ext k
    by_cases h : k = j <;> simp [v, basis, h, GaussianInt.toComplex_one,
      GaussianInt.toComplex_zero]
  have hc := congrFun (word_complex c p hp hp1 word v) i
  rw [hv, ← pulse, Matrix.mulVec_single_one] at hc
  norm_num [Pi.smul_apply, Matrix.col, smul_eq_mul, show word.length = 12 from rfl] at hc
  rw [certificate c i j, GaussianInt.toComplex_mul] at hc
  have hcheck : (target c v i : ℂ) =
      ((2 : ℂ) • IsometricDynamics.extend (embedding c) (Complex.I • ConcreteFermion.beta)) i j := by
    calc
      _ = ((1 + (antipode c).permMatrix ℂ +
          Complex.I • (CarrierVacuumSector.beta c * (1 - (antipode c).permMatrix ℂ))) *ᵥ
          fun k => (v k : ℂ)) i := by
        simp only [add_mulVec, smul_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec,
          permMatrix_mulVec, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, CarrierVacuumSector.beta, target, GaussianInt.toComplex_add,
          GaussianInt.toComplex_sub, GaussianInt.toComplex_mul, imag_complex]
      _ = _ := by rw [← htarget, hv, Matrix.mulVec_single_one]; rfl
  rw [hcheck, Matrix.smul_apply, smul_eq_mul] at hc
  norm_num [GaussianInt.toComplex] at hc
  linear_combination -hc / 4096

/-- With one whole tick per common root quarter-time, the shorter flip
and a serial six-reflection word fit within the elapsed time of a substrate
frame. This counts available time; it supplies no assignment of active slots. -/
theorem one_tick_budget :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ RootTransferPhase.quarterTime p = 1 ∧
      duration p + 6 * (2 * RootTransferPhase.quarterTime p) = 36 ∧
      (PMSubstrate.E8Values.N : ℝ) < 36 ∧ 36 ≤ (PMSubstrate.E8Values.Delta : ℝ) := by
  let p := (1 - Real.exp (-Real.pi / 4)) / 2
  have hp : 0 < p := by
    have he := Real.exp_lt_one_iff.mpr (show -Real.pi / 4 < 0 by linarith [Real.pi_pos])
    dsimp [p]
    linarith
  have hp1 : p < 1 / 2 := by
    dsimp [p]
    linarith [Real.exp_pos (-Real.pi / 4)]
  have hr : RootTransferPhase.residual p = Real.exp (-Real.pi / 4) := by
    dsimp [RootTransferPhase.residual, p]
    ring
  have hg : RootTransferPhase.gap p = Real.pi / 2 := by
    rw [RootTransferPhase.gap, hr, Real.log_exp]
    ring
  have hq : RootTransferPhase.quarterTime p = 1 := by
    rw [RootTransferPhase.quarterTime, hg]
    field_simp [Real.pi_ne_zero]
  refine ⟨p, hp, hp1, hq, ?_, ?_, ?_⟩
  · rw [duration_eq, hq]
    norm_num
  · norm_num [show PMSubstrate.E8Values.N = 32 from rfl]
  · norm_num [show PMSubstrate.E8Values.Delta = 43 from rfl]

end PMAction.SplitClassBlindFlip
