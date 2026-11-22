import PMElementaryParticles.CoherentRing

/-!
# Plane waves for the coherent ring

A plane wave on `Fin n × (Unit ⊕ Unit)` is `exp(i k j) u(d)` with
`k = 2π m / n`.  The full-firing tick shifts the site forward on `.inl` and
backward on `.inr`, so the shift multiplies the `.inl` component by `exp(+i k)`
and the `.inr` component by `exp(-i k)`.  The momentum block is therefore
`M = encounter x * diag(exp(i k), exp(-i k))`.

The certified encounter, the momentum action, the trace and determinant, the
eigenvalue identity, and the empty-firing limit are all proved below.  The
dispersion relation is `cos E = cos(x/2) cos k`, with zero-momentum offset
`E(0) = x/2` for `0 ≤ x ≤ π`.  That offset is a gap, not a mass.
-/

noncomputable section
namespace PMElementaryParticles.Dispersion

open Matrix PMAction
open PMElementaryParticles.CoherentRing
open PMElementaryParticles.PhaseToRecord

/-- Wavenumber of momentum mode `m`. -/
noncomputable def waveNumber (n : ℕ) (m : Fin n) : ℝ :=
  2 * Real.pi * (m.val : ℝ) / (n : ℝ)

/-- Plane wave on the ring. -/
def planeWave (n : ℕ) (m : Fin n) (u : Unit ⊕ Unit → ℂ) :
    Fin n × (Unit ⊕ Unit) → ℂ :=
  fun p => Complex.exp (((waveNumber n m * (p.1.val : ℝ) : ℝ) : ℂ) * Complex.I) * u p.2

/-- Shift phase in the direction order `(inl, inr)`. -/
def shiftDiag (k : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  diagonal fun d =>
    match d with
    | Sum.inl _ => Complex.exp ((k : ℂ) * Complex.I)
    | Sum.inr _ => Complex.exp ((-(k : ℂ)) * Complex.I)

/-- Momentum block of the full-firing tick. -/
def M (x k : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  encounter x * shiftDiag k

theorem planeWave_exp_period (n : ℕ) (m : Fin n) (hn : (n : ℝ) ≠ 0) :
    Complex.exp (((waveNumber n m * (n : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have hk : waveNumber n m * (n : ℝ) = 2 * Real.pi * (m.val : ℝ) := by
    unfold waveNumber
    field_simp [hn]
  rw [hk]
  have h : (((2 * Real.pi * (m.val : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h]
  exact Complex.exp_nat_mul_two_pi_mul_I m.val

/-! ## Step 1: explicit entries of the encounter -/

/-- Diagonal entry `(inl, inl)`: `e^{ix/2} cos(x/2)`. -/
theorem encounter_inl_inl (x : ℝ) :
    encounter x (.inl ()) (.inl ()) =
      Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * ((Real.cos (x / 2) : ℝ) : ℂ) := by
  unfold encounter converter CoherentComparisonRepair.compare CoherentComparisonRepair.plus
    PMAction.InterferenceReadout.phase
  rw [Matrix.fromBlocks_apply₁₁]
  change (1/2 : ℂ) * (1 + Complex.exp ((x:ℂ)*Complex.I)) =
    Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * ((Real.cos (x / 2) : ℝ) : ℂ)
  rw [Complex.ofReal_cos]
  have hc : Complex.cos ((x/2:ℝ):ℂ) =
      (Complex.exp (((x/2:ℝ):ℂ)*Complex.I) + Complex.exp (-((x/2:ℝ):ℂ)*Complex.I))/2 := by
    have h := Complex.two_cos ((x/2:ℝ):ℂ)
    rw [← h]; ring
  rw [hc]
  have hx : Complex.exp ((x:ℂ)*Complex.I) =
      Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (((x/2:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hx]
  have hab : Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (-((x/2:ℝ):ℂ)*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have h : ((x/2:ℝ):ℂ)*Complex.I + (-((x/2:ℝ):ℂ))*Complex.I = 0 := by ring
    rw [h, Complex.exp_zero]
  linear_combination (-1/2 : ℂ) * hab

/-- Off-diagonal entry `(inl, inr)`: `-i e^{ix/2} sin(x/2)`. -/
theorem encounter_inl_inr (x : ℝ) :
    encounter x (.inl ()) (.inr ()) =
      -Complex.I * Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * ((Real.sin (x / 2) : ℝ) : ℂ) := by
  unfold encounter converter CoherentComparisonRepair.compare CoherentComparisonRepair.minus
    PMAction.InterferenceReadout.phase
  rw [Matrix.fromBlocks_apply₁₂]
  change (1/2 : ℂ) * (1 - Complex.exp ((x:ℂ)*Complex.I)) =
    -Complex.I * Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * ((Real.sin (x / 2) : ℝ) : ℂ)
  rw [Complex.ofReal_sin]
  have hs : Complex.sin ((x/2:ℝ):ℂ) =
      (Complex.exp (-((x/2:ℝ):ℂ)*Complex.I) - Complex.exp (((x/2:ℝ):ℂ)*Complex.I)) * Complex.I / 2 := by
    have h := Complex.two_sin ((x/2:ℝ):ℂ)
    rw [← h]; ring
  rw [hs]
  have hx : Complex.exp ((x:ℂ)*Complex.I) =
      Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (((x/2:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hx]
  have hab : Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (-((x/2:ℝ):ℂ)*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have h : ((x/2:ℝ):ℂ)*Complex.I + (-((x/2:ℝ):ℂ))*Complex.I = 0 := by ring
    rw [h, Complex.exp_zero]
  linear_combination ((1/2) * (1 - Complex.exp (((x/2:ℝ):ℂ)*Complex.I)^2)) * Complex.I_sq + (Complex.I^2/2) * hab

/-- Lower-left entry `(inr, inl)` equals the upper-right entry. -/
theorem encounter_inr_inl (x : ℝ) :
    encounter x (.inr ()) (.inl ()) = encounter x (.inl ()) (.inr ()) := rfl

/-- Lower-right entry `(inr, inr)` equals the upper-left entry. -/
theorem encounter_inr_inr (x : ℝ) :
    encounter x (.inr ()) (.inr ()) = encounter x (.inl ()) (.inl ()) := rfl

/-! ## Step 2: momentum action -/

/-- A plane wave is periodic: `exp(i k (j % n)) = exp(i k j)`. -/
theorem exp_waveNumber_mod (n : ℕ) (m : Fin n) (hn : (n : ℝ) ≠ 0) (q : ℕ) :
    Complex.exp (((waveNumber n m * ((q % n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((waveNumber n m * (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hk : waveNumber n m * (n : ℝ) = 2 * Real.pi * ((m.val : ℕ) : ℝ) := by
    unfold waveNumber; field_simp [hn]
  have hq : (q : ℝ) = ((q % n : ℕ) : ℝ) + (n : ℝ) * ((q / n : ℕ) : ℝ) := by
    calc (q : ℝ) = ((n * (q / n) + q % n : ℕ) : ℝ) := by rw [Nat.div_add_mod]
      _ = ((q % n : ℕ) : ℝ) + (n : ℝ) * ((q / n : ℕ) : ℝ) := by push_cast; ring
  have hR : waveNumber n m * (q : ℝ) =
      waveNumber n m * ((q % n : ℕ) : ℝ) + ((q / n : ℕ) : ℝ) * ((m.val : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [hq]
    have h2 : waveNumber n m * ((n : ℝ) * ((q / n : ℕ) : ℝ)) =
        ((q / n : ℕ) : ℝ) * ((m.val : ℕ) : ℝ) * (2 * Real.pi) := by
      rw [← mul_assoc, hk]; ring
    rw [mul_add, h2]
  have hC : (((waveNumber n m * (q : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((waveNumber n m * ((q % n : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
        (((q / n : ℕ) * m.val : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hR]; push_cast; ring
  rw [hC, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- The `.inl` shift multiplies by `exp(i k)`. -/
theorem shiftDiag_inl (k : ℝ) (u : Unit ⊕ Unit → ℂ) :
    (shiftDiag k *ᵥ u) (Sum.inl ()) = Complex.exp ((k:ℂ)*Complex.I) * u (Sum.inl ()) := by
  simp [shiftDiag, Matrix.mulVec_diagonal]

/-- The `.inr` shift multiplies by `exp(-i k)`. -/
theorem shiftDiag_inr (k : ℝ) (u : Unit ⊕ Unit → ℂ) :
    (shiftDiag k *ᵥ u) (Sum.inr ()) = Complex.exp (-(k:ℂ)*Complex.I) * u (Sum.inr ()) := by
  simp [shiftDiag, Matrix.mulVec_diagonal]

/-- The shift sends `(j, inl)` to `(j+1, inl)` and multiplies by `exp(i k)`. -/
theorem shift_inl (n : ℕ) (m : Fin n) (u : Unit ⊕ Unit → ℂ) (hn : (n : ℝ) ≠ 0) (j : Fin n) :
    ((ringShift n).permMatrix ℂ *ᵥ planeWave n m u) (j, Sum.inl ()) =
      Complex.exp (((waveNumber n m * (j.val : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((waveNumber n m : ℂ) * Complex.I) * u (Sum.inl ()) := by
  rw [Matrix.permMatrix_mulVec]
  show Complex.exp (((waveNumber n m * ((finRotate n j).val : ℝ) : ℝ) : ℂ) * Complex.I) *
      u (Sum.inl ()) = _
  have hval : (finRotate n j).val = (j.val + 1) % n := by
    rw [finRotate_apply, Fin.val_add]
    norm_num
  rw [hval, exp_waveNumber_mod n m hn (j.val + 1)]
  have harg : (((waveNumber n m * ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((waveNumber n m * (j.val : ℝ) : ℝ) : ℂ) * Complex.I) + ((waveNumber n m : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_add]

/-- The shift sends `(j, inr)` to `(j-1, inr)` and multiplies by `exp(-i k)`. -/
theorem shift_inr (n : ℕ) (m : Fin n) (u : Unit ⊕ Unit → ℂ) (hn : (n : ℝ) ≠ 0) (j : Fin n) :
    ((ringShift n).permMatrix ℂ *ᵥ planeWave n m u) (j, Sum.inr ()) =
      Complex.exp (((waveNumber n m * (j.val : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(waveNumber n m : ℂ) * Complex.I) * u (Sum.inr ()) := by
  rw [Matrix.permMatrix_mulVec]
  show Complex.exp (((waveNumber n m * (((finRotate n).symm j).val : ℝ) : ℝ) : ℂ) * Complex.I) *
      u (Sum.inr ()) = _
  have hval : ((finRotate n).symm j).val = (n - 1 + j.val) % n := by
    rw [finRotate_symm_apply, Fin.val_sub]
    by_cases hn1 : n = 1
    · subst hn1
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      simp
    · have hn0 : n ≠ 0 := by intro h; rw [h] at hn; norm_num at hn
      have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
      norm_num
      rw [h1]
  rw [hval, exp_waveNumber_mod n m hn (n - 1 + j.val)]
  have hn1 : 0 < n := Nat.pos_of_ne_zero (by intro h; rw [h] at hn; norm_num at hn)
  have hcastC : ((n - 1 : ℕ) : ℂ) + 1 = ((n : ℕ) : ℂ) := by
    have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn1
    rw [← h]; push_cast; ring
  have hkey : Complex.exp (((waveNumber n m * ((n - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(waveNumber n m : ℂ) * Complex.I) := by
    have h1 : Complex.exp (((waveNumber n m * ((n - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((waveNumber n m : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have hsum : (((waveNumber n m * ((n - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
          ((waveNumber n m : ℂ) * Complex.I) = (((waveNumber n m * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
        push_cast
        rw [← hcastC]
        ring
      rw [hsum, planeWave_exp_period n m hn]
    have h2 : Complex.exp (-(waveNumber n m : ℂ) * Complex.I) *
        Complex.exp ((waveNumber n m : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have : -(waveNumber n m : ℂ) * Complex.I + (waveNumber n m : ℂ) * Complex.I = 0 := by ring
      rw [this, Complex.exp_zero]
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  have harg : (((waveNumber n m * ((n - 1 + j.val : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((waveNumber n m * ((n - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) +
        (((waveNumber n m * (j.val : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_add, hkey]
  ring

/-- The shift acts on the plane wave as `exp(i k j)` times the diagonal shift. -/
theorem ringShift_planeWave (n : ℕ) (m : Fin n) (u : Unit ⊕ Unit → ℂ) (hn : (n : ℝ) ≠ 0) :
    (ringShift n).permMatrix ℂ *ᵥ planeWave n m u =
      fun p => Complex.exp (((waveNumber n m * (p.1.val : ℝ) : ℝ) : ℂ) * Complex.I) *
        (shiftDiag (waveNumber n m) *ᵥ u) p.2 := by
  funext p
  obtain ⟨j, d⟩ := p
  cases d with
  | inl _ =>
    rw [shift_inl n m u hn j, shiftDiag_inl]
    ring
  | inr _ =>
    rw [shift_inr n m u hn j, shiftDiag_inr]
    ring

/-- Kronecker product on the site factor. -/
theorem kron_one_mulVec (n : ℕ) (A : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ)
    (φ : Fin n × (Unit ⊕ Unit) → ℂ) :
    Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) A *ᵥ φ =
      fun p => (A *ᵥ fun d => φ (p.1, d)) p.2 := by
  let B : Matrix (Unit ⊕ Unit) (Fin n) ℂ := fun d i => φ (i, d)
  have hvec : Matrix.vec B = φ := by funext p; obtain ⟨i,d⟩ := p; rfl
  rw [← hvec]
  simp only [Matrix.kronecker]
  rw [← Matrix.vec_mul_eq_mulVec]
  funext p; obtain ⟨i,d⟩ := p
  simp [Matrix.vec, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

/-- The full-firing tick acts on a plane wave by the momentum block. -/
theorem ringTick_mulVec_planeWave (n : ℕ) (x : ℝ) (m : Fin n) (u : Unit ⊕ Unit → ℂ)
    (hn : (n : ℝ) ≠ 0) :
    ringTick n x *ᵥ planeWave n m u = planeWave n m (M x (waveNumber n m) *ᵥ u) := by
  rw [ringTick, ← Matrix.mulVec_mulVec, ringShift_planeWave n m u hn]
  funext p
  obtain ⟨j, d⟩ := p
  rw [kron_one_mulVec]
  change (encounter x *ᵥ ((Complex.exp (((waveNumber n m * (j.val : ℝ) : ℝ) : ℂ) * Complex.I)) •
      (shiftDiag (waveNumber n m) *ᵥ u))) d = _
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Matrix.mulVec_mulVec]
  rfl

/-! ## Step 3: trace and determinant -/

/-- A bijection `Unit ⊕ Unit ≃ Fin 2` for reading the determinant. -/
def e2 : Unit ⊕ Unit ≃ Fin 2 where
  toFun d := match d with | Sum.inl _ => 0 | Sum.inr _ => 1
  invFun i := if i = 0 then Sum.inl () else Sum.inr ()
  left_inv := by rintro (u | u) <;> simp
  right_inv := by intro i; fin_cases i <;> simp

@[simp] theorem e2_symm_zero : e2.symm 0 = Sum.inl () := rfl
@[simp] theorem e2_symm_one : e2.symm 1 = Sum.inr () := rfl

/-- Determinant of the certified encounter: `e^{ix}`. -/
theorem encounter_det (x : ℝ) : (encounter x).det = Complex.exp ((x:ℂ)*Complex.I) := by
  have h := Matrix.det_reindex_self e2 (encounter x)
  rw [← h]
  rw [Matrix.det_fin_two]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e2_symm_zero, e2_symm_one]
  rw [encounter_inr_inl, encounter_inr_inr, encounter_inl_inl, encounter_inl_inr]
  have hx : Complex.exp ((x:ℂ)*Complex.I) = Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (((x/2:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hx]
  have hcc : ((Real.cos (x/2):ℝ):ℂ)^2 + ((Real.sin (x/2):ℝ):ℂ)^2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_one]
    congr 1
    exact Real.cos_sq_add_sin_sq (x/2)
  have hIsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((Complex.exp (((x/2:ℝ):ℂ)*Complex.I))^2) * hcc + (-((Complex.exp (((x/2:ℝ):ℂ)*Complex.I))^2 * ((Real.sin (x/2):ℝ):ℂ)^2)) * hIsq

/-- Determinant of the shift: `1`. -/
theorem shiftDiag_det (k : ℝ) : (shiftDiag k).det = 1 := by
  rw [shiftDiag, Matrix.det_diagonal]
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  have hk : Complex.exp ((k:ℂ)*Complex.I) * Complex.exp (-(k:ℂ)*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have h : (k:ℂ)*Complex.I + (-(k:ℂ))*Complex.I = 0 := by ring
    rw [h, Complex.exp_zero]
  rw [hk]

/-- Determinant of the momentum block: `e^{ix}`. -/
theorem M_det (x k : ℝ) : (M x k).det = Complex.exp ((x:ℂ)*Complex.I) := by
  unfold M
  rw [Matrix.det_mul, shiftDiag_det, encounter_det, mul_one]

/-- Trace of the momentum block: `2 e^{ix/2} cos(x/2) cos k`. -/
theorem M_trace (x k : ℝ) :
    (M x k).trace = 2 * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * ((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ) := by
  unfold M shiftDiag
  rw [Matrix.trace]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.diag]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique]
  simp
  rw [encounter_inr_inr, encounter_inl_inl]
  simp only [Complex.ofReal_cos]
  have hx2 : ((x/2:ℝ):ℂ) = (x:ℂ)/2 := by push_cast; ring
  rw [hx2]
  have hk : -(↑k * Complex.I) = (-↑k) * Complex.I := by ring
  rw [hk]
  have hc : Complex.exp ((k:ℂ)*Complex.I) + Complex.exp (-(k:ℂ)*Complex.I) = 2 * Complex.cos ((k:ℂ)) := by
    rw [← Complex.two_cos]
  linear_combination (Complex.exp ((x:ℂ)/2 * Complex.I) * Complex.cos ((x:ℂ)/2)) * hc

/-! ## Step 4: eigenvalue identity -/

/-- If `cos E = cos(x/2) cos k`, then `λ = e^{ix/2} e^{iE}` satisfies the
characteristic equation `λ² − trace(M) λ + det(M) = 0`. -/
theorem M_eigenvalue_plus (x k E : ℝ) (hE : Real.cos E = Real.cos (x/2) * Real.cos k) :
    (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) ^ 2 -
      (M x k).trace * (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) +
      (M x k).det = 0 := by
  rw [M_trace, M_det]
  have hc : ((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ) = Complex.cos ((E:ℂ)) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_mul, ← hE, Complex.ofReal_cos]
  have hsq : Complex.exp ((x:ℂ)*Complex.I) =
      Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (((x/2:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hsq]
  have htwo : Complex.exp ((E:ℂ)*Complex.I) + Complex.exp (-(↑E * Complex.I)) = 2 * Complex.cos ((E:ℂ)) := by
    have h := Complex.two_cos ((E:ℂ))
    rw [show (-↑E * Complex.I : ℂ) = -(↑E * Complex.I) by ring] at h
    rw [h]
  have hmul : Complex.exp ((E:ℂ)*Complex.I) * Complex.exp (-(↑E * Complex.I)) = 1 := by
    rw [← Complex.exp_add]
    have : (↑E * Complex.I : ℂ) + (-(↑E * Complex.I)) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hassoc : ((Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) ^ 2 -
      (2 * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * ((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ)) *
        (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) +
      Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I)) =
      ((Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) ^ 2 -
      (2 * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * (((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ))) *
        (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) +
      Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I)) := by ring
  rw [hassoc, hc]
  linear_combination (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp ((E:ℂ) * Complex.I)) * htwo +
    (-(Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I))) * hmul

/-- If `cos E = cos(x/2) cos k`, then `λ = e^{ix/2} e^{-iE}` satisfies the
characteristic equation `λ² − trace(M) λ + det(M) = 0`. -/
theorem M_eigenvalue_minus (x k E : ℝ) (hE : Real.cos E = Real.cos (x/2) * Real.cos k) :
    (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) ^ 2 -
      (M x k).trace * (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) +
      (M x k).det = 0 := by
  rw [M_trace, M_det]
  have hc : ((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ) = Complex.cos ((E:ℂ)) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_mul, ← hE, Complex.ofReal_cos]
  have hsq : Complex.exp ((x:ℂ)*Complex.I) =
      Complex.exp (((x/2:ℝ):ℂ)*Complex.I) * Complex.exp (((x/2:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hsq]
  have htwo : Complex.exp (-(↑E * Complex.I)) + Complex.exp ((E:ℂ)*Complex.I) = 2 * Complex.cos ((E:ℂ)) := by
    have h := Complex.two_cos ((E:ℂ))
    rw [show (-↑E * Complex.I : ℂ) = -(↑E * Complex.I) by ring] at h
    rw [h]; ring
  have hmul : Complex.exp (-(↑E * Complex.I)) * Complex.exp ((E:ℂ)*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have : (-(↑E * Complex.I) : ℂ) + (↑E * Complex.I) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hassoc : ((Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) ^ 2 -
      (2 * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * ((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ)) *
        (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) +
      Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I)) =
      ((Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) ^ 2 -
      (2 * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * (((Real.cos (x/2):ℝ):ℂ) * Complex.cos (k:ℂ))) *
        (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) +
      Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I)) := by ring
  rw [hassoc, hc]
  linear_combination (Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (-(↑E * Complex.I))) * htwo +
    (-(Complex.exp (((x/2:ℝ):ℂ) * Complex.I) * Complex.exp (((x/2:ℝ):ℂ) * Complex.I))) * hmul

/-! ## Step 5: empty firing -/

/-- The uncertified phase at zero is the identity. -/
theorem phase_zero : PMAction.InterferenceReadout.phase 0 = (1 : Matrix Unit Unit ℂ) := by
  unfold PMAction.InterferenceReadout.phase
  ext i j
  simp

/-- The comparison of the identity is the identity. -/
theorem compare_one : CoherentComparisonRepair.compare (1 : Matrix Unit Unit ℂ) = 1 := by
  unfold CoherentComparisonRepair.compare CoherentComparisonRepair.plus CoherentComparisonRepair.minus
  ext i j
  rcases i with u | u <;> rcases j with v | v <;>
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    norm_num

/-- Empty firing: the encounter at zero is the identity. -/
theorem encounter_zero : encounter 0 = 1 := by
  unfold encounter converter
  rw [phase_zero, compare_one]

/-- Empty firing: the momentum block is the shift. -/
theorem M_zero (k : ℝ) : M 0 k = shiftDiag k := by
  unfold M
  rw [encounter_zero, one_mul]

/-- The `.inl` eigenvector of the shift. -/
def eInl : Unit ⊕ Unit → ℂ := fun d => if d = Sum.inl () then 1 else 0

/-- The `.inr` eigenvector of the shift. -/
def eInr : Unit ⊕ Unit → ℂ := fun d => if d = Sum.inr () then 1 else 0

/-- The shift has eigenvalue `e^{ik}` on the `.inl` direction. -/
theorem shiftDiag_eigen_inl (k : ℝ) :
    shiftDiag k *ᵥ eInl = Complex.exp ((k:ℂ)*Complex.I) • eInl := by
  funext d
  rcases d with u | u
  · rw [shiftDiag_inl]
    simp [eInl]
  · rw [shiftDiag_inr]
    simp [eInl]

/-- The shift has eigenvalue `e^{-ik}` on the `.inr` direction. -/
theorem shiftDiag_eigen_inr (k : ℝ) :
    shiftDiag k *ᵥ eInr = Complex.exp (-(k:ℂ)*Complex.I) • eInr := by
  funext d
  rcases d with u | u
  · rw [shiftDiag_inl]
    simp [eInr]
  · rw [shiftDiag_inr]
    simp [eInr]

/-- Empty firing: the eigenvalues of `M 0 k` are `e^{∓ik}`. -/
theorem M_zero_eigenvalues (k : ℝ) :
    M 0 k *ᵥ eInl = Complex.exp ((k:ℂ)*Complex.I) • eInl ∧
      M 0 k *ᵥ eInr = Complex.exp (-(k:ℂ)*Complex.I) • eInr := by
  rw [M_zero]
  exact ⟨shiftDiag_eigen_inl k, shiftDiag_eigen_inr k⟩

/-- Zero-momentum gap offset.  At `k = 0` the dispersion relation reads
`cos E = cos(x/2)`, so for `0 ≤ x ≤ π` the energy is `E = x/2`.  This is a gap,
not a mass. -/
theorem gap_offset (x k E : ℝ) (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi)
    (hE0 : 0 ≤ E) (hEπ : E ≤ Real.pi) (hk : k = 0)
    (hE : Real.cos E = Real.cos (x/2) * Real.cos k) :
    E = x/2 := by
  have hcos : Real.cos E = Real.cos (x/2) := by
    rw [hk, Real.cos_zero, mul_one] at hE; exact hE
  have hx2 : x/2 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
  have hE' : E ∈ Set.Icc 0 Real.pi := ⟨hE0, hEπ⟩
  exact Real.injOn_cos hE' hx2 hcos

end PMElementaryParticles.Dispersion
