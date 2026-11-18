import PMAction.NativeFlavourWall
import PMAction.CyclicSeesaw
import PMAction.WallCurrentWeights

/-! A gap-calibration test within the existing two-wall Hamiltonian family.
The reference wall is undetuned and its reference state stays stationary for
every crossing strength while the other-wall flip is held fixed. -/
noncomputable section
namespace PMAction.WallGapCalibration
open Matrix ConcreteFermion WallChiralCurrent ChiralLightBand

def link (y : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := (y : ℂ) • 1

def H (u v y : ℝ) : Matrix Sites Sites ℂ :=
  fromBlocks ((u : ℂ) • beta) ((y : ℂ) • WallExchange.hop)
    ((y : ℂ) • WallExchange.back) ((v : ℂ) • beta)

def flavourIndex : Sites → (Fin 4 × Fin 1) ⊕ (Fin 4 × Fin 1)
  | .inl i => .inl (i,0)
  | .inr i => .inr (i,0)

theorem wall_identification (u v y : ℝ) :
    H u v y = (WallExchange.H2 0 u v (link y)).submatrix flavourIndex flavourIndex := by
  ext (i | i) (j | j) <;>
    simp [H, WallExchange.H2, WallExchange.diag, WallExchange.K, flavourIndex, submatrix, link, mul_comm]

theorem hermitian (u v y : ℝ) : (H u v y).IsHermitian := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [H, Matrix.conjTranspose_apply, beta, WallExchange.hop, WallExchange.back]

def reference : Sites → ℂ := Sum.elim (fun _ => 0) ![0,0,1,0]

theorem reference_stationary (u y : ℝ) : H u 0 y *ᵥ reference = 0 := by
  ext (i | i) <;> fin_cases i <;>
    simp [H, reference, beta, WallExchange.hop, WallExchange.back,
      mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four]

/-- All crossing values have the existing native realization at fixed
native clock, detuning and coordinate readout. -/
theorem native_family (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (u y : ℝ) :
    NativeObservation.Obs (NativeFlavourWall.coordinate c)
      (NativeFlavourWall.nativeHamiltonian2 c p 0 u 0 (link y))
      (WallExchange.H2 0 u 0 (link y)) := by
  have hz : NativeFlavourWall.momentum (0 : Fin 3 → ℝ) = 0 := by
    ext j
    change Real.sin 0 = 0
    exact Real.sin_zero
  have h := NativeFlavourWall.native_observed2 c p hp hp1 0 u 0 (link y)
  rw [hz] at h
  exact h

/-- A fixed nonzero flip and stationary reference admit every positive
flip-to-crossing ratio in this Hamiltonian family. -/
theorem arbitrary_relative_gap (u : ℝ) (hu : u ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ y : ℝ, 0 < y ∧ |u| / y = r ∧ H u 0 y *ᵥ reference = 0 := by
  refine ⟨|u| / r, div_pos (abs_pos.mpr hu) hr, ?_, reference_stationary _ _⟩
  field_simp

/-- Spin-up zero-energy states with an arbitrary light reference amplitude.
This diagnostic family does not select an external-state preparation. -/
def signal (u y : ℝ) (a d : ℂ) : Sites → ℂ :=
  Sum.elim ![a,0,0,0] ![(u/y : ℝ) * a,0,d,0]

theorem signal_stationary (u y : ℝ) (hy : y ≠ 0) (a d : ℂ) :
    H u 0 y *ᵥ signal u y a d = 0 := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  ext (i | i) <;> fin_cases i <;>
    simp [H, signal, beta, WallExchange.hop, WallExchange.back,
      mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four]
  field_simp [hyC]
  ring

theorem signal_weights (u y : ℝ) (a d : ℂ) :
    WallCurrentWeights.lightWeight (signal u y a d) = Complex.normSq a + Complex.normSq d ∧
    WallCurrentWeights.gapWeight (signal u y a d) = (u/y)^2 * Complex.normSq a ∧
    WallCurrentWeights.chargedLightWeight (signal u y a d) = Complex.normSq d ∧
    WallCurrentWeights.chargedGapWeight (signal u y a d) = 0 := by
  simp [signal, WallCurrentWeights.lightWeight, WallCurrentWeights.gapWeight,
    WallCurrentWeights.chargedLightWeight, WallCurrentWeights.chargedGapWeight,
    WallCurrentWeights.oppositeGapWeight, Complex.normSq_mul, pow_two]
  left
  ring

/-- The charged readout of this diagnostic zero-mode family is independent
of its opposite-chirality gapped amplitude. -/
theorem signal_current (u y : ℝ) (a d : ℂ) :
    projector *ᵥ signal u y a d = d • reference := by
  ext (i | i) <;> fin_cases i <;>
    norm_num [signal, reference, projector, chirality, gamma,
      mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four]

/-- A precise gap-to-weight relation in the one-leg zero-energy sector.
The external-state/readout identification is a separate construction. -/
theorem diagnostic_loss (u y : ℝ) (hy : y ≠ 0) :
    WallCurrentWeights.gapWeight (signal u y 1 0) /
      (WallCurrentWeights.lightWeight (signal u y 1 0) +
        WallCurrentWeights.gapWeight (signal u y 1 0)) = u^2 / (y^2 + u^2) := by
  have hw := signal_weights u y 1 0
  rw [hw.1, hw.2.1]
  norm_num only [Complex.normSq_one, Complex.normSq_zero, add_zero, mul_one]
  have hs : y^2 + u^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hy) (sq_nonneg u))
  have hr : 1 + (u/y)^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hy, hs, hr]

/-- Stationarity at exact resonance leaves the normalized charged fraction
free over the entire unit interval in the one-leg spin-up family. -/
theorem stationary_charged_fraction (u y f : ℝ) (hy : y ≠ 0)
    (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    ∃ a d : ℂ, H u 0 y *ᵥ signal u y a d = 0 ∧
      WallCurrentWeights.lightWeight (signal u y a d) +
        WallCurrentWeights.gapWeight (signal u y a d) = 1 ∧
      WallCurrentWeights.chargedLightWeight (signal u y a d) = f ∧
      WallCurrentWeights.chargedGapWeight (signal u y a d) = 0 := by
  let z : ℝ := 1 + (u / y) ^ 2
  have hz : 0 < z := by dsimp [z]; positivity
  let a : ℂ := (Real.sqrt ((1 - f) / z) : ℝ)
  let d : ℂ := (Real.sqrt f : ℝ)
  have ha : Complex.normSq a = (1 - f) / z := by
    dsimp only [a]
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (div_nonneg (sub_nonneg.mpr hf1) hz.le)]
  have hd : Complex.normSq d = f := by
    dsimp only [d]
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt hf]
  obtain ⟨hl, hg, hcl, hcg⟩ := signal_weights u y a d
  refine ⟨a, d, signal_stationary u y hy a d, ?_, hcl.trans hd, hcg⟩
  rw [hl, hg, ha, hd]
  calc
    (1 - f) / z + f + (u / y) ^ 2 * ((1 - f) / z) =
        z * ((1 - f) / z) + f := by dsimp [z]; ring
    _ = 1 := by field_simp [hz.ne']; ring

/-- The same free crossing scale respects the three-label glue support. -/
def cyclicLink (y : ℝ) := CyclicSeesaw.cyc (fun _ => (y : ℂ))

theorem native_cyclic_family (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) (u y : ℝ) :
    NativeObservation.Obs (NativeFlavourWall.coordinate c)
      (NativeFlavourWall.nativeHamiltonian2 c p 0 u 0 (cyclicLink y))
      (WallExchange.H2 0 u 0 (cyclicLink y)) := by
  have hz : NativeFlavourWall.momentum (0 : Fin 3 → ℝ) = 0 := by
    ext j
    exact Real.sin_zero
  have h := NativeFlavourWall.native_observed2 c p hp hp1 0 u 0 (cyclicLink y)
  rw [hz] at h
  exact h

def cyclicReference (g : Fin 3) : ((Fin 4 × Fin 3) ⊕ (Fin 4 × Fin 3)) → ℂ :=
  Pi.single (.inr (2,g)) 1

theorem cyclic_reference_stationary (u y : ℝ) (g : Fin 3) :
    WallExchange.H2 0 u 0 (cyclicLink y) *ᵥ cyclicReference g = 0 := by
  unfold cyclicReference
  rw [Matrix.mulVec_single_one]
  ext (⟨i,j⟩ | ⟨i,j⟩) <;> fin_cases i <;>
    simp [WallExchange.H2, WallExchange.diag, WallExchange.K, WallExchange.hop]

/-- The very same nonzero encoded reference is stationary across the
whole cyclic-link family, at a fixed native clock and fixed flip. -/
theorem native_reference (c : Fin 3) (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2)
    (u y : ℝ) (g : Fin 3) :
    let ψ := NativeFlavourWall.coordinate c *ᵥ cyclicReference g
    ψ ≠ 0 ∧ NativeFlavourWall.nativeHamiltonian2 c p 0 u 0 (cyclicLink y) *ᵥ ψ = 0 := by
  constructor
  · intro h
    have he := congrArg (fun v => (NativeFlavourWall.coordinate c)ᴴ *ᵥ v) h
    rw [mulVec_mulVec, NativeFlavourWall.coordinate_isometry, one_mulVec, mulVec_zero] at he
    have hg := congrFun he (.inr (2,g))
    norm_num [cyclicReference] at hg
  · rw [mulVec_mulVec, (native_cyclic_family c p hp hp1 u y).1,
      ← mulVec_mulVec, cyclic_reference_stationary, mulVec_zero]

theorem arbitrary_cyclic_ratio (u : ℝ) (hu : u ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ y : ℝ, 0 < y ∧ |u| / y = r ∧
      ∀ g, WallExchange.H2 0 u 0 (cyclicLink y) *ᵥ cyclicReference g = 0 := by
  obtain ⟨y, hy, hyr, _⟩ := arbitrary_relative_gap u hu r hr
  exact ⟨y,hy,hyr,cyclic_reference_stationary u y⟩

theorem cyclic_gap_square (y : ℝ) :
    WallSeesaw.G (cyclicLink y) * WallSeesaw.G (cyclicLink y) =
      ((y^2 : ℝ) : ℂ) • (1 : Matrix ((Fin 3) ⊕ (Fin 3)) _ ℂ) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    norm_num [WallSeesaw.G, cyclicLink, CyclicSeesaw.cyc, Matrix.conjTranspose_apply,
      mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, pow_two]

end PMAction.WallGapCalibration
