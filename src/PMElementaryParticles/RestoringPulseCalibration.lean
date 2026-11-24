import PMElementaryParticles.RestoringWallShift
import PMAction.AlternatingReferenceNode

/-!
# Calibrating the restoring output

The steady series current and the amplitude of an isolated pair of
exchanges are distinct readouts. In the steady model the interior
port is at its balanced value. In the staged model the payload visits
the intermediate port once and exits after the second exchange.
-/

noncomputable section
namespace PMElementaryParticles.RestoringPulseCalibration

open Matrix RestoringWallShift
open PMAction.ReferenceNodeBoundary PMConstants.HandoffAdmittance

local notation "α" => PMSubstrate.causalCoupling

private theorem shifted_stay_weight (θ : ℝ) (g : Fin 3) (a : Fin 8) :
    Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inr (g + 1, a))) = Real.cos θ ^ 2 := by
  have h : pulsePorts (.inr (g, a)) = .inr (g + 1, a) := rfl
  unfold classPulse
  rw [Matrix.submatrix_apply, ← h, Equiv.symm_apply_apply]
  simp [PMAction.BranchMixerSynthesis.xPulse_blocks, Complex.normSq_ofReal,
    -Complex.ofReal_cos, pow_two]

/-- Output population on the shifted slot with independently supplied
incoherent input populations. The right input reaches this slot by exchange. -/
def shiftedOutflow (θ : ℝ) (g : Fin 3) (a : Fin 8) (l r : ℝ) : ℝ :=
  Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a))) * r +
    Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inr (g + 1, a))) * l

theorem shiftedOutflow_eq (θ : ℝ) (g : Fin 3) (a : Fin 8) (l r : ℝ) :
    shiftedOutflow θ g a l r =
      leftOutflow (Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a)))) l r := by
  rw [shiftedOutflow, shifted_stay_weight, classPulse_weight, leftOutflow,
    show Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ]]

/-- The shifted slot has weight `α/2` exactly when its current equals
the steady two-leg current at the floating interior port. -/
theorem shifted_weight_iff_steady_current (θ : ℝ) (g : Fin 3) (a : Fin 8) :
    let w := Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a)))
    (∀ l r : ℝ, shiftedOutflow θ g a l r - l = α * (r - center α α r l)) ↔ w = α / 2 := by
  intro w
  simp only [shiftedOutflow_eq]
  change (∀ l r : ℝ, leftOutflow w l r - l = α * (r - center α α r l)) ↔ w = α / 2
  have hα := PMSubstrate.causalCoupling_bounds.1
  have hseries := equal_floating α hα
  constructor
  · intro h
    apply through_eq_conductance
    intro l r
    rw [h, floating_current α α (by positivity), hseries]
  · intro h l r
    rw [node_current, h, floating_current α α (by positivity), hseries]

/-- A principal shifted pulse matching that same steady current has
the specified area. Its duration remains a separate clock input. -/
theorem steady_principal_area (θ : ℝ) (g : Fin 3) (a : Fin 8) (hθ : 0 ≤ θ)
    (hprincipal : θ ≤ Real.pi / 2)
    (hCurrent : ∀ l r : ℝ, shiftedOutflow θ g a l r - l = α * (r - center α α r l)) :
    θ = Real.arcsin (Real.sqrt (α / 2)) := by
  have hw := (shifted_weight_iff_steady_current θ g a).mp hCurrent
  rw [classPulse_weight] at hw
  exact PMAction.CertainTransferRate.principal_transfer_area hθ hprincipal hw

/-- The pulse-area rate ratio for a steady-current calibrated shifted
port and a certain direct transfer in a common time convention. -/
theorem steady_rate_ratio (g : Fin 3) (a : Fin 8)
    {θ direct moveTime directTime : ℝ}
    (hθ : 0 ≤ θ) (hprincipal : θ ≤ Real.pi / 2)
    (hd : 0 ≤ direct) (hdp : direct ≤ Real.pi / 2)
    (hm : 0 < moveTime) (hdt : 0 < directTime)
    (hCurrent : ∀ l r : ℝ, shiftedOutflow θ g a l r - l = α * (r - center α α r l))
    (hcertain : Real.sin direct ^ 2 = 1) :
    (θ / moveTime) / (direct / directTime) =
      (2 * Real.arcsin (Real.sqrt (α / 2)) / Real.pi) * (directTime / moveTime) :=
  classPulse_rate_ratio g a hθ hprincipal hd hdp hm hdt
    ((shifted_weight_iff_steady_current θ g a).mp hCurrent) hcertain

/-! ## Alternating incoherent visits to a retained center -/

open PMAction.AlternatingReferenceNode in
/-- Match the shifted port to the current per complete two-visit cycle. -/
theorem shifted_weight_iff_alternating_current (θ : ℝ) (g : Fin 3) (a : Fin 8)
    {w : ℝ} (hw₀ : 0 < w) (hw₁ : w ≤ 1) :
    let weight := Complex.normSq (classPulse θ (.inr (g + 1, a)) (.inl (g, a)))
    (∀ l r : ℝ, shiftedOutflow θ g a l r - l =
      visit w (fixedCenter w l r) r - fixedCenter w l r) ↔
      weight = w / (2 - w) := by
  intro weight
  simp only [shiftedOutflow_eq]
  change (∀ l r : ℝ, leftOutflow weight l r - l =
    visit w (fixedCenter w l r) r - fixedCenter w l r) ↔ _
  constructor
  · intro h
    apply through_eq_conductance
    intro l r
    rw [h, (fixed_current w l r hw₀ hw₁).1]
  · intro h l r
    rw [node_current, h, (fixed_current w l r hw₀ hw₁).1]

open PMAction.AlternatingReferenceNode PMAction.CertainTransferRate in
/-- The direct and alternating restoring rates relative to the crossing.
The restoring tick count covers the entire cycle supplying the measured
model current. The crossing area, Hamiltonian conversions and native
identification of the events are inputs. -/
theorem alternating_crossing_rate_ratios (g : Fin 3) (a : Fin 8)
    {θ direct crossing tick directTicks moveTicks crossTicks w : ℝ}
    (directFactor moveFactor crossFactor : ℝ)
    (hw₀ : 0 < w) (hw₁ : w ≤ 1)
    (hθ : 0 ≤ θ) (hprincipal : θ ≤ Real.pi / 2)
    (hd : 0 ≤ direct) (hdp : direct ≤ Real.pi / 2) (hcertain : Real.sin direct ^ 2 = 1)
    (ht : 0 < tick) (hdt : 0 < directTicks) (hmt : 0 < moveTicks) (hct : 0 < crossTicks)
    (hc : crossing ≠ 0) (hcf : crossFactor ≠ 0)
    (hCurrent : ∀ l r : ℝ, shiftedOutflow θ g a l r - l =
      visit w (fixedCenter w l r) r - fixedCenter w l r) :
    let crossRate := crossFactor * (crossing / (crossTicks * tick))
    (directFactor * (direct / (directTicks * tick))) / crossRate =
      (directFactor / crossFactor) * ((Real.pi / 2) / crossing) * (crossTicks / directTicks) ∧
    (moveFactor * (θ / (moveTicks * tick))) / crossRate =
      (moveFactor / crossFactor) * (Real.arcsin (Real.sqrt (w / (2 - w))) / crossing) *
        (crossTicks / moveTicks) := by
  have hw := (shifted_weight_iff_alternating_current θ g a hw₀ hw₁).mp hCurrent
  rw [classPulse_weight] at hw
  have hmove := principal_transfer_area hθ hprincipal hw
  have hdirect : direct = Real.pi / 2 := by
    simpa using principal_transfer_area hd hdp hcertain
  rw [hdirect, hmove]
  exact ⟨common_tick_rate_ratio _ _ _ _ _ _ _ ht hdt hct hc hcf,
    common_tick_rate_ratio _ _ _ _ _ _ _ ht hmt hct hc hcf⟩

/-! ## Isolated sequential exchange on a matched carrier lane -/

-- Ports 0, 1 and 2 are entry live, intermediate record and exit live.
private def entry (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Real.cos θ, Complex.I * (Real.sin θ : ℂ), 0;
     Complex.I * (Real.sin θ : ℂ), Real.cos θ, 0; 0, 0, 1]

private def exit (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, Real.cos θ, Complex.I * (Real.sin θ : ℂ);
     0, Complex.I * (Real.sin θ : ℂ), Real.cos θ]

/-- A single pass through the two adjacent exchange operators, with
port 2 designated as the live exit on the shifted lane. -/
def stagedPulse (θ φ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ := exit φ * entry θ

private theorem entry_unitary (θ : ℝ) : entry θ ∈ unitary _ := by
  rw [Unitary.mem_iff]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [entry, star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im, -Complex.ofReal_sin, -Complex.ofReal_cos] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem exit_unitary (θ : ℝ) : exit θ ∈ unitary _ := by
  let e := (finRotate 3).symm
  have he : exit θ = (entry θ).submatrix e e := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h := entry_unitary θ
  have h₁ : (entry θ)ᴴ * entry θ = 1 := h.1
  have h₂ : entry θ * (entry θ)ᴴ = 1 := h.2
  rw [he, Unitary.mem_iff]
  simp only [star_eq_conjTranspose, conjTranspose_submatrix, submatrix_mul_equiv, h₁, h₂,
    submatrix_one_equiv, and_self]

theorem stagedPulse_unitary (θ φ : ℝ) : stagedPulse θ φ ∈ unitary _ :=
  mul_mem (exit_unitary φ) (entry_unitary θ)

/-- A signed lane injected at entry reaches the live exit via the
intermediate record port, with the product of the two exchange phases. -/
theorem stagedPulse_amplitude (θ φ : ℝ) :
    stagedPulse θ φ 2 0 = -((Real.sin θ * Real.sin φ : ℝ) : ℂ) := by
  simp [stagedPulse, entry, exit, mul_apply, Fin.sum_univ_three, Complex.ofReal_mul, -Complex.ofReal_sin]
  rw [show Complex.I * (Real.sin φ : ℂ) * (Complex.I * (Real.sin θ : ℂ)) =
      (Complex.I * Complex.I) * (Real.sin θ : ℂ) * (Real.sin φ : ℂ) by ring,
    Complex.I_mul_I]
  ring

/-- The resulting weight is the product of the two exchanged weights. -/
theorem stagedPulse_weight (θ φ : ℝ) :
    Complex.normSq (stagedPulse θ φ 2 0) = Real.sin θ ^ 2 * Real.sin φ ^ 2 := by
  rw [stagedPulse_amplitude, Complex.normSq_neg, Complex.normSq_ofReal]
  ring

/-- If each local pulse has geometric weight on its unexchanged through
port, the selected exchange-exchange exit reads the complementary
weights. The steady series coefficient differs from this single pass. -/
theorem staged_geometric_weight (θ φ : ℝ)
    (hθ : Real.cos θ ^ 2 = α) (hφ : Real.cos φ ^ 2 = α) :
    Complex.normSq (stagedPulse θ φ 2 0) = (1 - α) ^ 2 ∧
      α / 2 < Complex.normSq (stagedPulse θ φ 2 0) := by
  have hsθ : Real.sin θ ^ 2 = 1 - α := by linarith [Real.sin_sq_add_cos_sq θ]
  have hsφ : Real.sin φ ^ 2 = 1 - α := by linarith [Real.sin_sq_add_cos_sq φ]
  rw [stagedPulse_weight, hsθ, hsφ, ← pow_two]
  have hα : α < 1 / 4 := by linarith [PMConstants.CertifiedConstants.alpha_bounds.2]
  exact ⟨rfl, by nlinarith [sq_nonneg α]⟩

/-- The ordered geometric exchange pair cannot realize the same output
weight as a single shifted pulse matched to the steady series current. -/
theorem shifted_steady_ne_staged (ψ θ φ : ℝ) (g : Fin 3) (a : Fin 8)
    (hCurrent : ∀ l r : ℝ, shiftedOutflow ψ g a l r - l = α * (r - center α α r l))
    (hθ : Real.cos θ ^ 2 = α) (hφ : Real.cos φ ^ 2 = α) :
    Complex.normSq (classPulse ψ (.inr (g + 1, a)) (.inl (g, a))) <
      Complex.normSq (stagedPulse θ φ 2 0) := by
  rw [(shifted_weight_iff_steady_current ψ g a).mp hCurrent]
  exact (staged_geometric_weight θ φ hθ hφ).2

end PMElementaryParticles.RestoringPulseCalibration
