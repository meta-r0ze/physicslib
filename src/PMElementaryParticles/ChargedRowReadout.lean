import PMAction.WallRestChirality
import PMElementaryParticles.MassiveWidth

/-!
# Charged density readout on normalized two-wall modes

The current retains the negative-chirality sector of a two-wall parent.
The daughter sum measures the squared projection onto selected orthonormal
modes. On a window consisting of complete nonzero-energy chiral pairs, the
unweighted sum over both signs is twice the sum over positive energies.
-/

noncomputable section
namespace PMElementaryParticles.ChargedRowReadout
open Matrix PMAction.WallRestChirality

export PMAction.WallRestChirality
  (weight WallMode positivePart chargedPart chargedPart_is_native_density charged_weight_half
    weight_isometry)

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]

/-- The squared inclusive density amplitude to the chosen daughter columns is the
squared norm after orthogonal projection onto their span. -/
theorem daughter_sum_eq_projection (U : Matrix a b ℂ) (hU : Uᴴ * U = 1) (x : a → ℂ) :
    weight (Uᴴ *ᵥ x) = weight ((U * Uᴴ) *ᵥ x) := by
  rw [← mulVec_mulVec, weight_isometry U hU]

/-- Density amplitude from a charged source to a daughter wall mode. -/
def densityAmplitude {n : Type*} [Fintype n] (ψ : WallMode n) (x : n ⊕ n → ℂ) : ℂ :=
  star (chargedPart ψ) ⬝ᵥ x

/-- A chiral partner only changes the sign of the charged-density amplitude. -/
theorem densityAmplitude_chiralityFlip {n : Type*} [Fintype n]
    (ψ : WallMode n) (x : n ⊕ n → ℂ) :
    densityAmplitude (chiralityFlip ψ) x = -densityAmplitude ψ x := by
  rw [densityAmplitude, chargedPart_chiralityFlip, star_neg, neg_dotProduct, densityAmplitude]

/-- A supplied window of complete nonzero-energy pairs has twice the unweighted
density strength of its positive-energy half. The paired modes at opposite energy
are given by `PMAction.WallRestChirality.opposite_energy`. -/
theorem paired_window_strength {n ι : Type*} [Fintype n] [Fintype ι]
    (u : ι → WallMode n) (x : n ⊕ n → ℂ) :
    (∑ i, (Complex.normSq (densityAmplitude (u i) x) +
      Complex.normSq (densityAmplitude (chiralityFlip (u i)) x))) =
      2 * (∑ i, Complex.normSq (densityAmplitude (u i) x)) := by
  simp_rw [densityAmplitude_chiralityFlip, Complex.normSq_neg, ← two_mul]
  rw [Finset.mul_sum]

variable {n d : Type*} [Fintype n] [Fintype d] [DecidableEq d] [DecidableEq n]

/-- For unit-normalized nonzero rest modes, the unweighted inclusive density strength
is one half of the fraction of the charged density retained by the daughter projector.
The generation rotation `R` acts isometrically within the retained chirality. -/
theorem density_strength_eq_half_fraction
    {Y D₁ D₂ : Matrix n n ℂ} {ψ : WallMode n} {E : ℝ}
    (hE : E ≠ 0) (hψ : weight ψ = 1)
    (h : PMAction.ExactZeroMode.H Y D₁ D₂ *ᵥ ψ = (E : ℂ) • ψ)
    (R : Matrix (n ⊕ n) (n ⊕ n) ℂ) (hR : Rᴴ * R = 1)
    (U : Matrix ((n ⊕ n) ⊕ (n ⊕ n)) d ℂ) (hU : Uᴴ * U = 1) :
    let x : WallMode n := Sum.elim 0 (R *ᵥ chargedPart ψ)
    weight (Uᴴ *ᵥ x) = (1 / 2) * (weight ((U * Uᴴ) *ᵥ x) / weight x) := by
  dsimp only
  have hx : weight (Sum.elim 0 (R *ᵥ chargedPart ψ) : WallMode n) = 1 / 2 := by
    have hpad : weight (Sum.elim 0 (R *ᵥ chargedPart ψ) : WallMode n) =
        weight (R *ᵥ chargedPart ψ) := by
      simp [weight, Fintype.sum_sum_type]
    rw [hpad, weight_isometry R hR, charged_weight_half hE hψ h]
  rw [daughter_sum_eq_projection U hU, hx]
  ring

/-- Contact-width weight for a daughter of mass `μ` and two massless
spectators. Closed channels contribute zero. This is the integrated
`MassiveWidth` kernel under those kinematic assumptions. -/
def contactWeight (G m μ : ℝ) : ℝ :=
  if μ < m then MassiveDaughterSpectrum.width G m μ else 0

/-- In the factorized contact model a channel is strictly positive exactly
when it is open and its scalar transition amplitude is nonzero. -/
theorem contact_channel_pos_iff {G m μ : ℝ} (hG : G ≠ 0) (hμ : 0 ≤ μ) (a : ℂ) :
    0 < contactWeight G m μ * Complex.normSq a ↔ μ < m ∧ a ≠ 0 := by
  by_cases h : μ < m
  · rw [contactWeight, ite_eq_left h, mul_pos_iff_of_pos_left
      (MassiveDaughterSpectrum.width_positive G m μ hG hμ h), Complex.normSq_pos]
    simp [h]
  · simp [contactWeight, h]

/-- The open channel's weight is the integrated massive-daughter phase factor. -/
theorem contactWeight_open (G m μ : ℝ) (hμ : 0 ≤ μ) (h : μ < m) :
    contactWeight G m μ =
      G ^ 2 * m ^ 5 / (192 * Real.pi ^ 3) * MassiveWidth.phase ((μ / m) ^ 2) := by
  rw [contactWeight, ite_eq_left h, MassiveWidth.closed_width G m μ (lt_of_le_of_lt hμ h) hμ h.le]

/-- Rate sum for supplied orthogonal channels with two massless spectators
and a scalar multiplier on each contact amplitude. -/
def contactStrength {ι : Type*} [Fintype ι] (G m : ℝ) (μ : ι → ℝ) (a : ι → ℂ) : ℝ :=
  ∑ i, contactWeight G m (μ i) * Complex.normSq (a i)

/-- A common amplitude factor scales every channel, even at unequal thresholds. -/
theorem contactStrength_scale {ι : Type*} [Fintype ι] (G m : ℝ)
    (μ : ι → ℝ) (a : ι → ℂ) (q : ℂ) :
    contactStrength G m μ (fun i => q * a i) = Complex.normSq q * contactStrength G m μ a := by
  simp only [contactStrength, Complex.normSq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PMElementaryParticles.ChargedRowReadout
