import PMElementaryParticles.PairIsotropy

/-!
# A massive pair in its rest frame (review item A4, the tensor part)

`PairIsotropy.rest_tensor` gives the rest-frame pair tensor for a massless pair. Here the two members
have masses `m₁`, `m₂`: energies `E₁`, `E₂` and a common momentum `P` along opposite directions.

* `massive_rest_tensor`: from the same angular symmetries and unit length, the average of
  `k₁^μ k₂^ν` (momenta `P₁`, `P₂` along the sampled direction) is `Φ E₁ E₂` for `μ = ν = 0`,
  `Φ P₁ P₂/3` for `μ = ν` spatial, and `0` otherwise; opposite momenta are `P₂ = −P₁`.
* `massive_rest_covariant`: with `Q = E₁ + E₂` and `q = (Q, 0, 0, 0)`,
  `Q² ⟨k₁^μ k₂^ν⟩ = Φ (P²/3) g^{μν} Q² + Φ (E₁E₂ − P²/3) q^μ q^ν` (no division by `Q`).
* `massless_limit`: at `m₁ = m₂ = 0`, `E₁ = E₂ = P = Q/2`, the coefficients are `Q²/12` and `Q²/6`:
  `rest_covariant`'s.
* `two_body_kinematics`: with `E₁ = (Q² + m₁² − m₂²)/(2Q)`, `E₂ = (Q² − m₁² + m₂²)/(2Q)` and
  `P² = E₁² − m₁²`, the members are on their shells (`E₂² − P² = m₂²`) and `E₁ + E₂ = Q`.
* `shells`: the two momenta have invariant masses `E₁² − P²` and `E₂² − P²`.

Open (A4, remaining): the two-body volume with masses (`2P/Q` times the massless one is the standard
reduction; it is a measure statement, as `A.volume` is here) and the daughter-energy integral of
`MassiveDaughterSpectrum`/`MassiveWidth` with this tensor.
-/

noncomputable section
namespace PMElementaryParticles.MassivePair
open PMElementaryParticles.PairIsotropy PMElementaryParticles.PairIsotropy.AngularAverage

variable {Ω : Type*} (A : AngularAverage Ω)

/-- First member: energy `E₁`, momentum `P` along the sampled direction. -/
def left (E₁ P : ℝ) (ω : Ω) : Fin 4 → ℝ :=
  ![E₁, P * A.direction 0 ω, P * A.direction 1 ω, P * A.direction 2 ω]

/-- Second member: energy `E₂`, momentum `P₂` along the sampled direction (opposite to the first
member for `P₂ = −P`). -/
def right (E₂ P₂ : ℝ) (ω : Ω) : Fin 4 → ℝ :=
  ![E₂, P₂ * A.direction 0 ω, P₂ * A.direction 1 ω, P₂ * A.direction 2 ω]

theorem massive_rest_tensor (E₁ E₂ P₁ P₂ : ℝ) (μ ν : Fin 4) :
    A.average (fun ω => left A E₁ P₁ ω μ * right A E₂ P₂ ω ν) =
      if μ = 0 ∧ ν = 0 then A.volume * (E₁ * E₂)
      else if μ = ν then A.volume * (P₁ * P₂) / 3 else 0 := by
  have hc (c : ℝ) (f : Ω → ℝ) :
      A.average (fun ω => c * f ω) = c * A.average f := A.average.map_smul c f
  have hconst (c : ℝ) : A.average (fun _ => c) = c * A.volume := by
    simpa only [mul_one, volume] using hc c (fun _ => 1)
  have hl (c : ℝ) (i : Fin 3) :
      A.average (fun ω => c * A.direction i ω) = 0 := by
    rw [hc, A.first_moment, mul_zero]
  have hp (c : ℝ) (i j : Fin 3) :
      A.average (fun ω => c * (A.direction i ω * A.direction j ω)) =
        c * (if i = j then A.volume / 3 else 0) := by
    rw [hc, A.second_moment]
  have hll (a b : ℝ) (i j : Fin 3) :
      A.average (fun ω => (a * A.direction i ω) * (b * A.direction j ω)) =
        (a*b) * (if i = j then A.volume / 3 else 0) := by
    calc
      _ = A.average (fun ω => (a*b) * (A.direction i ω * A.direction j ω)) := by
        congr 1; funext ω; ring
      _ = _ := hp (a*b) i j
  have hcl (a b : ℝ) (i : Fin 3) :
      A.average (fun ω => a * (b * A.direction i ω)) = 0 := by
    simpa only [← mul_assoc] using hl (a*b) i
  have hlc (a b : ℝ) (i : Fin 3) :
      A.average (fun ω => (a * A.direction i ω) * b) = 0 := by
    calc
      _ = A.average (fun ω => (a*b) * A.direction i ω) := by
        congr 1; funext ω; ring
      _ = 0 := hl (a*b) i
  fin_cases μ <;> fin_cases ν <;>
    simp [left, right, hconst, hcl, hlc, hll] <;> ring

theorem massive_rest_covariant (E₁ E₂ P : ℝ) (μ ν : Fin 4) :
    (E₁ + E₂) ^ 2 * A.average (fun ω => left A E₁ P ω μ * right A E₂ (-P) ω ν) =
      A.volume * (P ^ 2 / 3) * metric μ ν * (E₁ + E₂) ^ 2 +
        A.volume * (E₁ * E₂ - P ^ 2 / 3) * restMomentum (E₁ + E₂) μ * restMomentum (E₁ + E₂) ν := by
  rw [massive_rest_tensor]
  fin_cases μ <;> fin_cases ν <;> norm_num [metric, restMomentum, Matrix.diagonal] <;> ring

/-- **Massless limit**: the coefficients reduce to `rest_covariant`'s `Q²/12` and `Q²/6`. -/
theorem massless_limit (Q : ℝ) :
    (Q / 2) ^ 2 / 3 = Q ^ 2 / 12 ∧ Q / 2 * (Q / 2) - (Q / 2) ^ 2 / 3 = Q ^ 2 / 6 := by
  constructor <;> ring

/-- **Two-body kinematics** in the pair rest frame. -/
theorem two_body_kinematics (Q m₁ m₂ P : ℝ) (hQ : Q ≠ 0)
    (hP : P ^ 2 = ((Q ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * Q)) ^ 2 - m₁ ^ 2) :
    ((Q ^ 2 - m₁ ^ 2 + m₂ ^ 2) / (2 * Q)) ^ 2 - P ^ 2 = m₂ ^ 2 ∧
      (Q ^ 2 + m₁ ^ 2 - m₂ ^ 2) / (2 * Q) + (Q ^ 2 - m₁ ^ 2 + m₂ ^ 2) / (2 * Q) = Q := by
  constructor
  · rw [hP]; field_simp; ring
  · field_simp; ring

/-- **Shells**: the members have invariant masses `E₁² − P²`, `E₂² − P²`. -/
theorem shells (E₁ E₂ P : ℝ) (ω : Ω) :
    MuonRate.mdot (left A E₁ P ω) (left A E₁ P ω) = E₁ ^ 2 - P ^ 2 ∧
    MuonRate.mdot (right A E₂ (-P) ω) (right A E₂ (-P) ω) = E₂ ^ 2 - P ^ 2 := by
  have hn := A.unit_length ω
  simp only [Fin.sum_univ_three] at hn
  constructor
  · have h : MuonRate.mdot (left A E₁ P ω) (left A E₁ P ω) =
        E₁ ^ 2 - P ^ 2 * (A.direction 0 ω ^ 2 + A.direction 1 ω ^ 2 + A.direction 2 ω ^ 2) := by
      simp [MuonRate.mdot, left]; ring
    rw [h, hn]; ring
  · have h : MuonRate.mdot (right A E₂ (-P) ω) (right A E₂ (-P) ω) =
        E₂ ^ 2 - P ^ 2 * (A.direction 0 ω ^ 2 + A.direction 1 ω ^ 2 + A.direction 2 ω ^ 2) := by
      simp [MuonRate.mdot, right]; ring
    rw [h, hn]; ring

end PMElementaryParticles.MassivePair
