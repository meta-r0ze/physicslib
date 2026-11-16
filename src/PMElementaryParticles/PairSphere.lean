import PMElementaryParticles.PairShell
import PMElementaryParticles.PairTransport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The pair tensor over the shell is the transported isotropic average

The last link of the three-body factorization (PMElementaryParticles REVIEW, "Mathematical gap").
`PairShell.shell_integral` writes the two-leg measure at fixed total momentum `P⃗ = b e₀` against the
pair energy `E` with density `(sin ν/2)` in the rest-frame angles `(ν, φ)`; `PairTransport` uses an
isotropic average of the rest pair, boosted. Here the continuum solid-angle integral is computed.

* `separable`, `mono_avg`: the solid-angle moments of the rest pair, `∫ dΩ = 4π`, first moments
  zero, `∫ nᵢ nⱼ dΩ = (4π/3) δᵢⱼ`, from the iterated integrals over `(0, π] × (−π, π]`.
* `rest_covariant`: so the rest pair tensor integrates to `4π/12 g Q² + 4π/6 q q`
  (`PairIsotropy.rest_covariant` with volume `4π`, for the continuum rather than a finite rule).
* `transported`: the same for the pair boosted by any Lorentz `Λ`, with `q = Λ(Q, 0, 0, 0)`.
* `leg_spatial`, `shellBoost_legs`, `shellBoost_rest`: the shell legs `k = (|Ψ|, Ψ)`,
  `k̄ = (|P⃗ − Ψ|, P⃗ − Ψ)` are the rest pair of mass `M = √(E² − b²)` boosted along `e₀` to
  `q = (E, b, 0, 0)`.
* `shell_tensor`: so `∫ k^μ k̄^ν dΩ* = 4π/12 g (E² − b²) + 4π/6 q^μ q^ν` over the actual shell, and
  `shell_tensor_normalized`: with the reduced angular density `1/(32π²)` (`PolarMeasure`) this is
  `Φ/12 g q² + Φ/6 q q` with `Φ = 1/(8π)`, the transported average `PairTransport` and
  `MassiveDaughterSpectrum.pair_density` use. The pair average is computed, not assumed.
-/

noncomputable section
open MeasureTheory Set Real Matrix

namespace PMElementaryParticles.PairSphere
set_option linter.unnecessarySeqFocus false

/-- The angle rectangle `(0, π] × (−π, π]`. -/
def rect : Set (ℝ × ℝ) := Ioc 0 π ×ˢ Ioc (-π) π

/-- A separable integrand integrates to the product of its factors' integrals. -/
theorem separable (g h : ℝ → ℝ) :
    ∫ p in rect, g p.1 * h p.2 = (∫ x in (0)..π, g x) * ∫ y in (-π)..π, h y := by
  rw [rect, Measure.volume_eq_prod, setIntegral_prod_mul,
    intervalIntegral.integral_of_le pi_pos.le,
    intervalIntegral.integral_of_le (by linarith [pi_pos])]

lemma nu_sin : ∫ x in (0)..π, sin x = 2 := by simp [integral_sin]; norm_num

lemma nu_cos_sin : ∫ x in (0)..π, cos x * sin x = 0 := by
  have : ∀ x ∈ uIcc 0 π, HasDerivAt (fun x => sin x ^ 2 / 2) (cos x * sin x) x := by
    intro x _
    have := (hasDerivAt_sin x).pow 2
    convert this.div_const 2 using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

lemma nu_cos_sq_sin : ∫ x in (0)..π, cos x ^ 2 * sin x = 2 / 3 := by
  have : ∀ x ∈ uIcc 0 π, HasDerivAt (fun x => -(cos x ^ 3) / 3) (cos x ^ 2 * sin x) x := by
    intro x _
    have := ((hasDerivAt_cos x).pow 3).neg.div_const 3
    convert this using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp; norm_num

lemma nu_sin_cube : ∫ x in (0)..π, sin x ^ 3 = 4 / 3 := by
  have : ∀ x ∈ uIcc 0 π, HasDerivAt (fun x => -cos x + cos x ^ 3 / 3) (sin x ^ 3) x := by
    intro x _
    have := (hasDerivAt_cos x).neg.add (((hasDerivAt_cos x).pow 3).div_const 3)
    convert this using 1
    have h := sin_sq_add_cos_sq x
    simp only [neg_neg]
    push_cast
    linear_combination (sin x) * h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp; norm_num

lemma phi_one : ∫ _ in (-π)..π, (1 : ℝ) = 2 * π := by simp; ring
lemma phi_cos : ∫ y in (-π)..π, cos y = 0 := by simp [integral_cos]
lemma phi_sin : ∫ y in (-π)..π, sin y = 0 := by simp [integral_sin]
lemma phi_cos_sq : ∫ y in (-π)..π, cos y ^ 2 = π := by
  rw [integral_cos_sq]; simp
lemma phi_sin_sq : ∫ y in (-π)..π, sin y ^ 2 = π := by
  rw [integral_sin_sq]; simp
lemma phi_cos_sin : ∫ y in (-π)..π, cos y * sin y = 0 := by
  have : ∀ x ∈ uIcc (-π) π, HasDerivAt (fun x => sin x ^ 2 / 2) (cos x * sin x) x := by
    intro x _
    have := (hasDerivAt_sin x).pow 2
    convert this.div_const 2 using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp


/-! ## The rest-frame sphere average -/

/-- The unit direction with polar angles `(ν, φ)` about `e₀` (`PairShell.restLeg`). -/
def dir (p : ℝ × ℝ) : Fin 3 → ℝ := ![cos p.1, sin p.1 * cos p.2, sin p.1 * sin p.2]

/-- The solid-angle integral `∫ f dΩ = ∫∫ f sin ν dν dφ`. -/
def sphereAvg (f : ℝ × ℝ → ℝ) : ℝ := ∫ p in rect, f p * sin p.1

lemma sep_eq {F : ℝ × ℝ → ℝ} (g h : ℝ → ℝ) (hF : ∀ p, F p = g p.1 * h p.2) :
    ∫ p in rect, F p = (∫ x in (0)..π, g x) * ∫ y in (-π)..π, h y := by
  rw [show F = fun p => g p.1 * h p.2 from funext hF]; exact separable g h

/-- Rest-frame legs of a massless pair of mass `Q`, back to back along `dir p`. -/
def leftRest (Q : ℝ) (p : ℝ × ℝ) : Fin 4 → ℝ :=
  ![Q / 2, Q / 2 * dir p 0, Q / 2 * dir p 1, Q / 2 * dir p 2]
def rightRest (Q : ℝ) (p : ℝ × ℝ) : Fin 4 → ℝ :=
  ![Q / 2, -Q / 2 * dir p 0, -Q / 2 * dir p 1, -Q / 2 * dir p 2]

-- Pointwise rewriting of a monomial integrand into separable form.
set_option hygiene false in
macro "sep_tac" : tactic =>
  `(tactic| first
    | (simp only [mono, dir, Matrix.cons_val, Fin.isValue]; ring)
    | (simp only [mono, dir, Matrix.cons_val, Fin.isValue])
    | (simp [mono, dir]; ring))

/-- The monomials of the rest pair tensor. -/
def mono (μ ν : Fin 4) (p : ℝ × ℝ) : ℝ :=
  (![1, dir p 0, dir p 1, dir p 2] : Fin 4 → ℝ) μ * (![1, -dir p 0, -dir p 1, -dir p 2] : Fin 4 → ℝ) ν

lemma rest_mono (Q : ℝ) (p : ℝ × ℝ) (μ ν : Fin 4) :
    leftRest Q p μ * rightRest Q p ν = Q ^ 2 / 4 * mono μ ν p := by
  fin_cases μ <;> fin_cases ν <;> simp [leftRest, rightRest, mono] <;> ring

/-- **The solid-angle moments of the rest pair**: `4π` on `(0,0)`, `−4π/3` on the spatial diagonal,
zero elsewhere. -/
theorem mono_avg (μ ν : Fin 4) :
    sphereAvg (mono μ ν) = 4 * π * (if μ = ν then (if μ = 0 then 1 else -1/3) else 0) := by
  unfold sphereAvg
  fin_cases μ <;> fin_cases ν <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    ite_true, ite_false, Fin.reduceEq, mul_zero]
  · rw [sep_eq sin (fun _ => 1) (fun p => by sep_tac), nu_sin, phi_one]; ring
  · rw [sep_eq (fun x => cos x * sin x) (fun _ => -1) (fun p => by sep_tac),
      nu_cos_sin, zero_mul]
  · rw [sep_eq (fun x => -(sin x ^ 2)) cos (fun p => by sep_tac), phi_cos, mul_zero]
  · rw [sep_eq (fun x => -(sin x ^ 2)) sin (fun p => by sep_tac), phi_sin, mul_zero]
  · rw [sep_eq (fun x => cos x * sin x) (fun _ => 1) (fun p => by sep_tac),
      nu_cos_sin, zero_mul]
  · rw [sep_eq (fun x => cos x ^ 2 * sin x) (fun _ => -1) (fun p => by sep_tac),
      nu_cos_sq_sin]; norm_num; ring
  · rw [sep_eq (fun x => -(cos x * sin x ^ 2)) cos (fun p => by sep_tac), phi_cos,
      mul_zero]
  · rw [sep_eq (fun x => -(cos x * sin x ^ 2)) sin (fun p => by sep_tac), phi_sin,
      mul_zero]
  · rw [sep_eq (fun x => sin x ^ 2) cos (fun p => by sep_tac), phi_cos, mul_zero]
  · rw [sep_eq (fun x => -(cos x * sin x ^ 2)) cos (fun p => by sep_tac), phi_cos,
      mul_zero]
  · rw [sep_eq (fun x => -(sin x ^ 3)) (fun y => cos y ^ 2) (fun p => by sep_tac),
      phi_cos_sq, intervalIntegral.integral_neg, nu_sin_cube]; ring
  · rw [sep_eq (fun x => -(sin x ^ 3)) (fun y => cos y * sin y) (fun p => by sep_tac),
      phi_cos_sin, mul_zero]
  · rw [sep_eq (fun x => sin x ^ 2) sin (fun p => by sep_tac), phi_sin, mul_zero]
  · rw [sep_eq (fun x => -(cos x * sin x ^ 2)) sin (fun p => by sep_tac), phi_sin,
      mul_zero]
  · rw [sep_eq (fun x => -(sin x ^ 3)) (fun y => cos y * sin y) (fun p => by sep_tac),
      phi_cos_sin, mul_zero]
  · rw [sep_eq (fun x => -(sin x ^ 3)) (fun y => sin y ^ 2) (fun p => by sep_tac),
      phi_sin_sq, intervalIntegral.integral_neg, nu_sin_cube]; ring

lemma sphereAvg_const_mul (c : ℝ) (f : ℝ × ℝ → ℝ) :
    sphereAvg (fun p => c * f p) = c * sphereAvg f := by
  unfold sphereAvg
  simp_rw [mul_assoc]
  exact integral_const_mul c _

open PairIsotropy.AngularAverage in
/-- **The rest-frame pair tensor of the solid-angle integral**, with volume `4π`. -/
theorem rest_covariant (Q : ℝ) (μ ν : Fin 4) :
    sphereAvg (fun p => leftRest Q p μ * rightRest Q p ν) =
      4 * π / 12 * metric μ ν * Q ^ 2 + 4 * π / 6 * restMomentum Q μ * restMomentum Q ν := by
  simp_rw [rest_mono]
  rw [sphereAvg_const_mul, mono_avg]
  fin_cases μ <;> fin_cases ν <;> norm_num [metric, restMomentum, Matrix.diagonal] <;> ring


/-! ## Transport to any frame -/

lemma integrableOn_rect {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f rect :=
  (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma cont_rest (Q : ℝ) (α β : Fin 4) :
    Continuous fun p : ℝ × ℝ => leftRest Q p α * rightRest Q p β * sin p.1 := by
  fin_cases α <;> fin_cases β <;> simp [leftRest, rightRest, dir] <;> fun_prop

open PairIsotropy.AngularAverage PairTransport in
/-- **The solid-angle integral of the boosted pair tensor** is `4π/12 g Q² + 4π/6 q q` with
`q = Λ(Q, 0, 0, 0)`, for every Lorentz `Λ`: `PairTransport.transported_tensor` with the continuum
solid angle in place of a finite rule. -/
theorem transported {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : IsLorentz Λ) (Q : ℝ) (μ ν : Fin 4) :
    sphereAvg (fun p => (Λ *ᵥ leftRest Q p) μ * (Λ *ᵥ rightRest Q p) ν) =
      4 * π / 12 * metric μ ν * Q ^ 2 +
        4 * π / 6 * (Λ *ᵥ restMomentum Q) μ * (Λ *ᵥ restMomentum Q) ν := by
  have hexp : (fun p : ℝ × ℝ => (Λ *ᵥ leftRest Q p) μ * (Λ *ᵥ rightRest Q p) ν * sin p.1) =
      fun p => ∑ α, ∑ β, (Λ μ α * Λ ν β) * (leftRest Q p α * rightRest Q p β * sin p.1) := by
    funext p
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun β _ => by ring
  have hint : ∀ α β, Integrable (fun p : ℝ × ℝ =>
      (Λ μ α * Λ ν β) * (leftRest Q p α * rightRest Q p β * sin p.1)) (volume.restrict rect) :=
    fun α β => integrableOn_rect (continuous_const.mul (cont_rest Q α β))
  have hrest : ∀ α β, ∫ p in rect, leftRest Q p α * rightRest Q p β * sin p.1 =
      4 * π / 12 * metric α β * Q ^ 2 + 4 * π / 6 * restMomentum Q α * restMomentum Q β :=
    fun α β => rest_covariant Q α β
  unfold sphereAvg
  rw [hexp, integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hint α β))]
  have hin : ∀ α, ∫ p in rect, ∑ β, (Λ μ α * Λ ν β) * (leftRest Q p α * rightRest Q p β * sin p.1) =
      ∑ β, (Λ μ α * Λ ν β) * (4 * π / 12 * metric α β * Q ^ 2 +
        4 * π / 6 * restMomentum Q α * restMomentum Q β) := by
    intro α
    rw [integral_finsetSum _ (fun β _ => hint α β)]
    exact Finset.sum_congr rfl fun β _ => by rw [integral_const_mul, hrest]
  simp_rw [hin]
  have hg := congrFun (congrFun (lorentz_transpose h) μ) ν
  rw [← hg]
  simp [Matrix.mul_apply, Fin.sum_univ_four, metric, restMomentum, Matrix.mulVec, dotProduct]
  ring

/-! ## The shell legs are the boosted rest pair -/

/-- The pair's four-momentum, total energy `E` and momentum `b e₀`. -/
def q (b E : ℝ) : Fin 4 → ℝ := ![E, b, 0, 0]

/-- The shell's two legs as four-vectors (`PairShell.Ψ`, `PairShell.nrm_Ψ`, `nrm_Ψ_bar`). -/
def leg (b E : ℝ) (p : ℝ × ℝ) : Fin 4 → ℝ :=
  ![(E + b * cos p.1) / 2, (b + E * cos p.1) / 2, PairShell.Mb b E / 2 * sin p.1 * cos p.2,
    PairShell.Mb b E / 2 * sin p.1 * sin p.2]
def legBar (b E : ℝ) (p : ℝ × ℝ) : Fin 4 → ℝ :=
  ![(E - b * cos p.1) / 2, (b - E * cos p.1) / 2, -(PairShell.Mb b E / 2 * sin p.1 * cos p.2),
    -(PairShell.Mb b E / 2 * sin p.1 * sin p.2)]

/-- The leg's spatial part is the shell point `Ψ(E, ν, φ)`, and the partner's is `P⃗ − Ψ`. -/
theorem leg_spatial (b E : ℝ) (p : ℝ × ℝ) :
    (fun i : Fin 3 => leg b E p i.succ) = PairShell.Ψ b ![E, p.1, p.2] ∧
      (fun i : Fin 3 => legBar b E p i.succ) = PairShell.P b - PairShell.Ψ b ![E, p.1, p.2] := by
  constructor <;> funext i <;> fin_cases i <;> simp [leg, legBar, PairShell.Ψ, PairShell.P] <;> ring

/-- The boost along `e₀` taking `(M, 0, 0, 0)` to `(E, b, 0, 0)`. -/
def shellBoost (b E : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  PairTransport.boost ![E / PairShell.Mb b E, b / PairShell.Mb b E, 0, 0]
    (PairShell.Mb b E / (PairShell.Mb b E + E))

theorem shellBoost_lorentz {b E : ℝ} (hb : 0 < b) (hE : b < E) :
    PairTransport.IsLorentz (shellBoost b E) := by
  have hM := PairShell.Mb_pos hb hE
  have hM2 := PairShell.Mb_sq hE.le hb.le
  apply PairTransport.boost_lorentz
  · simp; field_simp; linear_combination -hM2
  · have hME : PairShell.Mb b E + E ≠ 0 := by linarith
    have hM0 : PairShell.Mb b E ≠ 0 := hM.ne'
    simp only [Matrix.cons_val_zero]
    field_simp

theorem shellBoost_legs {b E : ℝ} (hb : 0 < b) (hE : b < E) (p : ℝ × ℝ) :
    shellBoost b E *ᵥ leftRest (PairShell.Mb b E) p = leg b E p ∧
      shellBoost b E *ᵥ rightRest (PairShell.Mb b E) p = legBar b E p := by
  have hM := PairShell.Mb_pos hb hE
  have hM2 := PairShell.Mb_sq hE.le hb.le
  have hME : PairShell.Mb b E + E ≠ 0 := by linarith
  constructor <;> funext i <;> fin_cases i <;>
    simp [shellBoost, PairTransport.boost, leftRest, rightRest, leg, legBar, dir, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four] <;> field_simp <;>
    first | ring1 | linear_combination (cos p.1) * hM2 | linear_combination (-cos p.1) * hM2

theorem shellBoost_rest {b E : ℝ} (hb : 0 < b) (hE : b < E) :
    shellBoost b E *ᵥ PairIsotropy.AngularAverage.restMomentum (PairShell.Mb b E) = q b E := by
  have hM := PairShell.Mb_pos hb hE
  funext i; fin_cases i <;>
    simp [shellBoost, PairTransport.boost, PairIsotropy.AngularAverage.restMomentum, q,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> field_simp

open PairIsotropy.AngularAverage in
/-- **The pair tensor over the shell at fixed `E`**: the solid-angle integral of `k^μ k̄^ν` over the
actual shell legs is `4π/12 g (E² − b²) + 4π/6 q q`, `q = (E, b, 0, 0)`. This is
`PairTransport.transported_tensor` with `Φ = 4π` times the measure's constant, now computed rather
than assumed. -/
theorem shell_tensor {b E : ℝ} (hb : 0 < b) (hE : b < E) (μ ν : Fin 4) :
    sphereAvg (fun p => leg b E p μ * legBar b E p ν) =
      4 * π / 12 * metric μ ν * (E ^ 2 - b ^ 2) + 4 * π / 6 * q b E μ * q b E ν := by
  have h := transported (shellBoost_lorentz hb hE) (PairShell.Mb b E) μ ν
  rw [shellBoost_rest hb hE, PairShell.Mb_sq hE.le hb.le] at h
  rw [← h]
  congr 1; funext p
  rw [(shellBoost_legs hb hE p).1, (shellBoost_legs hb hE p).2]

open PairIsotropy.AngularAverage in
/-- **With the reduced angular density `1/(32π²)`**: `Φ/12 g q² + Φ/6 q q`, `Φ = 1/(8π)`. -/
theorem shell_tensor_normalized {b E : ℝ} (hb : 0 < b) (hE : b < E) (μ ν : Fin 4) :
    1 / (32 * π ^ 2) * sphereAvg (fun p => leg b E p μ * legBar b E p ν) =
      1 / (8 * π) / 12 * metric μ ν * (E ^ 2 - b ^ 2) + 1 / (8 * π) / 6 * q b E μ * q b E ν := by
  rw [shell_tensor hb hE]
  have : π ≠ 0 := pi_pos.ne'
  field_simp
  ring

end PMElementaryParticles.PairSphere
