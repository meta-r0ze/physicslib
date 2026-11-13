import PMAction.D4Isotropy
import PMAction.LoopMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The leading log on the D₄ substrate

`LoopMeasure` writes the one-loop running in units of `(α/4π)·ln(M²/μ²)`, the 4D measure of the
shell `μ < |k| < M` with the continuum kernel `1/k⁴`, and `ContactRunning` multiplies that unit by
Dirac and charge weights. This module derives both from the substrate's link geometry: the
self-energy's `½` from the D₄ direction average (no Feynman parameter), and the shell integral of
the substrate's own propagator, with an explicit bound on the cutoff's contribution.

**1. The self-energy's `½` is the D₄ direction average.** The charged leg's propagator
`(k + p)/|k + p|²` has, at first order in the external momentum `p`, the term
`p/|k|² − 2(k·p)k/|k|⁴` (`propagator_deriv`). Averaged over the 24 link roots, whose second
moment is `12 δ` (`D4Isotropy.second_moment`), `(k·p)k` averages to `¼|k|²p`, so the bracket is
`(1 − 2·¼) p/|k|² = ½ p/|k|²` (`half_weight`, `averaged_propagator`). With the vertex contraction
`−2` (`ContactRunning.contraction`) this is the self-energy weight `W = −1`
(`self_energy_weight`): the `½` is the same `¼` that `ContactRunning.loop_direction_average`
gives for the vertex, not a Feynman-parameter average.

**2. The substrate's propagator symbol.** The link Laplacian over the D₄ roots has symbol
`symbol a k = Σ_r (1 − cos(a r·k)) / (6a²)`; the second moment fixes the `6` so that its leading
term is exactly `|k|²`. The remainder is controlled by the quartic moment
`Σ_r (r·k)⁴ = 12|k|⁴` (`D4Isotropy.quartic_isotropic`) and `0 ≤ x²/2 − (1 − cos x) ≤ x⁴/24`
(`cos_gap`): `0 ≤ |k|² − symbol a k ≤ a²|k|⁴/12` (`symbol_gap`).

**3. The kernel.** Below `a²|k|² ≤ 6` the symbol is at least `|k|²/2` (`half_le_symbol`), and
`|1/symbol² − 1/|k|⁴| ≤ (2/3) a²/|k|²` (`kernel_gap`).

**4. The shell.** In 4D momentum space (`Mom`), radial functions integrate with the 3-sphere's
`2π² r³` (`shell_radial`, from Mathlib's polar formula and `LoopMeasure.volume_ball_eq`):
* `shell_log`: `∫_{μ<|k|<M} |k|⁻⁴ = 2π² ln(M/μ)`;
* `shell_lattice`: with the substrate's kernel the same integral is `2π² ln(M/μ)` up to
  `(2/3) a² π² (M² − μ²)`, for `a²M² ≤ 6`;
* `leading_log`: per `d⁴k/(2π)⁴`, the substrate shell is `ln(M/μ)/(8π²)` up to
  `a²(M² − μ²)/(24π²)`, which with `e² = 4πα` is `LoopMeasure.log_unit`'s `(α/4π)·ln(M²/μ²)`.

So the leading log is set by the window between the two scales; the cutoff enters only through
`(aM)²`, which the theorem bounds. That is the identification `ContactRunning` and `LoopMeasure`
left to the continuum.
-/

noncomputable section
namespace PMAction.LeadingLog
open Real MeasureTheory Metric Set D4Gauge

/-- Projection of a root on a momentum, `r·w`. -/
def rk (r : Fin 4 → Fin 3) (w : Fin 4 → ℝ) : ℝ := ∑ i, (vec r i : ℝ) * w i

/-- `|w|²`. -/
def sq4 (w : Fin 4 → ℝ) : ℝ := ∑ i, w i ^ 2

/-- A root as a real vector. -/
def rv (r : Fin 4 → Fin 3) : Fin 4 → ℝ := fun i => (vec r i : ℝ)

/-! ## 1. The direction average -/

lemma moment (μ ν : Fin 4) :
    ∑ r ∈ roots, (vec r μ : ℝ) * vec r ν = if μ = ν then 12 else 0 := by
  have h := D4Isotropy.second_moment μ ν
  split_ifs at h ⊢ <;> exact_mod_cast h

lemma diag_moment (μ : Fin 4) : ∑ r ∈ roots, (vec r μ : ℝ) ^ 2 = 12 := by
  simpa [sq] using moment μ μ

lemma norm_moment : ∑ r ∈ roots, ∑ i, (vec r i : ℝ) ^ 2 = 48 := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => diag_moment i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

lemma root_sq {r : Fin 4 → Fin 3} (hr : r ∈ roots) : sq4 (rv r) = 2 := by
  have h := (Finset.mem_filter.1 hr).2
  unfold dot at h
  have h' : ((∑ i, vec r i * vec r i : ℤ) : ℝ) = 2 := by exact_mod_cast h
  push_cast at h'
  simpa [sq4, rv, sq] using h'

lemma cross_moment (p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ r ∈ roots, rk r p * vec r μ = 12 * p μ := by
  calc ∑ r ∈ roots, rk r p * vec r μ
      = ∑ i, p i * ∑ r ∈ roots, (vec r i : ℝ) * vec r μ := by
        simp only [rk, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => by ring
    _ = 12 * p μ := by simp [moment]; ring

/-- **The propagator's first order in the external momentum.**
`d/dt (k + tp)_μ/|k + tp|² = p_μ/|k|² − 2(k·p)k_μ/|k|⁴` at `t = 0`. -/
theorem propagator_deriv (k p : Fin 4 → ℝ) (hk : sq4 k ≠ 0) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => (k μ + t * p μ) / sq4 (fun i => k i + t * p i))
      (p μ / sq4 k - 2 * (∑ i, k i * p i) * k μ / sq4 k ^ 2) 0 := by
  have hn : HasDerivAt (fun t : ℝ => k μ + t * p μ) (p μ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (p μ)).const_add (k μ)
  have hd : HasDerivAt (fun t : ℝ => sq4 (fun i => k i + t * p i)) (∑ i, 2 * k i * p i) 0 := by
    unfold sq4
    have := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (((hasDerivAt_id (0 : ℝ)).mul_const (p i)).const_add (k i)).pow 2
    simpa using this
  have hk' : (fun t : ℝ => sq4 (fun i => k i + t * p i)) 0 ≠ 0 := by simpa using hk
  convert hn.fun_div hd hk' using 1
  have hs : ∑ i, 2 * k i * p i = 2 * ∑ i, k i * p i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hk2 : sq4 (fun i => k i) ≠ 0 := hk
  simp only [zero_mul, add_zero, hs]
  field_simp

/-- **The `½`.** Over the D₄ roots, `Σ_r (|r|² p_μ − 2(r·p) r_μ) = ½ (Σ_r |r|²) p_μ`. -/
theorem half_weight (p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ r ∈ roots, ((∑ i, (vec r i : ℝ) ^ 2) * p μ - 2 * (rk r p * vec r μ)) =
      1 / 2 * (∑ r ∈ roots, ∑ i, (vec r i : ℝ) ^ 2) * p μ := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, cross_moment, norm_moment]
  ring

/-- The propagator's first-order term, summed over the root directions, is half the leading
term: `Σ_r (p_μ/|r|² − 2(r·p) r_μ/|r|⁴) = ½ Σ_r p_μ/|r|²`. -/
theorem averaged_propagator (p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ r ∈ roots, (p μ / sq4 (rv r) - 2 * rk r p * vec r μ / sq4 (rv r) ^ 2) =
      1 / 2 * ∑ r ∈ roots, p μ / sq4 (rv r) := by
  have e1 : ∀ r ∈ roots, p μ / sq4 (rv r) - 2 * rk r p * vec r μ / sq4 (rv r) ^ 2 =
      ((∑ i, (vec r i : ℝ) ^ 2) * p μ - 2 * (rk r p * vec r μ)) / 4 := fun r hr => by
    rw [show (∑ i, (vec r i : ℝ) ^ 2) = sq4 (rv r) from rfl, root_sq hr]; ring
  have e2 : ∀ r ∈ roots, p μ / sq4 (rv r) = p μ / 2 := fun r hr => by rw [root_sq hr]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_div, half_weight,
    norm_moment, Finset.sum_const, roots_card, nsmul_eq_mul]
  push_cast
  ring

/-- Each direction carries a quarter of `|r|²`: `Σ_r r_μ² / Σ_r |r|² = ¼`. -/
theorem direction_share (μ : Fin 4) :
    (∑ r ∈ roots, (vec r μ : ℝ) ^ 2) / ∑ r ∈ roots, ∑ i, (vec r i : ℝ) ^ 2 = 1 / 4 := by
  rw [norm_moment, diag_moment]; norm_num

/-- **The self-energy weight from the substrate.** The vertex contraction `−2` times the direction
average `1 − 2·¼ = ½`: `W = −1`. -/
theorem self_energy_weight (μ : Fin 4) :
    (-2 : ℝ) * (1 - 2 * ((∑ r ∈ roots, (vec r μ : ℝ) ^ 2) /
      ∑ r ∈ roots, ∑ i, (vec r i : ℝ) ^ 2)) = -1 := by
  rw [direction_share]; norm_num

/-! ## 2. The substrate's propagator symbol -/

/-- `0 ≤ x²/2 − (1 − cos x) ≤ x⁴/24`. -/
lemma cos_gap (x : ℝ) : 0 ≤ x ^ 2 / 2 - (1 - cos x) ∧ x ^ 2 / 2 - (1 - cos x) ≤ x ^ 4 / 24 := by
  refine ⟨by linarith [one_sub_sq_div_two_le_cos (x := x)], ?_⟩
  have hc : cos x = 1 - 2 * sin (x / 2) ^ 2 := by
    have h1 := cos_two_mul (x / 2)
    have h2 := sin_sq_add_cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h1
    linarith
  have e : x ^ 2 / 2 - (1 - cos x) = 2 * ((x / 2 - sin (x / 2)) * (x / 2 + sin (x / 2))) := by
    rw [hc]; ring
  have h1 := abs_sub_sin_le (x / 2)
  have h2 : |x / 2 + sin (x / 2)| ≤ 2 * |x / 2| := by
    have := abs_sin_le_abs (x := x / 2)
    calc |x / 2 + sin (x / 2)| ≤ |x / 2| + |sin (x / 2)| := abs_add_le _ _
      _ ≤ 2 * |x / 2| := by linarith
  have h3 : (x / 2 - sin (x / 2)) * (x / 2 + sin (x / 2)) ≤ |x / 2| ^ 3 / 6 * (2 * |x / 2|) := by
    calc _ ≤ |(x / 2 - sin (x / 2)) * (x / 2 + sin (x / 2))| := le_abs_self _
      _ = |x / 2 - sin (x / 2)| * |x / 2 + sin (x / 2)| := abs_mul _ _
      _ ≤ |x / 2| ^ 3 / 6 * (2 * |x / 2|) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have h4 : |x / 2| ^ 3 / 6 * (2 * |x / 2|) = x ^ 4 / 48 := by
    have : |x / 2| ^ 4 = (x / 2) ^ 4 := by
      rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    calc |x / 2| ^ 3 / 6 * (2 * |x / 2|) = |x / 2| ^ 4 / 3 := by ring
      _ = x ^ 4 / 48 := by rw [this]; ring
  rw [e]; nlinarith [sq_nonneg (x ^ 2)]

/-- The symbol of the link Laplacian over the D₄ roots at spacing `a`. -/
def symbol (a : ℝ) (w : Fin 4 → ℝ) : ℝ := (∑ r ∈ roots, (1 - cos (a * rk r w))) / (6 * a ^ 2)

lemma rk_sq_sum (w : Fin 4 → ℝ) : ∑ r ∈ roots, rk r w ^ 2 = 12 * sq4 w := by
  calc ∑ r ∈ roots, rk r w ^ 2 = ∑ μ, w μ * ∑ r ∈ roots, rk r w * vec r μ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [sq]; nth_rw 2 [rk]; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring
    _ = 12 * sq4 w := by
        simp only [cross_moment, sq4, Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring

lemma rk_four_sum (w : Fin 4 → ℝ) : ∑ r ∈ roots, rk r w ^ 4 = 12 * sq4 w ^ 2 :=
  D4Isotropy.quartic_isotropic w

/-- **The symbol's gap.** `0 ≤ |k|² − symbol a k ≤ a²|k|⁴/12`. -/
theorem symbol_gap {a : ℝ} (ha : 0 < a) (w : Fin 4 → ℝ) :
    0 ≤ sq4 w - symbol a w ∧ sq4 w - symbol a w ≤ a ^ 2 / 12 * sq4 w ^ 2 := by
  have ha2 : 0 < 6 * a ^ 2 := by positivity
  have hs : ∑ r ∈ roots, (a * rk r w) ^ 2 / 2 = 6 * a ^ 2 * sq4 w := by
    rw [← Finset.sum_div]
    simp only [mul_pow]
    rw [← Finset.mul_sum, rk_sq_sum]; ring
  have key : sq4 w - symbol a w =
      (∑ r ∈ roots, ((a * rk r w) ^ 2 / 2 - (1 - cos (a * rk r w)))) / (6 * a ^ 2) := by
    rw [Finset.sum_sub_distrib, hs, sub_div, mul_div_cancel_left₀ _ ha2.ne', symbol]
  rw [key]
  refine ⟨div_nonneg (Finset.sum_nonneg fun r _ => (cos_gap _).1) ha2.le, ?_⟩
  rw [div_le_iff₀ ha2]
  calc ∑ r ∈ roots, ((a * rk r w) ^ 2 / 2 - (1 - cos (a * rk r w)))
      ≤ ∑ r ∈ roots, (a * rk r w) ^ 4 / 24 := Finset.sum_le_sum fun r _ => (cos_gap _).2
    _ = a ^ 4 / 24 * ∑ r ∈ roots, rk r w ^ 4 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
    _ = a ^ 2 / 12 * sq4 w ^ 2 * (6 * a ^ 2) := by rw [rk_four_sum]; ring

theorem symbol_le {a : ℝ} (ha : 0 < a) (w : Fin 4 → ℝ) : symbol a w ≤ sq4 w := by
  linarith [(symbol_gap ha w).1]

/-! ## 3. The kernel -/

theorem half_le_symbol {a : ℝ} (ha : 0 < a) {w : Fin 4 → ℝ} (hw : a ^ 2 * sq4 w ≤ 6) :
    sq4 w / 2 ≤ symbol a w := by
  have h := (symbol_gap ha w).2
  have h0 : 0 ≤ sq4 w := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [mul_nonneg h0 (sub_nonneg.2 hw)]

/-- **The kernel's gap.** For `a²|k|² ≤ 6`, `|1/symbol² − 1/|k|⁴| ≤ (2/3) a²/|k|²`. -/
theorem kernel_gap {a : ℝ} (ha : 0 < a) {w : Fin 4 → ℝ} (hw0 : 0 < sq4 w)
    (hw : a ^ 2 * sq4 w ≤ 6) :
    |1 / symbol a w ^ 2 - 1 / sq4 w ^ 2| ≤ 2 / 3 * a ^ 2 / sq4 w := by
  have hs := half_le_symbol ha hw
  have hsq := symbol_le ha w
  have hg := (symbol_gap ha w).2
  set s := symbol a w
  set q := sq4 w
  have spos : 0 < s := by linarith
  have hnn : 0 ≤ 1 / s ^ 2 - 1 / q ^ 2 := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ spos.le hsq 2)
  rw [abs_of_nonneg hnn, div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) hw0]
  have h1 : (q - s) * (q + s) ≤ a ^ 2 / 12 * q ^ 2 * (2 * q) :=
    mul_le_mul hg (by linarith) (by linarith) (by positivity)
  have h2 : q ^ 2 / 4 * q ^ 2 ≤ s ^ 2 * q ^ 2 := by
    have : (q / 2) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
    nlinarith [sq_nonneg q]
  nlinarith [mul_le_mul_of_nonneg_right h1 hw0.le, mul_le_mul_of_nonneg_left h2 (sq_nonneg a)]

/-! ## 4. The shell -/

/-- 4D (Euclidean) momentum space. -/
abbrev Mom := EuclideanSpace ℝ (Fin 4)

/-- The shell `μ < |k| < M`. -/
def shell (μ M : ℝ) : Set Mom := (fun k : Mom => ‖k‖) ⁻¹' Ioo μ M

/-- The substrate's one-loop kernel `1/symbol²`. -/
def latKernel (a : ℝ) (k : Mom) : ℝ := 1 / symbol a (fun i => k i) ^ 2

/-- **Radial functions on the shell.** `∫_{μ<|k|<M} g(|k|) = 2π² ∫_μ^M r³ g(r) dr`. -/
theorem shell_radial (g : ℝ → ℝ) {μ M : ℝ} (hμ : 0 ≤ μ) :
    ∫ k in shell μ M, g ‖k‖ = 2 * π ^ 2 * ∫ y in Ioo μ M, y ^ 3 * g y := by
  have hS : MeasurableSet (shell μ M) := measurable_norm measurableSet_Ioo
  rw [← integral_indicator hS]
  have e : (shell μ M).indicator (fun k : Mom => g ‖k‖) = fun k => (Ioo μ M).indicator g ‖k‖ := by
    funext k; simp only [Set.indicator, shell, Set.mem_preimage]; split_ifs <;> rfl
  rw [e, integral_fun_norm_addHaar volume ((Ioo μ M).indicator g)]
  have e2 : ∀ y : ℝ, y ^ (Module.finrank ℝ Mom - 1) • (Ioo μ M).indicator g y =
      (Ioo μ M).indicator (fun y => y ^ 3 * g y) y := by
    intro y; rw [finrank_euclideanSpace_fin]; by_cases hy : y ∈ Ioo μ M <;> simp [hy]
  simp only [e2]
  rw [setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_right.2 (show Ioo μ M ⊆ Ioi 0 from fun y hy => lt_of_le_of_lt hμ hy.1),
    finrank_euclideanSpace_fin]
  have hv : volume.real (ball (0 : Mom) 1) = π ^ 2 / 2 := by
    rw [Measure.real, LoopMeasure.volume_ball_eq 0 zero_le_one,
      ENNReal.toReal_ofReal (by unfold LoopMeasure.ballVolume; positivity)]
    unfold LoopMeasure.ballVolume; ring
  rw [hv]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The continuum shell.** `∫_{μ<|k|<M} |k|⁻⁴ = 2π² ln(M/μ)`. -/
theorem shell_log {μ M : ℝ} (hμ : 0 < μ) (hμM : μ ≤ M) :
    ∫ k in shell μ M, ‖k‖⁻¹ ^ 4 = 2 * π ^ 2 * Real.log (M / μ) := by
  have h : ∫ k in shell μ M, ‖k‖⁻¹ ^ 4 = 2 * π ^ 2 * ∫ y in Ioo μ M, y ^ 3 * y⁻¹ ^ 4 :=
    shell_radial (fun y => y⁻¹ ^ 4) hμ.le
  have e : ∀ y : ℝ, y ^ 3 * y⁻¹ ^ 4 = y⁻¹ := fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [show y ^ 3 * y⁻¹ ^ 4 = (y * y⁻¹) ^ 3 * y⁻¹ by ring, mul_inv_cancel₀ hy, one_pow, one_mul]
  rw [h]
  simp only [e]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hμM,
    integral_inv_of_pos hμ (hμ.trans_le hμM)]

/-- The error kernel's shell integral: `∫_{μ<|k|<M} (2/3) a² |k|⁻² = (2/3) a² π² (M² − μ²)`. -/
theorem shell_error {a μ M : ℝ} (hμ : 0 ≤ μ) (hμM : μ ≤ M) :
    ∫ k in shell μ M, 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2 = 2 / 3 * a ^ 2 * (π ^ 2 * (M ^ 2 - μ ^ 2)) := by
  have h : ∫ k in shell μ M, 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2 =
      2 * π ^ 2 * ∫ y in Ioo μ M, y ^ 3 * (2 / 3 * a ^ 2 * y⁻¹ ^ 2) :=
    shell_radial (fun y => 2 / 3 * a ^ 2 * y⁻¹ ^ 2) hμ
  have e : ∀ y : ℝ, y ^ 3 * (2 / 3 * a ^ 2 * y⁻¹ ^ 2) = 2 / 3 * a ^ 2 * y := fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    rw [show y ^ 3 * (2 / 3 * a ^ 2 * y⁻¹ ^ 2) = 2 / 3 * a ^ 2 * y * (y * y⁻¹) ^ 2 by ring,
      mul_inv_cancel₀ hy, one_pow, mul_one]
  rw [h]
  simp only [e]
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hμM,
    integral_id]
  ring

/-- **The substrate shell.** For `a²M² ≤ 6`, the shell integral of the substrate's kernel is the
continuum's `2π² ln(M/μ)` up to `(2/3) a² π² (M² − μ²)`. -/
theorem shell_lattice {a μ M : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hμM : μ ≤ M)
    (hMa : a ^ 2 * M ^ 2 ≤ 6) :
    |(∫ k in shell μ M, latKernel a k) - 2 * π ^ 2 * Real.log (M / μ)| ≤
      2 / 3 * a ^ 2 * (π ^ 2 * (M ^ 2 - μ ^ 2)) := by
  have hS : MeasurableSet (shell μ M) := measurable_norm measurableSet_Ioo
  have hmem : ∀ k ∈ shell μ M, μ < ‖k‖ ∧ ‖k‖ < M := fun k hk => by simpa [shell] using hk
  have hsub : shell μ M ⊆ ball (0 : Mom) M := fun k hk => mem_ball_zero_iff.2 (hmem k hk).2
  have hfin : volume (shell μ M) < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
  have hq : ∀ k : Mom, sq4 (fun i => k i) = ‖k‖ ^ 2 :=
    fun k => (EuclideanSpace.real_norm_sq_eq k).symm
  have hpt : ∀ k ∈ shell μ M, ‖latKernel a k - ‖k‖⁻¹ ^ 4‖ ≤ 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2 := by
    intro k hk
    obtain ⟨h1, h2⟩ := hmem k hk
    have hk0 : 0 < ‖k‖ := hμ.trans h1
    have hq0 : 0 < sq4 (fun i => k i) := by rw [hq]; positivity
    have hqa : a ^ 2 * sq4 (fun i => k i) ≤ 6 := by
      rw [hq]
      have : ‖k‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hk0.le h2.le 2
      nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg a)]
    have h := kernel_gap ha hq0 hqa
    rw [Real.norm_eq_abs, show ‖k‖⁻¹ ^ 4 = 1 / sq4 (fun i => k i) ^ 2 by rw [hq]; ring,
      show 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2 = 2 / 3 * a ^ 2 / sq4 (fun i => k i) by rw [hq]; ring]
    exact h
  have hinv : ∀ k ∈ shell μ M, ‖k‖⁻¹ ≤ μ⁻¹ := fun k hk => inv_anti₀ hμ (hmem k hk).1.le
  have hsc : Continuous fun k : Mom => symbol a (fun i => k i) := by
    unfold symbol rk; fun_prop
  have hcm : Measurable fun k : Mom => ‖k‖⁻¹ ^ 4 := (measurable_norm.inv).pow_const 4
  have hlm : Measurable fun k : Mom => latKernel a k := by
    unfold latKernel; exact measurable_const.div (hsc.measurable.pow_const 2)
  have hbm : Measurable fun k : Mom => 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2 :=
    measurable_const.mul ((measurable_norm.inv).pow_const 2)
  have hBk : ∀ k ∈ shell μ M, 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2 ≤ 2 / 3 * a ^ 2 * μ⁻¹ ^ 2 := fun k hk =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg k)) (hinv k hk) 2)
      (by positivity)
  have hcont : IntegrableOn (fun k : Mom => ‖k‖⁻¹ ^ 4) (shell μ M) :=
    IntegrableOn.of_bound hfin hcm.aestronglyMeasurable (μ⁻¹ ^ 4)
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun k hk => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg k)) (hinv k hk) 4))
  have hbnd : IntegrableOn (fun k : Mom => 2 / 3 * a ^ 2 * ‖k‖⁻¹ ^ 2) (shell μ M) :=
    IntegrableOn.of_bound hfin hbm.aestronglyMeasurable (2 / 3 * a ^ 2 * μ⁻¹ ^ 2)
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun k hk => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hBk k hk))
  have hdiff : IntegrableOn (fun k : Mom => latKernel a k - ‖k‖⁻¹ ^ 4) (shell μ M) :=
    IntegrableOn.of_bound hfin (hlm.sub hcm).aestronglyMeasurable (2 / 3 * a ^ 2 * μ⁻¹ ^ 2)
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun k hk =>
        (hpt k hk).trans (hBk k hk)))
  have hlat : IntegrableOn (fun k : Mom => latKernel a k) (shell μ M) :=
    (hdiff.add hcont).congr_fun (fun k _ => by simp) hS
  rw [← shell_log hμ hμM, ← integral_sub hlat hcont, ← shell_error hμ.le hμM,
    ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hbnd ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall hpt))

/-- **The leading log on the substrate.** Per `d⁴k/(2π)⁴`, the substrate's shell
`μ < |k| < M` is `ln(M/μ)/(8π²)` (`LoopMeasure.log_unit`'s unit before the coupling) up to
`a²(M² − μ²)/(24π²)`. -/
theorem leading_log {a μ M : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hμM : μ ≤ M)
    (hMa : a ^ 2 * M ^ 2 ≤ 6) :
    |(∫ k in shell μ M, latKernel a k) / (2 * π) ^ 4 - Real.log (M / μ) / (8 * π ^ 2)| ≤
      a ^ 2 * (M ^ 2 - μ ^ 2) / (24 * π ^ 2) := by
  have h := shell_lattice ha hμ hμM hMa
  have hp : (0 : ℝ) < (2 * π) ^ 4 := by positivity
  have hπ : π ≠ 0 := pi_ne_zero
  have e : (∫ k in shell μ M, latKernel a k) / (2 * π) ^ 4 - Real.log (M / μ) / (8 * π ^ 2) =
      ((∫ k in shell μ M, latKernel a k) - 2 * π ^ 2 * Real.log (M / μ)) / (2 * π) ^ 4 := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  calc _ ≤ 2 / 3 * a ^ 2 * (π ^ 2 * (M ^ 2 - μ ^ 2)) := h
    _ = a ^ 2 * (M ^ 2 - μ ^ 2) / (24 * π ^ 2) * (2 * π) ^ 4 := by field_simp; ring

end PMAction.LeadingLog
