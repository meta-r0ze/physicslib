import PMAction.ShellMoments

/-!
# The polarization integrand's remainder over the window

`ShellMoments.shell_orbital` integrates the `q²` part of the scalar polarization integrand
`(2k + q)_μ(2k + q)_ν / (|k|²|k + q|²)`. This module bounds what the `q²` truncation leaves.

**Pointwise (`scalar_remainder`).** With `u = 2k·q + q²` (`PolarizationAverage.inv_expand`), the
integrand is its orders `0`, `1`, `2` in `q` plus seven groups of order three or more. In the window
`|q| ≤ |k|/2`, with `|k_μ| ≤ |k|`, `|q_μ| ≤ |q|`, `|k·q| ≤ |k||q|` and `|k + q|² ≥ |k|²/4`, the groups
are bounded by `4, 2, 1/2, 16, 2, 225/8, 3125/8` times `|q|³/|k|⁵`, so the remainder is at most
`500 |q|³/|k|⁵`.

**Over the shell (`polarization_window`).** For `2|q| ≤ lo`, the shell integral of the integrand
minus its `q`-independent part `I0` is `−(1/3)(q²δ_μν − q_μq_ν) · 2π² ln(hi/lo)` up to
`500 |q|³/lo · 2π² ln(hi/lo)`: the order-one part `A1` is odd and integrates to zero (`iso_inv`
with `k ↦ −k`), the `q²` part is `ShellMoments.shell_orbital`, and the rest is `Rm_bound`.
-/

noncomputable section
namespace PMAction.PolarizationRemainder

/-- The integrand's orders `0`, `1`, `2` in `q` (`a, b = k_μ, k_ν`; `c, e = q_μ, q_ν`;
`p = k·q`; `r = |k|`; `s = |q|`). -/
def trunc (a b c e p r s : ℝ) : ℝ :=
  4 * a * b / r ^ 4 + 2 * (a * e + c * b) / r ^ 4 - 8 * a * b * p / r ^ 6 + c * e / r ^ 4 -
    4 * (a * e + c * b) * p / r ^ 6 + 4 * a * b * (-s ^ 2 / r ^ 6 + 4 * p ^ 2 / r ^ 8)

set_option maxHeartbeats 800000 in
/-- **The pointwise remainder.** -/
theorem scalar_remainder {a b c e p r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r / 2)
    (ha : |a| ≤ r) (hb : |b| ≤ r) (hc : |c| ≤ s) (he : |e| ≤ s) (hp : |p| ≤ r * s) :
    |(2 * a + c) * (2 * b + e) / (r ^ 2 * (r ^ 2 + 2 * p + s ^ 2)) - trunc a b c e p r s| ≤
      500 * (s ^ 3 / r ^ 5) := by
  set D := r ^ 2 + 2 * p + s ^ 2 with hDdef
  have hp' := abs_le.1 hp
  have hD : r ^ 2 / 4 ≤ D := by
    nlinarith [mul_nonneg (sub_nonneg.2 hsr) (by linarith : (0 : ℝ) ≤ 3 * r / 2 - s)]
  have hr2 : 0 < r ^ 2 := by positivity
  have hr0 : r ≠ 0 := hr.ne'
  have hDpos : 0 < D := by linarith
  set X := s ^ 3 / r ^ 5 with hXdef
  have hX0 : 0 ≤ X := by positivity
  -- factor bounds
  have hae : |a * e| ≤ r * s := by rw [abs_mul]; exact mul_le_mul ha he (abs_nonneg _) hr.le
  have hcb : |c * b| ≤ s * r := by rw [abs_mul]; exact mul_le_mul hc hb (abs_nonneg _) hs
  have hab : |a * b| ≤ r * r := by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hr.le
  have hce : |c * e| ≤ s * s := by rw [abs_mul]; exact mul_le_mul hc he (abs_nonneg _) hs
  have hss : s ^ 2 ≤ r * s / 2 := by nlinarith
  have hrs : r * s ≤ r ^ 2 / 2 := by nlinarith
  have hN1 : |2 * (a * e + c * b)| ≤ 4 * r * s := by
    rw [abs_mul, abs_two]; nlinarith [abs_add_le (a * e) (c * b)]
  have hN0 : |4 * a * b| ≤ 4 * r ^ 2 := by
    rw [show 4 * a * b = 4 * (a * b) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hab]
  have hu1 : |2 * p| ≤ 2 * r * s := by rw [abs_mul, abs_two]; linarith
  have hu : |2 * p + s ^ 2| ≤ 5 / 2 * r * s := by
    have := abs_add_le (2 * p) (s ^ 2)
    rw [abs_of_nonneg (sq_nonneg s)] at this
    linarith
  have hN12 : |2 * (a * e + c * b) + c * e| ≤ 9 / 2 * r * s := by
    have := abs_add_le (2 * (a * e + c * b)) (c * e)
    nlinarith
  have hN : |4 * a * b + 2 * (a * e + c * b) + c * e| ≤ 25 / 4 * r ^ 2 := by
    have := abs_add_le (4 * a * b) (2 * (a * e + c * b) + c * e)
    rw [show 4 * a * b + 2 * (a * e + c * b) + c * e = 4 * a * b + (2 * (a * e + c * b) + c * e)
      by ring]
    nlinarith
  have hu3 : |2 * p + s ^ 2| ^ 3 ≤ (5 / 2 * r * s) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hu 3
  have hu2 : |2 * p + s ^ 2| ^ 2 ≤ (5 / 2 * r * s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu 2
  -- the identity
  have key : (2 * a + c) * (2 * b + e) / (r ^ 2 * D) - trunc a b c e p r s =
      -(2 * (a * e + c * b) * s ^ 2 / (r ^ 2) ^ 3 + c * e * (2 * p) / (r ^ 2) ^ 3 +
          c * e * s ^ 2 / (r ^ 2) ^ 3) +
        (4 * a * b * (2 * (2 * p) * s ^ 2) / (r ^ 2) ^ 4 + 4 * a * b * (s ^ 2) ^ 2 / (r ^ 2) ^ 4 +
          (2 * (a * e + c * b) + c * e) * (2 * p + s ^ 2) ^ 2 / (r ^ 2) ^ 4) -
        (4 * a * b + 2 * (a * e + c * b) + c * e) * (2 * p + s ^ 2) ^ 3 / ((r ^ 2) ^ 4 * D) := by
    have hD0 : r ^ 2 + 2 * p + s ^ 2 ≠ 0 := by rw [← hDdef]; exact hDpos.ne'
    unfold trunc
    rw [hDdef]
    field_simp
    ring
  -- group bounds: |num / r^(2m)| ≤ c X
  have grp : ∀ (num B : ℝ) (m : ℕ), |num| ≤ B * (s ^ 3 * r ^ (2 * m - 5)) → 3 ≤ m →
      |num / (r ^ 2) ^ m| ≤ B * X := by
    intro num B m h hm
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (r ^ 2) ^ m), div_le_iff₀ (by positivity),
      hXdef]
    have e : s ^ 3 / r ^ 5 * (r ^ 2) ^ m = s ^ 3 * r ^ (2 * m - 5) := by
      have h5 : r ^ (2 * m) = r ^ 5 * r ^ (2 * m - 5) := by rw [← pow_add]; congr 1; omega
      rw [← pow_mul, h5]
      field_simp
    rw [mul_assoc, e]; exact h
  have b1 := grp (2 * (a * e + c * b) * s ^ 2) 4 3 (by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    calc |2 * (a * e + c * b)| * s ^ 2 ≤ 4 * r * s * s ^ 2 :=
          mul_le_mul_of_nonneg_right hN1 (sq_nonneg s)
      _ = 4 * (s ^ 3 * r ^ (2 * 3 - 5)) := by rw [show 2 * 3 - 5 = 1 by norm_num, pow_one]; ring) le_rfl
  have b2 := grp (c * e * (2 * p)) 2 3 (by
    rw [abs_mul]
    calc |c * e| * |2 * p| ≤ (s * s) * (2 * r * s) :=
          mul_le_mul hce hu1 (abs_nonneg _) (by positivity)
      _ = 2 * (s ^ 3 * r ^ (2 * 3 - 5)) := by rw [show 2 * 3 - 5 = 1 by norm_num, pow_one]; ring) le_rfl
  have b3 := grp (c * e * s ^ 2) (1 / 2) 3 (by
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    calc |c * e| * s ^ 2 ≤ (s * s) * (r * s / 2) :=
          mul_le_mul hce hss (sq_nonneg s) (by positivity)
      _ = 1 / 2 * (s ^ 3 * r ^ (2 * 3 - 5)) := by rw [show 2 * 3 - 5 = 1 by norm_num, pow_one]; ring) le_rfl
  have b4 := grp (4 * a * b * (2 * (2 * p) * s ^ 2)) 16 4 (by
    rw [show 4 * a * b * (2 * (2 * p) * s ^ 2) = (4 * a * b) * ((2 * p) * (2 * s ^ 2)) by ring,
      abs_mul (4 * a * b), abs_mul (2 * p),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s ^ 2)]
    calc |4 * a * b| * (|2 * p| * (2 * s ^ 2)) ≤ (4 * r ^ 2) * ((2 * r * s) * (2 * s ^ 2)) :=
          mul_le_mul hN0 (mul_le_mul_of_nonneg_right hu1 (by positivity))
            (by positivity) (by positivity)
      _ = 16 * (s ^ 3 * r ^ (2 * 4 - 5)) := by rw [show 2 * 4 - 5 = 3 by norm_num]; ring) (by norm_num)
  have b5 := grp (4 * a * b * (s ^ 2) ^ 2) 2 4 (by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ 2) ^ 2)]
    calc |4 * a * b| * (s ^ 2) ^ 2 ≤ (4 * r ^ 2) * (s ^ 2 * (r * s / 2)) :=
          mul_le_mul hN0 (by rw [sq (s ^ 2)]; exact mul_le_mul_of_nonneg_left hss (sq_nonneg s))
            (by positivity) (by positivity)
      _ = 2 * (s ^ 3 * r ^ (2 * 4 - 5)) := by rw [show 2 * 4 - 5 = 3 by norm_num]; ring) (by norm_num)
  have b6 := grp ((2 * (a * e + c * b) + c * e) * (2 * p + s ^ 2) ^ 2) (225 / 8) 4 (by
    rw [abs_mul, abs_pow]
    calc |2 * (a * e + c * b) + c * e| * |2 * p + s ^ 2| ^ 2 ≤
          (9 / 2 * r * s) * (5 / 2 * r * s) ^ 2 :=
          mul_le_mul hN12 hu2 (by positivity) (by positivity)
      _ = 225 / 8 * (s ^ 3 * r ^ (2 * 4 - 5)) := by rw [show 2 * 4 - 5 = 3 by norm_num]; ring) (by norm_num)
  have b7 : |(4 * a * b + 2 * (a * e + c * b) + c * e) * (2 * p + s ^ 2) ^ 3 / ((r ^ 2) ^ 4 * D)| ≤
      3125 / 8 * X := by
    have hY : (0 : ℝ) < (r ^ 2) ^ 4 * D := mul_pos (by positivity) hDpos
    rw [abs_div, abs_of_pos hY, div_le_iff₀ hY, hXdef]
    have hn : |(4 * a * b + 2 * (a * e + c * b) + c * e) * (2 * p + s ^ 2) ^ 3| ≤
        25 / 4 * r ^ 2 * (5 / 2 * r * s) ^ 3 := by
      rw [abs_mul, abs_pow]; exact mul_le_mul hN hu3 (by positivity) (by positivity)
    have e : 3125 / 8 * (s ^ 3 / r ^ 5) * ((r ^ 2) ^ 4 * D) = 3125 / 8 * (s ^ 3 * r ^ 3) * D := by
      field_simp
    rw [e]
    have : 3125 / 8 * (s ^ 3 * r ^ 3) * (r ^ 2 / 4) ≤ 3125 / 8 * (s ^ 3 * r ^ 3) * D :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    calc _ ≤ 25 / 4 * r ^ 2 * (5 / 2 * r * s) ^ 3 := hn
      _ = 3125 / 8 * (s ^ 3 * r ^ 3) * (r ^ 2 / 4) := by ring
      _ ≤ _ := this
  rw [key]
  have := abs_le.1 b1; have := abs_le.1 b2; have := abs_le.1 b3; have := abs_le.1 b4
  have := abs_le.1 b5; have := abs_le.1 b6; have := abs_le.1 b7
  rw [abs_le]; constructor <;> linarith

/-! ## Over the shell -/

open Real MeasureTheory Set LeadingLog PolarizationAverage ShellMoments

variable {lo hi : ℝ}

/-- The scalar polarization integrand `(2k + q)_μ(2k + q)_ν / (|k|²|k + q|²)`. -/
def Ipol (q : Mom) (μ ν : Fin 4) (k : Mom) : ℝ :=
  (2 * k μ + q μ) * (2 * k ν + q ν) / (‖k‖ ^ 2 * ‖k + q‖ ^ 2)

/-- Its order `0` in `q`: independent of `q`, subtracted (gauge invariance removes it). -/
def I0 (μ ν : Fin 4) (k : Mom) : ℝ := 4 * (k μ * k ν) * ‖k‖⁻¹ ^ 4

/-- Its order `1` in `q`: odd in `k`. -/
def A1 (q : Mom) (μ ν : Fin 4) (k : Mom) : ℝ :=
  2 * (k μ * q ν + q μ * k ν) * ‖k‖⁻¹ ^ 4 - 8 * (k μ * k ν * inner ℝ k q) * ‖k‖⁻¹ ^ 6

/-- What the `q²` truncation leaves. -/
def Rm (q : Mom) (μ ν : Fin 4) (k : Mom) : ℝ :=
  Ipol q μ ν k - I0 μ ν k - A1 q μ ν k - coefC q μ ν k

lemma trunc_eq (q : Mom) (μ ν : Fin 4) (k : Mom) :
    trunc (k μ) (k ν) (q μ) (q ν) (inner ℝ k q) ‖k‖ ‖q‖ =
      I0 μ ν k + A1 q μ ν k + coefC q μ ν k := by
  simp only [trunc, I0, A1, coefC]; ring

lemma coord_le (k : Mom) (μ : Fin 4) : |k μ| ≤ ‖k‖ := by
  have := abs_real_inner_le_norm k (bv μ)
  rwa [inner_bv, norm_bv, mul_one] at this

/-- **The remainder, pointwise on the window.** -/
theorem Rm_bound (q : Mom) (μ ν : Fin 4) {k : Mom} (hk : 2 * ‖q‖ < ‖k‖) :
    |Rm q μ ν k| ≤ 500 * ‖q‖ ^ 3 * ‖k‖⁻¹ ^ 5 := by
  have hr : 0 < ‖k‖ := lt_of_le_of_lt (by positivity) hk
  have h := scalar_remainder hr (norm_nonneg q) (by linarith) (coord_le k μ) (coord_le k ν)
    (coord_le q μ) (coord_le q ν) (abs_real_inner_le_norm k q)
  have e : Rm q μ ν k = (2 * k μ + q μ) * (2 * k ν + q ν) /
      (‖k‖ ^ 2 * (‖k‖ ^ 2 + 2 * inner ℝ k q + ‖q‖ ^ 2)) -
        trunc (k μ) (k ν) (q μ) (q ν) (inner ℝ k q) ‖k‖ ‖q‖ := by
    rw [trunc_eq, Rm, Ipol, norm_add_sq_real]; ring
  rw [e]
  calc _ ≤ 500 * (‖q‖ ^ 3 / ‖k‖ ^ 5) := h
    _ = 500 * ‖q‖ ^ 3 * ‖k‖⁻¹ ^ 5 := by rw [div_eq_mul_inv, inv_pow]; ring

/-- **The polarization over the window.** For `2|q| ≤ lo`, the shell integral of the integrand
minus its `q`-independent part is the orbital `−(1/3)(q²δ_μν − q_μq_ν) · 2π² ln(hi/lo)` up to
`500 |q|³/lo · 2π² ln(hi/lo)`: the order-one part integrates to zero (it is odd), the `q²` part is
`ShellMoments.shell_orbital`, and the rest is `Rm_bound`. -/
theorem polarization_window (hlo : 0 < lo) (hlh : lo ≤ hi) (q : Mom) (hq : 2 * ‖q‖ ≤ lo)
    (μ ν : Fin 4) :
    |(∫ k in shell lo hi, (Ipol q μ ν k - I0 μ ν k)) -
        -(1 / 3) * (‖q‖ ^ 2 * d μ ν - q μ * q ν) * (2 * π ^ 2 * Real.log (hi / lo))| ≤
      500 * ‖q‖ ^ 3 * lo⁻¹ * (2 * π ^ 2 * Real.log (hi / lo)) := by
  have hS : MeasurableSet (shell lo hi) := measurable_norm measurableSet_Ioo
  have hmem : ∀ k ∈ shell lo hi, lo < ‖k‖ ∧ ‖k‖ < hi := fun k hk => by simpa [shell] using hk
  have hsub : shell lo hi ⊆ Metric.ball (0 : Mom) hi :=
    fun k hk => mem_ball_zero_iff.2 (hmem k hk).2
  have hfin : volume (shell lo hi) < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
  have hwin : ∀ k ∈ shell lo hi, 2 * ‖q‖ < ‖k‖ := fun k hk => by linarith [(hmem k hk).1]
  have hinv : ∀ k ∈ shell lo hi, ‖k‖⁻¹ ≤ lo⁻¹ := fun k hk => inv_anti₀ hlo (hmem k hk).1.le
  -- integrability
  have hA1 : IntegrableOn (fun k => A1 q μ ν k) (shell lo hi) :=
    (ion hlo (fun k : Mom => 2 * (k μ * q ν + q μ * k ν)) (by fun_prop) 4).sub
      (ion hlo (fun k : Mom => 8 * (k μ * k ν * inner ℝ k q)) (by fun_prop) 6)
  have hC : IntegrableOn (fun k => coefC q μ ν k) (shell lo hi) :=
    ((((ion hlo (fun k : Mom => -4 * ‖q‖ ^ 2 * (k μ * k ν)) (by fun_prop) 6).add
      (ion hlo (fun k : Mom => 16 * (k μ * k ν) * inner ℝ k q ^ 2) (by fun_prop) 8)).add
      (ion hlo (fun k : Mom => -4 * (k μ * q ν + q μ * k ν) * inner ℝ k q) (by fun_prop) 6)).add
      (ion hlo (fun _ : Mom => q μ * q ν) (by fun_prop) 4)).congr_fun
      (fun k _ => by simp only [Pi.add_apply, coefC]; ring) hS
  have hRmeas : Measurable fun k => Rm q μ ν k := by
    unfold Rm Ipol I0 A1 coefC; fun_prop
  have hR : IntegrableOn (fun k => Rm q μ ν k) (shell lo hi) :=
    IntegrableOn.of_bound hfin hRmeas.aestronglyMeasurable (500 * ‖q‖ ^ 3 * lo⁻¹ ^ 5)
      ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun k hk => by
        rw [Real.norm_eq_abs]
        refine (Rm_bound q μ ν (hwin k hk)).trans ?_
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg k)) (hinv k hk) 5) (by positivity)))
  -- the split
  have hsplit : ∫ k in shell lo hi, (Ipol q μ ν k - I0 μ ν k) =
      (∫ k in shell lo hi, A1 q μ ν k) + (∫ k in shell lo hi, coefC q μ ν k) +
        ∫ k in shell lo hi, Rm q μ ν k := by
    rw [← integral_add hA1 hC,
      ← integral_add (f := fun k => A1 q μ ν k + coefC q μ ν k) (hA1.add hC) hR]
    congr 1; funext k; simp only [Rm]; ring
  -- the odd part vanishes
  have hA0 : ∫ k in shell lo hi, A1 q μ ν k = 0 := by
    have h := iso_inv (lo := lo) (hi := hi) (LinearIsometryEquiv.neg ℝ) (fun k => A1 q μ ν k)
    have hneg : ∀ k : Mom, A1 q μ ν (LinearIsometryEquiv.neg ℝ k) = -A1 q μ ν k := by
      intro k
      show A1 q μ ν (-k) = _
      simp only [A1, PiLp.neg_apply, norm_neg, inner_neg_left]; ring
    simp only [hneg, integral_neg] at h
    linarith
  rw [hsplit, hA0, zero_add, shell_orbital hlo hlh, add_sub_cancel_left, ← Real.norm_eq_abs]
  have hg : IntegrableOn (fun k : Mom => 500 * ‖q‖ ^ 3 * lo⁻¹ * ‖k‖⁻¹ ^ 4) (shell lo hi) :=
    ion hlo (fun _ : Mom => 500 * ‖q‖ ^ 3 * lo⁻¹) (by fun_prop) 4
  calc ‖∫ k in shell lo hi, Rm q μ ν k‖
      ≤ ∫ k in shell lo hi, 500 * ‖q‖ ^ 3 * lo⁻¹ * ‖k‖⁻¹ ^ 4 :=
        norm_integral_le_of_norm_le hg ((ae_restrict_iff' hS).2
          (Filter.Eventually.of_forall fun k hk => by
            rw [Real.norm_eq_abs]
            refine (Rm_bound q μ ν (hwin k hk)).trans ?_
            rw [show ‖k‖⁻¹ ^ 5 = ‖k‖⁻¹ * ‖k‖⁻¹ ^ 4 by ring, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hinv k hk) (by positivity)) (by positivity)))
    _ = 500 * ‖q‖ ^ 3 * lo⁻¹ * (2 * π ^ 2 * Real.log (hi / lo)) := by
        rw [integral_const_mul, shell_log hlo hlh]

end PMAction.PolarizationRemainder
