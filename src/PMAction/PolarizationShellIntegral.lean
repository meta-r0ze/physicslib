import PMAction.PolarizationShellPointwise

/-!
# Step (d2) of the subtracted lattice polarization: the shell integral

* `leg_reflect`, `symbol_neg`, `contact_reflect`, `latInt_reflect`: under `(k, q) ↦ (−k, −q)` the
  leg changes sign and the symbols and the contact do not, so `latInt a (−q) μ ν (−k) = latInt a q μ ν k`.
* `int_reflect`: with `k ↦ −k` (`iso_inv`), `∫_shell L(−q) = ∫_shell L(q)`.
* `sym_pos`: on the closed shell `lo ≤ |k| ≤ hi`, with `|p| ≤ |q|`, `4|q| ≤ lo`, `2 a hi ≤ 1`,
  the symbol at `k + p` is positive.
* `latInt_int`: so `latInt` is continuous on the closed shell and integrable on the shell.
* `coefC_int`: the continuum integrand `coefC` is integrable on the shell.
* `shell_integral`: for `0 < lo ≤ hi`, `4|q| ≤ lo`, `2 a hi ≤ 1`,
  `|∫_shell (L(q) − L(0)) − (−1/3)(|q|² δ_μν − q_μ q_ν)·2π² ln(hi/lo)|
     ≤ (4K a² hi² |q|² + 8P(1) |q|³/lo)·2π² ln(hi/lo)`,
  with `K = 271853128/3`, `P(1) = 47979504985/36`.

The proof: `∫(L(q) − L(0)) = ∫((L(q) + L(−q))/2 − L(0))` (`int_reflect`), `∫ coefC` is the orbital
term (`shell_orbital`), and the pointwise bound (`shell_pointwise`) integrates against `shell_log`.
-/

noncomputable section
namespace PMAction.PolarizationShellIntegral
open Real MeasureTheory LeadingLog PolarizationContact PolarizationOrders PolarizationMagnitudes
  PolarizationPointwise ShellMoments PolarizationShellPointwise

/-! ## The reflection `(k, q) ↦ (−k, −q)` -/

lemma leg_reflect (a : ℝ) (k Q v : Fin 4 → ℝ) : leg a (-k) (-Q) v 1 = -leg a k Q v 1 := by
  unfold leg
  rw [← neg_div, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rk_neg, rk_neg, show a * -rk r Q / 2 = -(a * rk r Q / 2) by ring,
    show a * -rk r k + 1 * -(a * rk r Q / 2) = -(a * rk r k + 1 * (a * rk r Q / 2)) by ring,
    sinc_neg, sin_neg]
  ring

lemma symbol_neg (a : ℝ) (w : Fin 4 → ℝ) : symbol a (-w) = symbol a w := by
  unfold symbol
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rk_neg, mul_neg, cos_neg]

lemma contact_reflect (a : ℝ) (k Q u v : Fin 4 → ℝ) : contact a (-k) (-Q) u v = contact a k Q u v := by
  unfold contact
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [rk_neg, rk_neg, mul_neg, cos_neg, show a * -rk r Q / 2 = -(a * rk r Q / 2) by ring, sinc_neg]

theorem latInt_reflect (a : ℝ) (Q : Fin 4 → ℝ) (μ ν : Fin 4) (k : Fin 4 → ℝ) :
    latInt a (-Q) μ ν (-k) = latInt a Q μ ν k := by
  unfold latInt
  rw [leg_reflect, leg_reflect, contact_reflect, show -k + -Q = -(k + Q) by abel, symbol_neg,
    symbol_neg]
  ring

theorem int_reflect {lo hi a : ℝ} (q : Mom) (μ ν : Fin 4) :
    ∫ k in shell lo hi, latInt a (-(fun i => q i)) μ ν (fun i => k i) =
      ∫ k in shell lo hi, latInt a (fun i => q i) μ ν (fun i => k i) := by
  have h := iso_inv (lo := lo) (hi := hi) (LinearIsometryEquiv.neg ℝ)
    (fun k : Mom => latInt a (-(fun i => q i)) μ ν (fun i => k i))
  have hneg : ∀ k : Mom, (LinearIsometryEquiv.neg ℝ) k = -k := fun _ => rfl
  have hpt : ∀ k : Mom, latInt a (-(fun i => q i)) μ ν (fun i => (-k) i) =
      latInt a (fun i => q i) μ ν (fun i => k i) := fun k => by
    rw [show (fun i => (-k) i) = -(fun i => k i) from funext fun i => by simp, latInt_reflect]
  simp only [hneg, hpt] at h
  exact h.symm

/-! ## Integrability -/

lemma sym_pos {a lo hi : ℝ} (ha : 0 < a) (hlo : 0 < lo) (hah : 2 * a * hi ≤ 1) {q : Mom}
    (hq : 4 * ‖q‖ ≤ lo) {k : Mom} (hk1 : lo ≤ ‖k‖) (hk2 : ‖k‖ ≤ hi) {p : Mom} (hp : ‖p‖ ≤ ‖q‖) :
    0 < symbol a (fun i => (k + p) i) := by
  have hl : ‖k‖ - ‖p‖ ≤ ‖k + p‖ := by
    have := norm_sub_norm_le k (-p); rwa [norm_neg, sub_neg_eq_add] at this
  have hu : ‖k + p‖ ≤ ‖k‖ + ‖p‖ := norm_add_le _ _
  have hq0 := norm_nonneg q
  have hpos : 0 < ‖k + p‖ := by linarith
  have h2 : ‖k + p‖ ≤ 2 * hi := by linarith
  have hsq := sq4_mom (k + p)
  have h6 : a ^ 2 * sq4 (fun i => (k + p) i) ≤ 6 := by
    rw [hsq]
    have h0 : 0 ≤ 2 * a * hi :=
      mul_nonneg (mul_nonneg (by norm_num) ha.le) ((norm_nonneg k).trans hk2)
    have h3 : ‖k + p‖ ^ 2 ≤ (2 * hi) ^ 2 := pow_le_pow_left₀ hpos.le h2 2
    calc a ^ 2 * ‖k + p‖ ^ 2 ≤ a ^ 2 * (2 * hi) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg a)
      _ = (2 * a * hi) ^ 2 := by ring
      _ ≤ 1 := pow_le_one₀ h0 hah
      _ ≤ 6 := by norm_num
  have := half_le_symbol ha h6
  rw [hsq] at this
  have : 0 < ‖k + p‖ ^ 2 := pow_pos hpos 2
  linarith

theorem latInt_int {a lo hi : ℝ} (ha : 0 < a) (hlo : 0 < lo) (hah : 2 * a * hi ≤ 1) {q : Mom}
    (hq : 4 * ‖q‖ ≤ lo) {Q : Mom} (hQ : ‖Q‖ ≤ ‖q‖) (μ ν : Fin 4) :
    IntegrableOn (fun k : Mom => latInt a (fun i => Q i) μ ν (fun i => k i)) (shell lo hi) := by
  have hK : IsCompact (Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖}) :=
    (isCompact_closedBall 0 hi).inter_right (isClosed_le continuous_const continuous_norm)
  have hsub : shell lo hi ⊆ Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖} := fun k hk => by
    simp only [shell, Set.mem_preimage, Set.mem_Ioo] at hk
    exact ⟨mem_closedBall_zero_iff.2 hk.2.le, hk.1.le⟩
  refine (ContinuousOn.integrableOn_compact hK ?_).mono_set hsub
  have hL : ∀ v : Fin 4 → ℝ, Continuous fun k : Mom => leg a (fun i => k i) (fun i => Q i) v 1 := by
    intro v; unfold leg rk; fun_prop
  have hC : Continuous fun k : Mom => contact a (fun i => k i) (fun i => Q i) (e μ) (e ν) := by
    unfold contact rk; fun_prop
  have hS1 : Continuous fun k : Mom => symbol a (fun i => k i) := by
    unfold symbol rk; fun_prop
  have hS2 : Continuous fun k : Mom => symbol a ((fun i => k i) + fun i => Q i) := by
    unfold symbol rk; simp only [Pi.add_apply]; fun_prop
  have hmem : ∀ k ∈ Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖}, lo ≤ ‖k‖ ∧ ‖k‖ ≤ hi :=
    fun k hk => ⟨hk.2, mem_closedBall_zero_iff.1 hk.1⟩
  have hne1 : ∀ k ∈ Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖},
      symbol a (fun i => k i) ≠ 0 := fun k hk => by
    have := sym_pos ha hlo hah hq (hmem k hk).1 (hmem k hk).2 (p := 0) (by simp)
    simp only [add_zero] at this
    exact this.ne'
  have hne2 : ∀ k ∈ Metric.closedBall (0 : Mom) hi ∩ {k | lo ≤ ‖k‖},
      symbol a ((fun i => k i) + fun i => Q i) ≠ 0 := fun k hk => by
    have := sym_pos ha hlo hah hq (hmem k hk).1 (hmem k hk).2 hQ
    rw [show (fun i => (k + Q) i) = (fun i => k i) + fun i => Q i from funext fun i => by simp]
      at this
    exact this.ne'
  simp only [latInt]
  exact (((hL (e μ)).mul (hL (e ν))).continuousOn.div (hS1.mul hS2).continuousOn
      fun k hk => mul_ne_zero (hne1 k hk) (hne2 k hk)).sub
    (hC.continuousOn.div hS1.continuousOn hne1)

theorem coefC_int {lo hi : ℝ} (hlo : 0 < lo) (q : Mom) (μ ν : Fin 4) :
    IntegrableOn (fun k : Mom => coefC q μ ν k) (shell lo hi) := by
  have e : (fun k : Mom => coefC q μ ν k) = fun k =>
      (-4 * ‖q‖ ^ 2) * (inner ℝ k (bv μ) * inner ℝ k (bv ν) * ‖k‖⁻¹ ^ 6) +
        16 * (inner ℝ k (bv μ) * inner ℝ k (bv ν) * inner ℝ k q ^ 2 * ‖k‖⁻¹ ^ 8) +
          (-4 * q ν) * (inner ℝ k (bv μ) * inner ℝ k q * ‖k‖⁻¹ ^ 6) +
            (-4 * q μ) * (inner ℝ k (bv ν) * inner ℝ k q * ‖k‖⁻¹ ^ 6) +
              (q μ * q ν) * (1 * ‖k‖⁻¹ ^ 4) := funext fun k => by
    simp only [coefC, inner_bv]; ring
  rw [e]
  have h1 := Integrable.const_mul
    (ion (hi := hi) hlo (fun k => inner ℝ k (bv μ) * inner ℝ k (bv ν)) (by fun_prop) 6) (-4 * ‖q‖ ^ 2)
  have h2 := Integrable.const_mul
    (ion (hi := hi) hlo (fun k => inner ℝ k (bv μ) * inner ℝ k (bv ν) * inner ℝ k q ^ 2)
      (by fun_prop) 8) 16
  have h3 := Integrable.const_mul
    (ion (hi := hi) hlo (fun k => inner ℝ k (bv μ) * inner ℝ k q) (by fun_prop) 6) (-4 * q ν)
  have h4 := Integrable.const_mul
    (ion (hi := hi) hlo (fun k => inner ℝ k (bv ν) * inner ℝ k q) (by fun_prop) 6) (-4 * q μ)
  have h5 := Integrable.const_mul
    (ion (hi := hi) hlo (fun _ => (1 : ℝ)) (by fun_prop) 4) (q μ * q ν)
  exact (((h1.add h2).add h3).add h4).add h5

/-! ## The shell integral -/

/-- **The shell integral of the subtracted lattice polarization.** -/
theorem shell_integral {a lo hi : ℝ} (ha : 0 < a) (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hah : 2 * a * hi ≤ 1) {q : Mom} (hq : 4 * ‖q‖ ≤ lo) (μ ν : Fin 4) :
    |(∫ k in shell lo hi, (latInt a (fun i => q i) μ ν (fun i => k i) -
          latInt a 0 μ ν (fun i => k i))) -
        -(1 / 3) * (‖q‖ ^ 2 * PolarizationAverage.d μ ν - q μ * q ν) * (2 * π ^ 2 * Real.log (hi / lo))| ≤
      (4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * ‖q‖ ^ 2 + 8 * (47979504985 / 36) * ‖q‖ ^ 3 / lo) *
        (2 * π ^ 2 * Real.log (hi / lo)) := by
  have hS : MeasurableSet (shell lo hi) := measurable_norm measurableSet_Ioo
  have Iq := latInt_int ha hlo hah hq (Q := q) le_rfl μ ν
  have Im := latInt_int ha hlo hah hq (Q := -q) (by rw [norm_neg]) μ ν
  rw [show (fun i => (-q) i) = -(fun i => q i) from funext fun i => by simp] at Im
  have I0 := latInt_int ha hlo hah hq (Q := 0) (by simp) μ ν
  rw [show (fun i => (0 : Mom) i) = 0 from funext fun i => by simp] at I0
  have hC := coefC_int (hi := hi) hlo q μ ν
  have hF : IntegrableOn (fun k : Mom => (latInt a (fun i => q i) μ ν (fun i => k i) +
      latInt a (-(fun i => q i)) μ ν (fun i => k i)) / 2 - latInt a 0 μ ν (fun i => k i))
      (shell lo hi) := Integrable.sub (Integrable.div_const (Integrable.add Iq Im) 2) I0
  have h1 : (∫ k in shell lo hi, (latInt a (fun i => q i) μ ν (fun i => k i) -
        latInt a 0 μ ν (fun i => k i))) =
      ∫ k in shell lo hi, ((latInt a (fun i => q i) μ ν (fun i => k i) +
        latInt a (-(fun i => q i)) μ ν (fun i => k i)) / 2 - latInt a 0 μ ν (fun i => k i)) := by
    have hA : IntegrableOn (fun k : Mom => (latInt a (fun i => q i) μ ν (fun i => k i) +
        latInt a (-(fun i => q i)) μ ν (fun i => k i)) / 2) (shell lo hi) :=
      Integrable.div_const (Integrable.add Iq Im) 2
    rw [integral_sub Iq I0, integral_sub hA I0, integral_div, integral_add Iq Im, int_reflect]
    ring
  have h2 := integral_sub hF hC
  have hinv : IntegrableOn (fun k : Mom => ‖k‖⁻¹ ^ 4) (shell lo hi) := by
    simpa using ion (hi := hi) hlo (fun _ => (1 : ℝ)) continuous_const 4
  rw [h1, ← shell_orbital hlo hlh q μ ν, ← h2, ← shell_log hlo hlh, ← integral_const_mul,
    ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (Integrable.const_mul hinv _) ?_
  refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun k hk => ?_)
  rw [Real.norm_eq_abs]
  exact shell_pointwise ha hlo hah hq hk μ ν

end PMAction.PolarizationShellIntegral
