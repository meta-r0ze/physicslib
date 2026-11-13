import PMAction.LeadingLog

/-!
# The vacuum polarization's orbital `−1/3` from the D₄ moments

`RunningResponse` derives a helicity pair's `B²` coefficient `a² − 1/3` from the Landau spectrum:
the Zeeman `a² = (2s)²` and the diamagnetic `−1/3`. Its log comes from the window between the
two scales. This module reads the same coefficient in momentum space on the substrate, where the
window is `LeadingLog`'s shell.

**The orbital `−1/3`.** A charged scalar's polarization loop has integrand
`(2k + q)_μ(2k + q)_ν / (k²(k + q)²)` (plus a seagull independent of `q`). For `|k|` in the
window above the external momentum `q`, expand `1/(k + q)²` with `u = 2k·q + q²`
(`inv_expand`): its `q²` part is `−q²/k⁴ + 4(k·q)²/k⁶`. The integrand's `q²` part is then
`coef` below: `4k_μk_ν(−q²/k⁶ + 4(k·q)²/k⁸) − 4(k_μq_ν + q_μk_ν)(k·q)/k⁶ + q_μq_ν/k⁴`.
Averaged over the 24 link roots it is
`−(1/3)(q²δ_μν − q_μq_ν)` times the average of `1/k⁴` (`orbital_third`). The average uses
the second moment `12δ` (`LeadingLog.moment`) and the fourth moment
`4(δδ + δδ + δδ)` (`D4Isotropy.fourth_moment`, `quad`): the D₄ roots are isotropic to fourth
order, which is what makes the result transverse. The hypercubic directions are not
(`D4Isotropy.hypercubic_not_isotropic`).

**The spin `a²`.** The Zeeman term enters at second order with no direction dependence, so it
multiplies the shell directly; its value `(2s)²` is `RunningResponse.zeeman`.

**The vertex.** The substrate's scalar vertex is `∂_μ symbol`, which is `2k_μ` up to
`(a²/3)|k|²√(2|k|²)` (`vertex_gap`), the vertex's counterpart of `LeadingLog.symbol_gap`. So in
the window `|k| ≪ 1/a` both the propagator and the vertex are the continuum's to `O(a²k²)`
relative, and the integrand above is the substrate's at leading order.

**The unit.** The `1/k⁴` that both terms multiply is `LeadingLog.leading_log`'s shell,
`ln(M/μ)/(8π²)` up to `a²(M² − μ²)/(24π²)`. With `α = g²/4π`, a coefficient `c` per unit index
shifts `α⁻¹` by `c · 4π · ln(M/μ)/(8π²) = c · ln(M/μ)/(2π)` (`running_unit`): the `2π` of
`RunningCoefficients`' `μ dα⁻¹/dμ = b₀/(2π)`.
-/

noncomputable section
namespace PMAction.PolarizationAverage
open Real D4Gauge LeadingLog

/-- Kronecker delta on `Fin 4`, real. -/
def d (μ ν : Fin 4) : ℝ := if μ = ν then 1 else 0

lemma fmom (μ ν ρ σ : Fin 4) :
    ∑ r ∈ roots, (vec r μ : ℝ) * vec r ν * vec r ρ * vec r σ =
      4 * (d μ ν * d ρ σ + d μ ρ * d ν σ + d μ σ * d ν ρ) := by
  have h := D4Isotropy.fourth_moment μ ν ρ σ
  simp only [D4Isotropy.δ] at h
  unfold d
  exact_mod_cast h

/-- `Σ_r (r·q)² r_μ r_ν = 4(|q|² δ_μν + 2 q_μ q_ν)`. -/
lemma quad (q : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ r ∈ roots, rk r q ^ 2 * (vec r μ : ℝ) * vec r ν = 4 * (sq4 q * d μ ν + 2 * q μ * q ν) := by
  have h1 : ∀ r, rk r q ^ 2 * (vec r μ : ℝ) * vec r ν =
      ∑ ρ, ∑ σ, q ρ * q σ * ((vec r μ : ℝ) * vec r ν * vec r ρ * vec r σ) := by
    intro r; simp only [rk, Fin.sum_univ_four]; ring
  rw [Finset.sum_congr rfl fun r _ => h1 r, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun ρ _ => Finset.sum_comm]
  simp only [← Finset.mul_sum, fmom]
  fin_cases μ <;> fin_cases ν <;> simp [Fin.sum_univ_four, d, sq4] <;> ring

/-- `1/(k² + u) = 1/k² − u/k⁴ + u²/k⁶ − u³/(k⁶(k² + u))`: with `u = 2k·q + q²` the `q²` part of
`1/(k + q)²` is `−q²/k⁴ + 4(k·q)²/k⁶`. -/
theorem inv_expand {k2 u : ℝ} (hk : k2 ≠ 0) (hd : k2 + u ≠ 0) :
    1 / (k2 + u) = 1 / k2 - u / k2 ^ 2 + u ^ 2 / k2 ^ 3 - u ^ 3 / (k2 ^ 3 * (k2 + u)) := by
  field_simp
  ring

/-- The `q²` part of the scalar polarization integrand at loop momentum `r`. -/
def coef (q : Fin 4 → ℝ) (μ ν : Fin 4) (r : Fin 4 → Fin 3) : ℝ :=
  4 * ((vec r μ : ℝ) * vec r ν) * (-sq4 q / sq4 (rv r) ^ 3 + 4 * rk r q ^ 2 / sq4 (rv r) ^ 4)
    - 4 * ((vec r μ : ℝ) * q ν + q μ * vec r ν) * rk r q / sq4 (rv r) ^ 3
    + q μ * q ν / sq4 (rv r) ^ 2

/-- **The orbital `−1/3`.** Over the D₄ roots, the polarization integrand's `q²` part is
`−(1/3)(q²δ_μν − q_μq_ν)` times the sum of `1/|r|⁴`: transverse, with the diamagnetic `−1/3`. -/
theorem orbital_third (q : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ r ∈ roots, coef q μ ν r =
      -(1 / 3) * (sq4 q * d μ ν - q μ * q ν) * ∑ r ∈ roots, 1 / sq4 (rv r) ^ 2 := by
  have e : ∀ r ∈ roots, coef q μ ν r =
      (-sq4 q / 2) * ((vec r μ : ℝ) * vec r ν) + rk r q ^ 2 * (vec r μ : ℝ) * vec r ν +
        (-q ν / 2) * (rk r q * vec r μ) + (-q μ / 2) * (rk r q * vec r ν) + q μ * q ν / 4 :=
    fun r hr => by unfold coef; rw [root_sq hr]; ring
  have e2 : ∀ r ∈ roots, 1 / sq4 (rv r) ^ 2 = 1 / 4 := fun r hr => by rw [root_sq hr]; norm_num
  rw [Finset.sum_congr rfl e, Finset.sum_congr rfl e2]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, roots_card, nsmul_eq_mul]
  rw [moment, quad, cross_moment, cross_moment]
  push_cast
  unfold d
  split_ifs <;> ring

/-- The roots' `Σ 1/|r|⁴ = 6`, so the orbital sum is `−2(q²δ_μν − q_μq_ν)`. -/
theorem orbital_sum (q : Fin 4 → ℝ) (μ ν : Fin 4) :
    ∑ r ∈ roots, coef q μ ν r = -2 * (sq4 q * d μ ν - q μ * q ν) := by
  have e2 : ∀ r ∈ roots, 1 / sq4 (rv r) ^ 2 = 1 / 4 := fun r hr => by rw [root_sq hr]; norm_num
  rw [orbital_third, Finset.sum_congr rfl e2, Finset.sum_const, roots_card, nsmul_eq_mul]
  push_cast
  ring

/-- **The running unit.** A coefficient per unit index times the shell `ln(M/μ)/(8π²)`, with
`α = g²/4π`, shifts `α⁻¹` by `ln(M/μ)/(2π)` per unit coefficient. -/
theorem running_unit (L : ℝ) : 4 * π * (L / (8 * π ^ 2)) = L / (2 * π) := by
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-! ## The vertex in the window -/

/-- The substrate's scalar vertex `∂_μ symbol`: `Σ_r r_μ sin(a r·k)/(6a)`. -/
def vertex (a : ℝ) (w : Fin 4 → ℝ) (μ : Fin 4) : ℝ :=
  (∑ r ∈ roots, (vec r μ : ℝ) * sin (a * rk r w)) / (6 * a)

lemma vec_abs (r : Fin 4 → Fin 3) (μ : Fin 4) : |(vec r μ : ℝ)| ≤ 1 := by
  have h : ∀ x : Fin 3, -1 ≤ (x : ℤ) - 1 ∧ (x : ℤ) - 1 ≤ 1 := by decide
  rw [abs_le]
  exact_mod_cast h (r μ)

/-- **The vertex's gap.** `|∂_μ symbol − 2k_μ| ≤ (a²/3)|k|²·√(2|k|²)`: the substrate vertex is the
continuum's `2k` up to `O(a²|k|³)`, as `LeadingLog.symbol_gap` is for the propagator. -/
theorem vertex_gap {a : ℝ} (ha : 0 < a) (w : Fin 4 → ℝ) (μ : Fin 4) :
    |vertex a w μ - 2 * w μ| ≤ a ^ 2 / 3 * sq4 w * Real.sqrt (2 * sq4 w) := by
  have hc : ∑ r ∈ roots, (vec r μ : ℝ) * (a * rk r w) = 6 * a * (2 * w μ) := by
    calc _ = a * ∑ r ∈ roots, rk r w * vec r μ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      _ = _ := by rw [cross_moment]; ring
  have ha6 : 6 * a ≠ 0 := by positivity
  have key : vertex a w μ - 2 * w μ =
      (∑ r ∈ roots, (vec r μ : ℝ) * (sin (a * rk r w) - a * rk r w)) / (6 * a) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hc, vertex, sub_div, mul_div_cancel_left₀ _ ha6]
  have hroot : ∀ r ∈ roots, |(vec r μ : ℝ) * (sin (a * rk r w) - a * rk r w)| ≤
      a ^ 3 / 6 * (Real.sqrt (2 * sq4 w) * rk r w ^ 2) := by
    intro r hr
    have hv := vec_abs r μ
    have hs : |sin (a * rk r w) - a * rk r w| ≤ |a * rk r w| ^ 3 / 6 := by
      rw [abs_sub_comm]; exact abs_sub_sin_le _
    have hcs : rk r w ^ 2 ≤ 2 * sq4 w := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (vec r i : ℝ)) w
      rw [show (∑ i, (vec r i : ℝ) ^ 2) = 2 from root_sq hr] at this
      exact this
    have habs : |rk r w| ≤ Real.sqrt (2 * sq4 w) := Real.abs_le_sqrt hcs
    rw [abs_mul]
    calc |(vec r μ : ℝ)| * |sin (a * rk r w) - a * rk r w| ≤ 1 * (|a * rk r w| ^ 3 / 6) :=
          mul_le_mul hv hs (abs_nonneg _) zero_le_one
      _ = a ^ 3 / 6 * (|rk r w| * rk r w ^ 2) := by
          rw [abs_mul, abs_of_pos ha, mul_pow, show |rk r w| ^ 3 = |rk r w| * rk r w ^ 2 by
            rw [← sq_abs]; ring]
          ring
      _ ≤ a ^ 3 / 6 * (Real.sqrt (2 * sq4 w) * rk r w ^ 2) := by gcongr
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 6 * a), div_le_iff₀ (by positivity)]
  calc |∑ r ∈ roots, (vec r μ : ℝ) * (sin (a * rk r w) - a * rk r w)|
      ≤ ∑ r ∈ roots, |(vec r μ : ℝ) * (sin (a * rk r w) - a * rk r w)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ roots, a ^ 3 / 6 * (Real.sqrt (2 * sq4 w) * rk r w ^ 2) := Finset.sum_le_sum hroot
    _ = a ^ 3 / 6 * Real.sqrt (2 * sq4 w) * ∑ r ∈ roots, rk r w ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
    _ = a ^ 2 / 3 * sq4 w * Real.sqrt (2 * sq4 w) * (6 * a) := by rw [rk_sq_sum]; ring

end PMAction.PolarizationAverage
