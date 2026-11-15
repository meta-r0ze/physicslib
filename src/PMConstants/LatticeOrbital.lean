import PMAction.PolarizationShellIntegral

/-!
# The orbital `−1/3` from the substrate's lattice polarization

`PMConstants.RunningResponseLink` takes the vacuum polarization's orbital `−1/3` as a premise read
from the continuum integrand (`PMAction.PolarizationAverage.orbital_third`,
`PMAction.PolarizationRemainder.polarization_window`). This module reads it from the substrate's
lattice integrand instead: the link Laplacian's symbol, the sinc-weighted conserved vertex and the
contact term (`PMAction.PolarizationPointwise.latInt`), with the `q = 0` value subtracted, on the
shell `lo < |k| < hi` (`PMAction.PolarizationShellIntegral.shell_integral`).

* `latPol`, `orbital`: the subtracted lattice polarization on the shell, and the continuum's
  orbital term `−(1/3)(|q|² δ_μν − q_μ q_ν) · 2π² ln(hi/lo)`.
* `lattice_coefficient`: for `q ≠ 0` in the window (`4|q| ≤ lo`, `2 a hi ≤ 1`), divided by `|q|²`,
  the two differ by at most `(4K a² hi² + 8P(1)|q|/lo) · 2π² ln(hi/lo)`.
* `lattice_orbital_limit`: along a unit direction `u`, the `q²` coefficient of the lattice
  polarization tends to `−(1/3)(δ_μν − u_μ u_ν) · 2π² ln(hi/lo)` as `a → 0` and `|q| → 0`, jointly.

So the orbital `−1/3` is a property of the substrate's own integrand in the continuum limit, not only
of the continuum integrand. Scope: the momentum integral is the continuum shell (not the Brillouin-zone
sum), and the limit is `a → 0` at a fixed shell. The constants `K = 271853128/3`,
`P(1) = 47979504985/36` are crude; they make no claim about the size of the lattice correction at a
given `a`.
-/

noncomputable section
namespace PMConstants.LatticeOrbital
open Real MeasureTheory PMAction PMAction.LeadingLog PMAction.PolarizationPointwise
  PMAction.PolarizationShellIntegral

/-- The subtracted lattice polarization on the shell `lo < |k| < hi`. -/
def latPol (a lo hi : ℝ) (q : Mom) (μ ν : Fin 4) : ℝ :=
  ∫ k in shell lo hi, (latInt a (fun i => q i) μ ν (fun i => k i) - latInt a 0 μ ν (fun i => k i))

/-- The continuum's orbital term on the shell. -/
def orbital (lo hi : ℝ) (q : Mom) (μ ν : Fin 4) : ℝ :=
  -(1 / 3) * (‖q‖ ^ 2 * PolarizationAverage.d μ ν - q μ * q ν) * (2 * π ^ 2 * Real.log (hi / lo))

/-- **The `q²` coefficient, with explicit rates.** -/
theorem lattice_coefficient {a lo hi : ℝ} (ha : 0 < a) (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hah : 2 * a * hi ≤ 1) {q : Mom} (hq : 4 * ‖q‖ ≤ lo) (hq0 : q ≠ 0) (μ ν : Fin 4) :
    |latPol a lo hi q μ ν / ‖q‖ ^ 2 - orbital lo hi q μ ν / ‖q‖ ^ 2| ≤
      (4 * (271853128 / 3) * a ^ 2 * hi ^ 2 + 8 * (47979504985 / 36) * ‖q‖ / lo) *
        (2 * π ^ 2 * Real.log (hi / lo)) := by
  have hn : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have hn2 : 0 < ‖q‖ ^ 2 := pow_pos hn 2
  have h := shell_integral ha hlo hlh hah hq μ ν
  rw [← sub_div, abs_div, abs_of_pos hn2, div_le_iff₀ hn2]
  unfold latPol orbital
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **The orbital `−1/3` in the continuum limit of the lattice integrand.** -/
theorem lattice_orbital_limit {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi) {u : Mom} (hu : ‖u‖ = 1)
    (μ ν : Fin 4) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a s : ℝ, 0 < a → a ≤ δ → 0 < s → s ≤ δ →
      |latPol a lo hi (s • u) μ ν / s ^ 2 -
          -(1 / 3) * (PolarizationAverage.d μ ν - u μ * u ν) * (2 * π ^ 2 * Real.log (hi / lo))| ≤ ε := by
  have hhi : 0 < hi := hlo.trans_le hlh
  set L := 2 * π ^ 2 * Real.log (hi / lo) with hLdef
  have hL : 0 ≤ L := by
    have : 0 ≤ Real.log (hi / lo) := Real.log_nonneg ((one_le_div hlo).2 hlh)
    positivity
  set A := 4 * (271853128 / 3 : ℝ) * hi ^ 2 * L with hA
  set B := 8 * (47979504985 / 36 : ℝ) * L with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine ⟨min (min 1 (1 / (2 * hi))) (min (lo / 4) (min (ε / (2 * (A + 1))) (ε * lo / (2 * (B + 1))))),
    by positivity, ?_⟩
  intro a s ha haδ hs hsδ
  have ha1 : a ≤ 1 := haδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have ha2 : a ≤ 1 / (2 * hi) := haδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : s ≤ lo / 4 := hsδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ha3 : a ≤ ε / (2 * (A + 1)) :=
    haδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs2 : s ≤ ε * lo / (2 * (B + 1)) :=
    hsδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnorm : ‖s • u‖ = s := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  have hq0 : s • u ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; exact hs.ne' hnorm.symm
  have hq : 4 * ‖s • u‖ ≤ lo := by rw [hnorm]; linarith
  have hah : 2 * a * hi ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * hi)).1 ha2
    linarith
  have hc := lattice_coefficient ha hlo hlh hah hq hq0 μ ν
  have horb : orbital lo hi (s • u) μ ν / ‖s • u‖ ^ 2 =
      -(1 / 3) * (PolarizationAverage.d μ ν - u μ * u ν) * L := by
    have hs0 : s ≠ 0 := hs.ne'
    have hcomp : ∀ i, (s • u) i = s * u i := fun i => by simp
    unfold orbital
    rw [hnorm, hcomp, hcomp]
    field_simp
    ring
  rw [horb, hnorm] at hc
  refine hc.trans ?_
  -- the two error terms
  have hsq : a ^ 2 ≤ a := by nlinarith
  have e1 : A * a ≤ ε / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (A + 1))).1 ha3
    nlinarith
  have e2 : B * s ≤ ε * lo / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (B + 1))).1 hs2
    nlinarith
  have t1 : 4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * L ≤ ε / 2 := by
    have : 4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * L = A * a ^ 2 := by rw [hA]; ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left hsq hA0).trans e1
  have t2 : 8 * (47979504985 / 36) * s / lo * L ≤ ε / 2 := by
    have : 8 * (47979504985 / 36) * s / lo * L = B * s / lo := by rw [hB]; ring
    rw [this, div_le_iff₀ hlo]
    linarith
  calc (4 * (271853128 / 3) * a ^ 2 * hi ^ 2 + 8 * (47979504985 / 36) * s / lo) * L
      = 4 * (271853128 / 3) * a ^ 2 * hi ^ 2 * L + 8 * (47979504985 / 36) * s / lo * L := by ring
    _ ≤ ε / 2 + ε / 2 := add_le_add t1 t2
    _ = ε := by ring

end PMConstants.LatticeOrbital
