import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Peierls dichotomy: discrete link values have an excitation gap, `U(1)` does not

The contour route to a volume-uniform gap (`DefectGap`, `ContourCount`, `PolymerConvergence`,
`GapFromDecay`) needs the **Peierls condition**: every non-vacuum local value costs at least a fixed
positive amount. This file isolates where that holds and where it fails. It is the check that the
argument cannot give the photon a mass.

* `finite_peierls`: if a plaquette variable takes values in a **finite** set and its cost is
  positive off the identity, there is a minimum positive cost `m > 0`. Any finite gauge group (for
  example a discrete subgroup reached from the `E₈` substrate) satisfies the Peierls condition.
* `u1_no_peierls`: for `U(1)` with the Wilson cost `Re(1 − z)` (the `N = 1` case of
  `LatticeGibbs.wilson_bounds`), for every `ε > 0` there is a unit `z ≠ 1` with cost `< ε`. Built
  from the rational points `z = ((1 − t²) + 2t i)/(1 + t²)` of the circle, without trigonometry.
  The Peierls condition fails, so the contour argument gives **no** gap for a continuous abelian
  link variable. This matches the massless Coulomb phase of 4D `U(1)` at weak coupling (Guth;
  Fröhlich–Spencer).

## Consequence for PM

The contour argument proves a gap only for **discrete** link values. Continuous `SU(N)` fails
the same way as `U(1)`: near the identity the Wilson cost has no positive minimum. So:
(i) the PM gap is a statement about a discrete substrate sector; (ii) if `SU(3)` colour is read
out from that discrete sector, the gap must survive the readout, which is unproved; (iii) the
photon must be read out from a sector where this argument does not apply, or PM predicts a
massive photon. Item (iii) is a falsifiable constraint on the readout.
-/

namespace PMAction.PeierlsDichotomy

/-- **Finite link values satisfy the Peierls condition.** -/
theorem finite_peierls {G : Type*} [Fintype G] [DecidableEq G] (one : G) (c : G → ℝ)
    (hpos : ∀ g, g ≠ one → 0 < c g) (hnt : ∃ g, g ≠ one) :
    ∃ m : ℝ, 0 < m ∧ ∀ g, g ≠ one → m ≤ c g := by
  classical
  let S : Finset G := Finset.univ.filter fun g => g ≠ one
  have hS : S.Nonempty := by
    obtain ⟨g, hg⟩ := hnt
    exact ⟨g, by simp [S, hg]⟩
  refine ⟨S.inf' hS c, ?_, fun g hg => Finset.inf'_le c (by simp [S, hg])⟩
  rw [Finset.lt_inf'_iff]
  intro g hg
  exact hpos g (by simpa [S] using hg)

/-- A rational point on the unit circle. -/
noncomputable def circlePoint (t : ℝ) : ℂ := ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

lemma circlePoint_normSq (t : ℝ) : Complex.normSq (circlePoint t) = 1 := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [Complex.normSq_apply]
  simp only [circlePoint]
  field_simp
  ring

lemma circlePoint_ne_one {t : ℝ} (ht : t ≠ 0) : circlePoint t ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp only [circlePoint, Complex.one_im] at him
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_eq_zero_iff] at him
  rcases him with h1 | h1
  · exact ht (by linarith)
  · linarith

lemma circlePoint_cost (t : ℝ) : (1 - circlePoint t).re = 2 * t ^ 2 / (1 + t ^ 2) := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  simp only [Complex.sub_re, Complex.one_re, circlePoint]
  field_simp
  ring

/-- **`U(1)` violates the Peierls condition.** Arbitrarily cheap non-identity plaquettes exist. -/
theorem u1_no_peierls (ε : ℝ) (hε : 0 < ε) :
    ∃ z : ℂ, Complex.normSq z = 1 ∧ z ≠ 1 ∧ (1 - z).re < ε := by
  set t : ℝ := min 1 (ε / 4) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htε : t ≤ ε / 4 := min_le_right _ _
  refine ⟨circlePoint t, circlePoint_normSq t, circlePoint_ne_one ht0.ne', ?_⟩
  rw [circlePoint_cost]
  have hd : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [div_lt_iff₀ hd]
  nlinarith [sq_nonneg t]

/-- **No positive minimum cost for `U(1)`.** -/
theorem u1_no_min_cost :
    ¬ ∃ m : ℝ, 0 < m ∧ ∀ z : ℂ, Complex.normSq z = 1 → z ≠ 1 → m ≤ (1 - z).re := by
  rintro ⟨m, hm, h⟩
  obtain ⟨z, hz1, hz2, hz3⟩ := u1_no_peierls m hm
  linarith [h z hz1 hz2]

end PMAction.PeierlsDichotomy
