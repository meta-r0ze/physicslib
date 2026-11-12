import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The squared-amplitude readout from additivity and invariance

`CommonResponse` and `CarrierResponse` take the readout of an amplitude to be its squared modulus
("not a Born-rule derivation"). This file derives that form from two properties Persistence
Mechanics already imposes on a readout weight `g(r)` of a component of modulus `r`:

* **Additivity and invariance.** The ledger is additive over components (`PMSubstrate.Impedance`:
  signed additivity), and the total weight of a state cannot depend on which orthonormal basis the
  substrate's unitary update happens to use. In particular, the real rotation in the plane of two
  components that carries `(x, y)` to `(√(x²+y²), 0)` (`rotation_to_axis`) leaves the total weight
  unchanged: `g x + g y = g √(x²+y²) + g 0`.
* **Monotonicity.** A larger amplitude never reads less (`MonotoneOn g (Ici 0)`).

* `hh_add`: with `hh t = g(√t) − g 0`, invariance is Cauchy's equation `hh (s+t) = hh s + hh t` on
  `[0, ∞)`.
* `hh_nat`, `hh_rat`: so `hh` is linear on nonnegative rationals.
* `hh_linear`: monotonicity extends this to all `t ≥ 0`: `hh t = t · hh 1`.
* `readout_rule`: `g r = g 0 + (g 1 − g 0) r²`.
* `born`: with `g 0 = 0` (an empty component reads nothing) and `g 1 = 1` (a normalized carrier
  reads one), `g r = r²`.

This is the finite, two-component core of Gleason-type arguments; no continuity is assumed,
monotonicity suffices.
-/

noncomputable section
namespace PMAction.ReadoutRule
open Real Set

/-- **The rotation to the axis.** For `r = √(x²+y²) > 0`, the rotation with `cos = x/r`,
`sin = y/r` is orthogonal and carries `(x, y)` to `(r, 0)`. -/
theorem rotation_to_axis (x y : ℝ) (hr : 0 < √(x ^ 2 + y ^ 2)) :
    (x / √(x ^ 2 + y ^ 2)) ^ 2 + (y / √(x ^ 2 + y ^ 2)) ^ 2 = 1 ∧
      x / √(x ^ 2 + y ^ 2) * x + y / √(x ^ 2 + y ^ 2) * y = √(x ^ 2 + y ^ 2) ∧
      -(y / √(x ^ 2 + y ^ 2)) * x + x / √(x ^ 2 + y ^ 2) * y = 0 := by
  have hs : √(x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 := sq_sqrt (by positivity)
  set r := √(x ^ 2 + y ^ 2)
  have hne : r ≠ 0 := hr.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, ← hs, div_self (pow_ne_zero 2 hne)]
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hne]
    nlinarith [hs]
  · ring

variable (g : ℝ → ℝ)

/-- The weight shifted to vanish at zero, as a function of the squared modulus. -/
def hh (t : ℝ) : ℝ := g (√t) - g 0

theorem hh_zero : hh g 0 = 0 := by simp [hh]

variable (hpy : ∀ x y, 0 ≤ x → 0 ≤ y → g x + g y = g (√(x ^ 2 + y ^ 2)) + g 0)

include hpy in
/-- **Cauchy's equation.** -/
theorem hh_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : hh g (s + t) = hh g s + hh g t := by
  have h := hpy (√s) (√t) (sqrt_nonneg s) (sqrt_nonneg t)
  rw [sq_sqrt hs, sq_sqrt ht] at h
  unfold hh
  linarith

include hpy in
theorem hh_nat (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : hh g (n * t) = n * hh g t := by
  induction n with
  | zero => simp [hh_zero]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, hh_add g hpy _ _ (by positivity) ht, ih]
    ring

include hpy in
theorem hh_rat (m N : ℕ) (hN : 0 < N) : hh g (m / N) = (m / N) * hh g 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have e1 := hh_nat g hpy N ((m : ℝ) / N) (by positivity)
  rw [show (N : ℝ) * (m / N) = m by field_simp] at e1
  have e2 := hh_nat g hpy m 1 zero_le_one
  rw [mul_one] at e2
  field_simp
  linarith

variable (hg : MonotoneOn g (Ici 0))

include hg in
theorem hh_mono {a b : ℝ} (hab : a ≤ b) : hh g a ≤ hh g b := by
  have h := hg (mem_Ici.mpr (sqrt_nonneg a)) (mem_Ici.mpr (sqrt_nonneg b)) (sqrt_le_sqrt hab)
  unfold hh
  linarith

include hpy hg in
/-- **Linearity in the squared modulus.** -/
theorem hh_linear (t : ℝ) (ht : 0 ≤ t) : hh g t = t * hh g 1 := by
  have h1nn : 0 ≤ hh g 1 := by
    have := hh_mono g hg (zero_le_one : (0 : ℝ) ≤ 1)
    rw [hh_zero] at this
    exact this
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * |hh g t - t * hh g 1| ≤ hh g 1 := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
    have hNt : 0 ≤ (N : ℝ) * t := by positivity
    have hm1 : (⌊(N : ℝ) * t⌋₊ : ℝ) ≤ N * t := Nat.floor_le hNt
    have hm2 : (N : ℝ) * t < ⌊(N : ℝ) * t⌋₊ + 1 := Nat.lt_floor_add_one _
    have hk1 : (N : ℝ) * t ≤ ⌈(N : ℝ) * t⌉₊ := Nat.le_ceil _
    have hk2 : (⌈(N : ℝ) * t⌉₊ : ℝ) < N * t + 1 := Nat.ceil_lt_add_one hNt
    have lo : (⌊(N : ℝ) * t⌋₊ : ℝ) * hh g 1 ≤ N * hh g t := by
      have hmono := hh_mono g hg (show (⌊(N : ℝ) * t⌋₊ : ℝ) / N ≤ t by
        rw [div_le_iff₀ hNr]; linarith)
      rw [hh_rat g hpy _ N hN] at hmono
      calc (⌊(N : ℝ) * t⌋₊ : ℝ) * hh g 1 = N * ((⌊(N : ℝ) * t⌋₊ / N) * hh g 1) := by
            field_simp
        _ ≤ N * hh g t := mul_le_mul_of_nonneg_left hmono hNr.le
    have hi : (N : ℝ) * hh g t ≤ (⌈(N : ℝ) * t⌉₊ : ℝ) * hh g 1 := by
      have hmono := hh_mono g hg (show t ≤ (⌈(N : ℝ) * t⌉₊ : ℝ) / N by
        rw [le_div_iff₀ hNr]; linarith)
      rw [hh_rat g hpy _ N hN] at hmono
      calc (N : ℝ) * hh g t ≤ N * ((⌈(N : ℝ) * t⌉₊ / N) * hh g 1) :=
            mul_le_mul_of_nonneg_left hmono hNr.le
        _ = (⌈(N : ℝ) * t⌉₊ : ℝ) * hh g 1 := by field_simp
    have habs : |(N : ℝ) * (hh g t - t * hh g 1)| ≤ hh g 1 := by
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg (show (0 : ℝ) ≤ ⌊(N : ℝ) * t⌋₊ - N * t + 1 by linarith) h1nn]
      · nlinarith [mul_nonneg (show (0 : ℝ) ≤ N * t + 1 - ⌈(N : ℝ) * t⌉₊ by linarith) h1nn]
    rwa [abs_mul, abs_of_pos hNr] at habs
  by_contra hne
  have hd : 0 < |hh g t - t * hh g 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (hh g 1 / |hh g t - t * hh g 1|)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg h1nn hd.le) hN
    exact_mod_cast this
  have h1 := key N hNpos
  rw [div_lt_iff₀ hd] at hN
  linarith

include hpy hg in
/-- **The readout rule.** `g r = g 0 + (g 1 − g 0) r²` for `r ≥ 0`. -/
theorem readout_rule (r : ℝ) (hr : 0 ≤ r) : g r = g 0 + (g 1 - g 0) * r ^ 2 := by
  have h := hh_linear g hpy hg (r ^ 2) (by positivity)
  unfold hh at h
  rw [sqrt_sq hr, sqrt_one] at h
  linarith

include hpy hg in
/-- **Born.** With `g 0 = 0` and `g 1 = 1`, the readout weight is `r²`. -/
theorem born (h0 : g 0 = 0) (h1 : g 1 = 1) (r : ℝ) (hr : 0 ≤ r) : g r = r ^ 2 := by
  rw [readout_rule g hpy hg r hr, h0, h1]
  ring

end PMAction.ReadoutRule
