import PMAtoms.NuclearLedger
import Mathlib.Tactic

/-!
# Certified numerics over the E8 primitives

Reusable infrastructure for proving **rational enclosures** of expressions built
from the substrate primitives (`π`, `proton`, `neutron`, the packing weight) and
the nuclear power/roots `A^(2/3)`, `√(A^(2/3)+1)`.  It is what lets a downstream
configuration (a specific nuclide's mass, lifetime, width) be *proved out*
mechanically instead of by hand.

* `cbrt` — an `O(log n)` integer cube root, with spec `k³ ≤ n < (k+1)³`.
* `rpow23Lo`/`rpow23Hi`, `sqrtLo`/`sqrtHi` — computable `ℚ` bounds at `d` digits,
  with `rpow23_bounds_auto` / `sqrt_add_one_bounds_auto`.
* `mul_bounds` / `inv_bounds` — the interval-arithmetic primitives.

All bounds are E8 statements; measured values are the comparison, never inputs.
-/

noncomputable section
namespace PMAtoms

/-! ## Integer cube root -/

/-- Binary-search integer cube root (`O(log n)` evaluation). -/
def cbrtAux (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := lo + (hi - lo) / 2
        if mid ^ 3 ≤ n then cbrtAux n fuel mid hi else cbrtAux n fuel lo mid

/-- Integer cube root: greatest `k` with `k³ ≤ n`. -/
def cbrt (n : ℕ) : ℕ := cbrtAux n (n + 1) 0 (n + 1)

theorem cbrtAux_spec (n : ℕ) : ∀ fuel lo hi, hi - lo ≤ fuel → lo ^ 3 ≤ n → n < hi ^ 3 →
    (cbrtAux n fuel lo hi) ^ 3 ≤ n ∧ n < (cbrtAux n fuel lo hi + 1) ^ 3 := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hf hlo hhi
      simp only [cbrtAux]
      have : hi ≤ lo := by omega
      have h3 : hi ^ 3 ≤ lo ^ 3 := Nat.pow_le_pow_left this 3
      omega
  | succ fuel ih =>
      intro lo hi hf hlo hhi
      simp only [cbrtAux]
      split
      · rename_i h
        exact ⟨hlo, by
          have : hi ^ 3 ≤ (lo + 1) ^ 3 := Nat.pow_le_pow_left h 3
          omega⟩
      · rename_i h
        have hx : 1 ≤ (hi - lo) / 2 := Nat.div_pos (by omega) (by norm_num)
        have hxlt : (hi - lo) / 2 < hi - lo := Nat.div_lt_self (by omega) (by norm_num)
        split
        · rename_i hm
          have hsub : hi - (lo + (hi - lo) / 2) ≤ fuel := by omega
          exact ih _ _ hsub hm hhi
        · rename_i hm
          have hsub : lo + (hi - lo) / 2 - lo ≤ fuel := by omega
          exact ih _ _ hsub hlo (not_le.mp hm)

theorem cbrt_spec (n : ℕ) : cbrt n ^ 3 ≤ n ∧ n < (cbrt n + 1) ^ 3 := by
  have hhi : n < (n + 1) ^ 3 := by
    have h1 : n < n + 1 := Nat.lt_succ_self n
    have h2 : n + 1 ≤ (n + 1) ^ 3 := le_self_pow (by omega) (by norm_num)
    omega
  exact cbrtAux_spec n (fuel := n + 1) (lo := 0) (hi := n + 1) (by omega)
    (by positivity) hhi

theorem cbrt_cube_le (n : ℕ) : cbrt n ^ 3 ≤ n := (cbrt_spec n).1

theorem lt_cbrt_succ_cube (n : ℕ) : n < (cbrt n + 1) ^ 3 := (cbrt_spec n).2

/-! ## Computable rational bounds -/

/-- Rational lower bound `≤ a^(2/3)` at `d` decimal digits. -/
def rpow23Lo (a d : ℕ) : ℚ := (cbrt (a ^ 2 * 10 ^ (3 * d)) : ℚ) / 10 ^ d

/-- Rational upper bound `≥ a^(2/3)` at `d` decimal digits. -/
def rpow23Hi (a d : ℕ) : ℚ := ((cbrt (a ^ 2 * 10 ^ (3 * d)) : ℚ) + 1) / 10 ^ d

/-- Rational lower bound `≤ √(a^(2/3)+1)` at `d` digits. -/
def sqrtLo (a d : ℕ) : ℚ :=
  (Nat.sqrt ((cbrt (a ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d) : ℚ) / 10 ^ d

/-- Rational upper bound `≥ √(a^(2/3)+1)` at `d` digits. -/
def sqrtHi (a d : ℕ) : ℚ :=
  ((Nat.sqrt ((cbrt (a ^ 2 * 10 ^ (3 * d)) + 1 + 10 ^ d) * 10 ^ d) + 1 : ℕ) : ℚ) / 10 ^ d

/-- Rational bounds on `a^(2/3)` from cube bounds on `a^2`. -/
lemma rpow23_bounds {a : ℕ} {lo hi : ℝ}
    (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi)
    (hlo : lo ^ 3 ≤ (a : ℝ) ^ 2) (hhi : (a : ℝ) ^ 2 ≤ hi ^ 3) :
    lo ≤ (a : ℝ) ^ ((2 : ℝ) / 3) ∧ (a : ℝ) ^ ((2 : ℝ) / 3) ≤ hi := by
  have ha : 0 ≤ (a : ℝ) := by positivity
  have hrt : (a : ℝ) ^ ((2 : ℝ) / 3) = ((a : ℝ) ^ (2 : ℝ)) ^ ((3 : ℕ)⁻¹ : ℝ) := by
    rw [show ((2 : ℝ) / 3) = 2 * ((3 : ℕ)⁻¹ : ℝ) by norm_num, Real.rpow_mul ha]
  have hbase : (a : ℝ) ^ (2 : ℝ) = (a : ℝ) ^ 2 := Real.rpow_natCast (a : ℝ) 2
  constructor
  · rw [hrt, hbase, ← Real.pow_rpow_inv_natCast hlo0 (by norm_num : (3 : ℕ) ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hlo (by norm_num)
  · rw [hrt, hbase, ← Real.pow_rpow_inv_natCast hhi0 (by norm_num : (3 : ℕ) ≠ 0)]
    exact Real.rpow_le_rpow (by positivity) hhi (by norm_num)

theorem rpow23_bounds_auto (a d : ℕ) :
    (rpow23Lo a d : ℝ) ≤ (a : ℝ) ^ ((2 : ℝ) / 3) ∧
      (a : ℝ) ^ ((2 : ℝ) / 3) ≤ (rpow23Hi a d : ℝ) := by
  have hN : ((cbrt (a ^ 2 * 10 ^ (3 * d)) : ℕ) : ℝ) ^ 3 ≤ ((a ^ 2 * 10 ^ (3 * d) : ℕ) : ℝ) := by
    exact_mod_cast cbrt_cube_le (a ^ 2 * 10 ^ (3 * d))
  have hM : ((a ^ 2 * 10 ^ (3 * d) : ℕ) : ℝ) < ((cbrt (a ^ 2 * 10 ^ (3 * d)) : ℕ) + 1) ^ 3 := by
    exact_mod_cast lt_cbrt_succ_cube (a ^ 2 * 10 ^ (3 * d))
  have hpow : ((10 : ℝ) ^ d) ^ 3 = (10 : ℝ) ^ (3 * d) := by
    rw [← pow_mul, Nat.mul_comm]
  refine rpow23_bounds (a := a) ?_ ?_ ?_ ?_
  · unfold rpow23Lo; positivity
  · unfold rpow23Hi; positivity
  · unfold rpow23Lo
    push_cast
    rw [div_pow, hpow, div_le_iff₀ (by positivity)]
    calc ((cbrt (a ^ 2 * 10 ^ (3 * d)) : ℕ) : ℝ) ^ 3
        ≤ (((a ^ 2 * 10 ^ (3 * d) : ℕ)) : ℝ) := hN
      _ = (a : ℝ) ^ 2 * (10 : ℝ) ^ (3 * d) := by push_cast; ring
  · unfold rpow23Hi
    push_cast
    rw [div_pow, hpow, le_div_iff₀ (by positivity)]
    calc (a : ℝ) ^ 2 * (10 : ℝ) ^ (3 * d)
        = (((a ^ 2 * 10 ^ (3 * d) : ℕ)) : ℝ) := by push_cast; ring
      _ ≤ ((cbrt (a ^ 2 * 10 ^ (3 * d)) : ℕ) + 1) ^ 3 := le_of_lt hM

/-- `√(u+1)` bounds from rational bounds on `u+1`. -/
lemma sqrt_add_one_bounds {u sl sh : ℝ} (hsl : 0 ≤ sl) (hsh : 0 ≤ sh)
    (h1 : sl ^ 2 ≤ u + 1) (h2 : u + 1 ≤ sh ^ 2) :
    sl ≤ Real.sqrt (u + 1) ∧ Real.sqrt (u + 1) ≤ sh := by
  have hy : 0 ≤ u + 1 := le_trans (sq_nonneg sl) h1
  exact ⟨(Real.le_sqrt hsl hy).mpr h1, Real.sqrt_le_iff.mpr ⟨hsh, h2⟩⟩

theorem sqrtLo_sq (a d : ℕ) : (sqrtLo a d : ℝ) ^ 2 ≤ (rpow23Lo a d : ℝ) + 1 := by
  have hk : ((Nat.sqrt ((cbrt (a ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d) : ℕ) : ℝ) ^ 2
      ≤ ((((cbrt (a ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d : ℕ)) : ℝ) := by
    exact_mod_cast Nat.sqrt_le' ((cbrt (a ^ 2 * 10 ^ (3 * d)) + 10 ^ d) * 10 ^ d)
  push_cast at hk
  unfold sqrtLo rpow23Lo
  push_cast
  have hd : (0 : ℝ) < (10 : ℝ) ^ d := by positivity
  field_simp
  nlinarith [hk]

theorem sqrtHi_sq (a d : ℕ) : (rpow23Hi a d : ℝ) + 1 ≤ (sqrtHi a d : ℝ) ^ 2 := by
  have hk : (((Nat.sqrt ((cbrt (a ^ 2 * 10 ^ (3 * d)) + 1 + 10 ^ d) * 10 ^ d) + 1 : ℕ)) : ℝ) ^ 2
      > ((((cbrt (a ^ 2 * 10 ^ (3 * d)) + 1 + 10 ^ d) * 10 ^ d : ℕ)) : ℝ) := by
    have h := Nat.lt_succ_sqrt' ((cbrt (a ^ 2 * 10 ^ (3 * d)) + 1 + 10 ^ d) * 10 ^ d)
    rw [Nat.succ_eq_add_one] at h
    exact_mod_cast h
  push_cast at hk
  unfold sqrtHi rpow23Hi
  push_cast
  have hd : (0 : ℝ) < (10 : ℝ) ^ d := by positivity
  field_simp
  nlinarith [hk]

theorem sqrt_add_one_bounds_auto (a d : ℕ) :
    (sqrtLo a d : ℝ) ≤ Real.sqrt ((a : ℝ) ^ ((2 : ℝ) / 3) + 1) ∧
      Real.sqrt ((a : ℝ) ^ ((2 : ℝ) / 3) + 1) ≤ (sqrtHi a d : ℝ) := by
  have hu := rpow23_bounds_auto a d
  refine sqrt_add_one_bounds (u := (a : ℝ) ^ ((2 : ℝ) / 3)) ?_ ?_ ?_ ?_
  · unfold sqrtLo; positivity
  · unfold sqrtHi; positivity
  · linarith [sqrtLo_sq a d, hu.1]
  · linarith [sqrtHi_sq a d, hu.2]

/-! ## Interval-arithmetic primitives -/

/-- Product of intervals, all endpoints nonnegative. -/
lemma mul_bounds {a b c d x y : ℝ} (hx : a ≤ x) (hx' : x ≤ b) (hy : c ≤ y) (hy' : y ≤ d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul hx hy hc (le_trans ha hx),
   mul_le_mul hx' hy' (le_trans hc hy) (le_trans (le_trans ha hx) hx')⟩

/-- Reciprocal flips the interval for a positive denominator. -/
lemma inv_bounds {s slo shi : ℝ} (hs : slo ≤ s) (hs' : s ≤ shi) (hslo : 0 < slo) :
    1 / shi ≤ 1 / s ∧ 1 / s ≤ 1 / slo :=
  ⟨one_div_le_one_div_of_le (lt_of_lt_of_le hslo hs) hs',
   one_div_le_one_div_of_le hslo hs⟩

end PMAtoms
