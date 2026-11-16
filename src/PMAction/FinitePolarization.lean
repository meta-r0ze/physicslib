import PMAction.PolarizationContact
import Mathlib.Data.ZMod.Basic

/-! Wrapped finite-volume longitudinal cancellation with a positive regulator.
The regulator is added to both inverse propagators, retaining every grid point.
The longitudinal regulator limit is taken after summation. The transverse
lattice remainder and its continuum comparison remain separate questions. -/
noncomputable section
namespace PMAction.FinitePolarization
open Matrix Real D4Gauge LeadingLog FiniteVertex PolarizationContact

abbrev Grid (N : ℕ) := Fin 4 → ZMod N

def momentum (N : ℕ) (a : ℝ) (k : Grid N) : Momentum :=
  fun i => (2 * Real.pi / a) * (k i).val / N

def winding (N : ℕ) (k q : Grid N) (i : Fin 4) : ℤ :=
  ((((k i).val + (q i).val) / N : ℕ) : ℤ)

lemma coordinate_wrap (N : ℕ) [NeZero N] (a : ℝ) (k q : Grid N) (i : Fin 4) :
    momentum N a k i + momentum N a q i =
      momentum N a (k+q) i + (2 * Real.pi / a) * (winding N k q i : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h := Nat.mod_add_div ((k i).val + (q i).val) N
  have hr : (((k i).val : ℝ) + (q i).val) =
      (((k i).val + (q i).val) % N : ℕ) +
        (N : ℝ) * ((((k i).val + (q i).val) / N : ℕ) : ℝ) := by exact_mod_cast h.symm
  simp only [momentum, winding, Int.cast_natCast, Pi.add_apply, ZMod.val_add]
  let c := 2 * Real.pi / a
  change c * (k i).val / (N : ℝ) + c * (q i).val / (N : ℝ) =
    c * (((k i).val + (q i).val) % N : ℕ) / (N : ℝ) +
      c * ((((k i).val + (q i).val) / N : ℕ) : ℝ)
  field_simp [hn]
  rw [hr]

def rootWinding (N : ℕ) (k q : Grid N) (r : Fin 4 → Fin 3) : ℤ :=
  ∑ i, vec r i * winding N k q i

lemma phase_wrap (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0)
    (k q : Grid N) (r : Fin 4 → Fin 3) :
    a * rk r (momentum N a k + momentum N a q) =
      a * rk r (momentum N a (k+q)) + (rootWinding N k q r : ℝ) * (2 * Real.pi) := by
  unfold rk
  simp only [Pi.add_apply]
  simp_rw [coordinate_wrap N a k q]
  simp only [mul_add, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  simp only [rootWinding, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

theorem symbol_wrap (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0) (k q : Grid N) :
    symbol a (momentum N a k + momentum N a q) = symbol a (momentum N a (k+q)) := by
  unfold symbol
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [phase_wrap N ha, Real.cos_add_int_mul_two_pi]

theorem leg_wrap (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0)
    (k q : Grid N) (v : Momentum) :
    leg a (momentum N a k + momentum N a q) (momentum N a q) v (-1) =
      leg a (momentum N a (k+q)) (momentum N a q) v (-1) := by
  unfold leg
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [phase_wrap N ha]
  have he : a * rk r (momentum N a (k+q)) +
      (rootWinding N k q r : ℝ) * (2 * Real.pi) + -1 * (a * rk r (momentum N a q) / 2) =
      (a * rk r (momentum N a (k+q)) + -1 * (a * rk r (momentum N a q) / 2)) +
        (rootWinding N k q r : ℝ) * (2 * Real.pi) := by ring
  rw [he, Real.sin_add_int_mul_two_pi]

def denominator (m a : ℝ) (k : Momentum) := m + symbol a k

lemma denominator_pos {m : ℝ} (hm : 0 < m) (a : ℝ) (k : Momentum) :
    0 < denominator m a k := by
  have hs : 0 ≤ symbol a k := by
    unfold symbol
    apply div_nonneg
    · exact Finset.sum_nonneg fun r _ => sub_nonneg.mpr (Real.cos_le_one _)
    · positivity
  unfold denominator
  linarith

theorem regulated_routing {a m : ℝ} (ha : a ≠ 0) (k q v : Momentum)
    (hk : denominator m a k ≠ 0) (hq : denominator m a (k+q) ≠ 0) :
    leg a k q q 1 * leg a k q v 1 /
        (denominator m a k * denominator m a (k+q)) -
      contact a k q q v / denominator m a k =
    leg a k q v (-1) / denominator m a k -
      leg a k q v 1 / denominator m a (k+q) := by
  rw [leg_ward ha, contact_ward ha]
  unfold denominator at *
  field_simp
  ring

/-- The longitudinal sum uses the full coordinate torus with D₄ hopping. -/
def longitudinal (N : ℕ) [NeZero N] (a m : ℝ) (q : Grid N) (v : Momentum) : ℝ :=
  (∑ k : Grid N,
      (leg a (momentum N a k) (momentum N a q) (momentum N a q) 1 *
        leg a (momentum N a k) (momentum N a q) v 1 /
        (denominator m a (momentum N a k) *
          denominator m a (momentum N a k + momentum N a q)) -
        contact a (momentum N a k) (momentum N a q) (momentum N a q) v /
          denominator m a (momentum N a k)))

/-- The full finite torus, including all massless zero-mode locations, has
zero longitudinal bubble-minus-contact sum at every positive regulator. -/
theorem finite_cancel (N : ℕ) [NeZero N] {a m : ℝ} (ha : a ≠ 0) (hm : 0 < m)
    (q : Grid N) (v : Momentum) :
    longitudinal N a m q v = 0 := by
  unfold longitudinal
  have hs (k : Grid N) : denominator m a (momentum N a k + momentum N a q) =
      denominator m a (momentum N a (k+q)) := by
    simp only [denominator, symbol_wrap N ha]
  have hk (k : Grid N) := (denominator_pos hm a (momentum N a k)).ne'
  have hterm (k : Grid N) := regulated_routing ha
    (momentum N a k) (momentum N a q) v (hk k) (by rw [hs]; exact hk _)
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp_rw [← leg_reroute, leg_wrap N ha, hs]
  exact sub_eq_zero.mpr (Equiv.sum_comp (Equiv.addRight q)
    (fun k => leg a (momentum N a k) (momentum N a q) v (-1) /
      denominator m a (momentum N a k))).symm

/-- Remove the regulator after forming the full longitudinal sum. This
Individual massless summands can remain singular in this prescription. -/
theorem zero_regulator_limit (N : ℕ) [NeZero N] {a : ℝ} (ha : a ≠ 0)
    (q : Grid N) (v : Momentum) :
    Filter.Tendsto (fun m => longitudinal N a m q v)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with m hm
  exact (finite_cancel N ha hm q v).symm

end PMAction.FinitePolarization
