import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Exact versions of reversible remainder storage and a chosen real impedance
interface law. These do not assert that the vacuum realizes this interface. -/
noncomputable section
namespace PMConstants.Interface

def encode (k n : ℕ) : ℕ × ℕ := (n/k, n%k)

def decode (k : ℕ) (p : ℕ × ℕ) : ℕ := k*p.1+p.2

theorem decode_encode (k n : ℕ) : decode k (encode k n) = n := by
  simpa [decode, encode, Nat.add_comm] using Nat.mod_add_div n k

theorem encoding_injective (k : ℕ) : Function.Injective (encode k) := by
  intro a b h
  have := congrArg (decode k) h
  simpa [decode_encode] using this

theorem remainder_bounded {k : ℕ} (hk : 0 < k) (n : ℕ) : (encode k n).2 < k :=
  Nat.mod_lt n hk

theorem forgetting_remainder_loses_information :
    (4 : ℕ)/3 = 5/3 ∧ (4 : ℕ) ≠ 5 := by norm_num

def reflection (source load : ℝ) : ℝ := (load-source)/(load+source)

def transmission (source load : ℝ) : ℝ := 1-(reflection source load)^2

theorem reflection_zero_iff {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    reflection source load = 0 ↔ load = source := by
  simp [reflection, div_eq_zero_iff, ne_of_gt (add_pos hl hs), sub_eq_zero]

theorem transmission_formula {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    transmission source load = 4*source*load/(load+source)^2 := by
  have hn : load+source ≠ 0 := ne_of_gt (add_pos hl hs)
  unfold transmission reflection
  field_simp [hn]
  ring

theorem transmission_bounds {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    0 < transmission source load ∧ transmission source load ≤ 1 := by
  constructor
  · rw [transmission_formula hs hl]
    positivity
  · unfold transmission
    nlinarith [sq_nonneg (reflection source load)]

theorem perfect_matching_iff {source load : ℝ} (hs : 0 < source) (hl : 0 < load) :
    transmission source load = 1 ↔ load = source := by
  have h : transmission source load = 1 ↔ (reflection source load)^2 = 0 := by
    unfold transmission
    constructor <;> intro hx <;> linarith
  rw [h, sq_eq_zero_iff, reflection_zero_iff hs hl]

end PMConstants.Interface
