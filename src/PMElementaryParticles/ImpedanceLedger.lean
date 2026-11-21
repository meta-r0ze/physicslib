import PMElementaryParticles.PhaseToRecord
import PersistenceMechanics.ImpedanceMatching

/-!
# The certified converter is an impedance-matching interface

Nested Rule 3 (`PersistenceMechanics.ImpedanceMatching`) on the K-Automaton. The certified
converter (`PhaseToRecord.converter`, the coherent encounter) sends the phase input to a pass
outcome and a flip (mismatch) outcome.

* `plus_probability`: the pass probability is `1 − flag x`.
* `converter_ledger`: pass plus flip probability is one. This is the conserved ledger
  `P r² + P T = P` at `P = 1`.
* `converter_is_interface`: the flip probability is the reflected fraction `r²` of the
  positive-real interface with source `1 − s` and load `1 + s`, where `s = |sin(x/2)|`;
  the pass probability is its transmission `T`. The exact record bit `x = π` is `s = 1`,
  the total-reflection limit (zero source impedance).
* `period_ledger`: over a period's encounters, reflected plus transmitted load is the
  number of encounters.
* `zero_reserve_no_registration`, `toll_needs_reserve`: with zero reserve every encounter
  transmits fully, so nothing registers. A protocol that meets the Toll floor (at least
  one registration) therefore needs a positive reflected-load reserve: the Margin reserve.

Reflected load is registration (a flip is a receiver flag, `PhaseToRecord.expected_receiver_flag`).
So Rule 3 on the machine is the converter's ledger plus the Margin reserve. This module does
not choose a reserve or a phase.
-/

noncomputable section
namespace PMElementaryParticles.ImpedanceLedger

open PMAction PMElementaryParticles.PhaseToRecord PersistenceMechanics.ImpedanceMatching
open Matrix

/-- `|1 + e^{iθ}|² = 4 (1 − flag θ)`. -/
theorem normSq_one_add_exp (θ : ℝ) :
    Complex.normSq (1 + Complex.exp ((θ : ℂ) * Complex.I)) =
      4 * (1 - DiagonalReadout.flag θ) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    Complex.one_im, Complex.add_im, Complex.mul_im]
  unfold DiagonalReadout.flag
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The pass (plus) output probability is `1 − flag x`. -/
theorem plus_probability (x : ℝ) :
    Complex.normSq ((converter x *ᵥ phaseInput) (.inl ())) =
      1 - DiagonalReadout.flag x := by
  rw [converter_plus, Complex.normSq_div, normSq_one_add_exp]
  norm_num [DiagonalReadout.flag]

/-- **The converter's ledger.** Pass plus flip probability is one. -/
theorem converter_ledger (x : ℝ) :
    Complex.normSq ((converter x *ᵥ phaseInput) (.inr ())) +
      Complex.normSq ((converter x *ᵥ phaseInput) (.inl ())) = 1 := by
  rw [minus_probability, plus_probability]
  ring

/-- **The converter is a positive-real interface.** With `s = |sin(x/2)|`, source `1 − s` and
load `1 + s`: the flip probability is the reflected fraction and the pass probability is the
transmission. -/
theorem converter_is_interface (x : ℝ) :
    reflection (1 - |Real.sin (x / 2)|) (1 + |Real.sin (x / 2)|) ^ 2 =
        Complex.normSq ((converter x *ᵥ phaseInput) (.inr ())) ∧
      transmission (1 - |Real.sin (x / 2)|) (1 + |Real.sin (x / 2)|) =
        Complex.normSq ((converter x *ᵥ phaseInput) (.inl ())) := by
  constructor
  · rw [realize, sq_abs, ← DiagonalReadout.flag_eq_sin_sq, minus_probability]
  · unfold transmission
    rw [realize, sq_abs, ← DiagonalReadout.flag_eq_sin_sq, plus_probability]

/-- Reflected load of a period's encounters at phases `xs`. -/
def reflectedLoad (xs : List ℝ) : ℝ := (xs.map DiagonalReadout.flag).sum

/-- Transmitted load of a period's encounters. -/
def transmittedLoad (xs : List ℝ) : ℝ := (xs.map fun x => 1 - DiagonalReadout.flag x).sum

/-- **The period ledger.** Reflected plus transmitted load is the number of encounters. -/
theorem period_ledger (xs : List ℝ) :
    reflectedLoad xs + transmittedLoad xs = xs.length := by
  induction xs with
  | nil => simp [reflectedLoad, transmittedLoad]
  | cons x xs ih =>
    unfold reflectedLoad transmittedLoad at *
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

theorem reflectedLoad_nonneg (xs : List ℝ) : 0 ≤ reflectedLoad xs :=
  List.sum_nonneg fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
    exact (DiagonalReadout.flag_bounds x).1

/-- **Zero reserve: nothing registers.** If the reflected load fits a zero reserve, every
encounter transmits fully. -/
theorem zero_reserve_no_registration (xs : List ℝ) (h : reflectedLoad xs ≤ 0) :
    ∀ x ∈ xs, DiagonalReadout.flag x = 0 := by
  intro x hx
  have hle : DiagonalReadout.flag x ≤ reflectedLoad xs := by
    unfold reflectedLoad
    refine List.single_le_sum (fun y hy => ?_) _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
    exact (DiagonalReadout.flag_bounds z).1
  linarith [(DiagonalReadout.flag_bounds x).1]

/-- **The Toll floor needs a reserve.** A period with at least one registering encounter has
positive reflected load, so Rule 3 admits it only with a positive reserve (the Margin
reserve). -/
theorem toll_needs_reserve (xs : List ℝ) (h : ∃ x ∈ xs, DiagonalReadout.flag x ≠ 0) :
    0 < reflectedLoad xs := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hx, hne⟩ := h
  exact hne (zero_reserve_no_registration xs hc x hx)

end PMElementaryParticles.ImpedanceLedger
