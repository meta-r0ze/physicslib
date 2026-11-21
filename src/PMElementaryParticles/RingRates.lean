import PMElementaryParticles.IsolatedReceiverTrace
import PMKAutomaton.ClockSites

set_option linter.unusedSimpArgs false

/-!
# One-site registration rates on the receiver ring

A single firing site on an `n`-site ring registers once every `n` ticks. The
packet reflects at the firing site and laps the ring; the first registration has
offset `d = (x0 - s - 1) mod n` for start site `x0` and firing site `s` (the
`Nat` formula is `(s + n - 1 - x0) % n`). Over `T` ticks the count is

`(T + n - 1 - d) / n`.

The formula is kernel-checked for `n = 3, …, 8` at `T = 43`. The general
period/remainder proof is not completed. The `n = 43, T = 43` case is checked
row by row; `ring_Delta_one` restates it with `PMSubstrate.E8Values.Delta`.
-/

noncomputable section

namespace PMElementaryParticles.RingRates

open PMElementaryParticles.IsolatedExcitation

/-- Requests with one firing site: `(true,true)` at `s`, idle elsewhere. -/
def oneFiringN (n : ℕ) (s : Fin n) : Fin n → IsolatedRequests :=
  fun x => if x = s then (true, true) else (false, false)

/-- First-registration offset: `(s + n - 1 - x0) % n`. -/
def offset (n : ℕ) (s x0 : Fin n) : ℕ := (s.val + n - 1 - x0.val) % n

/-- Predicted number of registrations in `T` ticks. -/
def predictedCount (n T : ℕ) (s x0 : Fin n) : ℕ :=
  (T + n - 1 - offset n s x0) / n

set_option maxHeartbeats 0 in
theorem formula_three : ∀ s x0 : Fin 3,
    localizedSumN 3 true (oneFiringN 3 s) x0 43 = predictedCount 3 43 s x0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem formula_four : ∀ s x0 : Fin 4,
    localizedSumN 4 true (oneFiringN 4 s) x0 43 = predictedCount 4 43 s x0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem formula_five : ∀ s x0 : Fin 5,
    localizedSumN 5 true (oneFiringN 5 s) x0 43 = predictedCount 5 43 s x0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem formula_six : ∀ s x0 : Fin 6,
    localizedSumN 6 true (oneFiringN 6 s) x0 43 = predictedCount 6 43 s x0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem formula_seven : ∀ s x0 : Fin 7,
    localizedSumN 7 true (oneFiringN 7 s) x0 43 = predictedCount 7 43 s x0 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem formula_eight : ∀ s x0 : Fin 8,
    localizedSumN 8 true (oneFiringN 8 s) x0 43 = predictedCount 8 43 s x0 := by
  decide +kernel

/-! The `n = 43, T = 43` row checks. -/

set_option maxHeartbeats 0 in
theorem row_0 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨0, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_1 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨1, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_2 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨2, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_3 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨3, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_4 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨4, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_5 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨5, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_6 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨6, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_7 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨7, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_8 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨8, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_9 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨9, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_10 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨10, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_11 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨11, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_12 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨12, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_13 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨13, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_14 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨14, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_15 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨15, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_16 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨16, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_17 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨17, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_18 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨18, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_19 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨19, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_20 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨20, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_21 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨21, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_22 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨22, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_23 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨23, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_24 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨24, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_25 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨25, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_26 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨26, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_27 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨27, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_28 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨28, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_29 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨29, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_30 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨30, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_31 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨31, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_32 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨32, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_33 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨33, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_34 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨34, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_35 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨35, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_36 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨36, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_37 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨37, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_38 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨38, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_39 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨39, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_40 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨40, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_41 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨41, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
theorem row_42 (x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 ⟨42, by norm_num⟩) x0 43 = 1 := by
  revert x0
  decide +kernel

set_option maxHeartbeats 0 in
/-- **On the 43-ring a single firing site registers exactly once in 43 ticks.** -/
theorem ring43_one (s x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 s) x0 43 = 1 := by
  fin_cases s
  · exact row_0 x0
  · exact row_1 x0
  · exact row_2 x0
  · exact row_3 x0
  · exact row_4 x0
  · exact row_5 x0
  · exact row_6 x0
  · exact row_7 x0
  · exact row_8 x0
  · exact row_9 x0
  · exact row_10 x0
  · exact row_11 x0
  · exact row_12 x0
  · exact row_13 x0
  · exact row_14 x0
  · exact row_15 x0
  · exact row_16 x0
  · exact row_17 x0
  · exact row_18 x0
  · exact row_19 x0
  · exact row_20 x0
  · exact row_21 x0
  · exact row_22 x0
  · exact row_23 x0
  · exact row_24 x0
  · exact row_25 x0
  · exact row_26 x0
  · exact row_27 x0
  · exact row_28 x0
  · exact row_29 x0
  · exact row_30 x0
  · exact row_31 x0
  · exact row_32 x0
  · exact row_33 x0
  · exact row_34 x0
  · exact row_35 x0
  · exact row_36 x0
  · exact row_37 x0
  · exact row_38 x0
  · exact row_39 x0
  · exact row_40 x0
  · exact row_41 x0
  · exact row_42 x0

/-- The same result at the substrate period `Δ = 43`. -/
theorem ring_Delta_one (s x0 : Fin PMSubstrate.E8Values.Delta) :
    localizedSumN PMSubstrate.E8Values.Delta true
      (oneFiringN PMSubstrate.E8Values.Delta s) x0 43 = 1 := by
  simpa [PMSubstrate.E8Values.Delta_eq] using ring43_one s x0

end PMElementaryParticles.RingRates
