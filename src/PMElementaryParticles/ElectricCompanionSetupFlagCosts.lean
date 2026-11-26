import PMElementaryParticles.ElectricCompanionBank

/-!
# Primitive state flags of the companion's six-root setup

Follow the supplied occupied coordinate seed through the actual glued
crossing word. The finite comparison support is the union of the before
and after root labels for the visit. Coincident paths are summed as
amplitudes before taking the squared norm. The sum of these flags prices
the setup under one registration per primitive comparison flag.
-/

noncomputable section
namespace PMElementaryParticles.ElectricCompanionSetupFlagCosts

open Matrix PMAction GluedRegister
open ElectricCompanionBank

private def seedPath (wall : Bool) (n : ℕ) (a : Fin 8) : Wt × Wt :=
  let v := carrier (seedClass wall) a
  (crossingWord.take n).foldl
    (fun p r => reflectPair (HeavyCrossingCost.rootPair r) p) (v, v)

/-- On the supplied seed only the third root is needed for the active
wall. The static-wall seed uses the second root followed by the third. -/
def shortSetupWord (wall : Bool) : List HeavyCrossingCost.Instruction :=
  if wall then [(2, 6, 6)] else [(0, 6, 6), (2, 6, 6)]

set_option maxRecDepth 4096 in
/-- Removing the idle visits preserves the endpoint of every basis label
with nonzero amplitude in the supplied coordinate-zero seed. -/
theorem short_setup_on_seed_support : ∀ (wall : Bool) (a : Fin 8),
    carrier (seedClass wall) a 0 ≠ 0 →
      let v := carrier (seedClass wall) a
      (shortSetupWord wall).foldl
        (fun p r => reflectPair (HeavyCrossingCost.rootPair r) p) (v, v) =
          runCrossing (v, v) := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The static-wall word also prepares the active-wall seed. One fixed
two-root setup can serve both walls, with the first visit idle on the active seed. -/
theorem common_setup_on_seed_support : ∀ (wall : Bool) (a : Fin 8),
    carrier (seedClass wall) a 0 ≠ 0 →
      let v := carrier (seedClass wall) a
      (shortSetupWord false).foldl
        (fun p r => reflectPair (HeavyCrossingCost.rootPair r) p) (v, v) =
          runCrossing (v, v) := by
  decide +kernel

private def visitSupport (wall : Bool) (visit : Fin 6) : Finset (Wt × Wt) :=
  (Finset.univ.image (seedPath wall visit.val)) ∪
    (Finset.univ.image (seedPath wall (visit.val + 1)))

private def coefficient (wall : Bool) (n : ℕ) (p : Wt × Wt) : ℤ :=
  ∑ a : Fin 8, if seedPath wall n a = p then carrier (seedClass wall) a 0 else 0

private def delta (wall : Bool) (visit : Fin 6) (p : Wt × Wt) : ℤ :=
  coefficient wall (visit.val + 1) p - coefficient wall visit.val p

private def visitState (wall : Bool) (visit : Fin 6) (after : Bool) :
    ↥(visitSupport wall visit) → ℂ :=
  fun p => CarrierParity.scale *
    (coefficient wall (if after then visit.val + 1 else visit.val) p : ℂ)

def visitFlag (wall : Bool) (visit : Fin 6) : ℝ :=
  CommonResponse.linkFlag (1 : Matrix ↥(visitSupport wall visit) _ ℂ)
    (visitState wall visit false) (visitState wall visit true)

private def jumpSq (wall : Bool) (visit : Fin 6) : ℤ :=
  ∑ p : ↥(visitSupport wall visit), (delta wall visit p) ^ 2

private theorem flag_cast (wall : Bool) (visit : Fin 6) :
    visitFlag wall visit = (jumpSq wall visit : ℝ) / 32 := by
  have hs : Complex.normSq CarrierParity.scale = (1 / 8 : ℝ) := by
    have h := CarrierParity.scale_sq
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at h
    simpa using congrArg Complex.re h
  have hd : ∀ p : ↥(visitSupport wall visit),
      (visitState wall visit true - visitState wall visit false) p =
        CarrierParity.scale * (delta wall visit p : ℂ) := by
    intro p
    simp [visitState, delta, mul_sub]
  have hsq (p : ↥(visitSupport wall visit)) :
      Complex.normSq (delta wall visit p : ℂ) = (delta wall visit p : ℝ) ^ 2 := by
    simp [Complex.normSq_apply, pow_two]
  rw [visitFlag, CommonResponse.linkFlag, Matrix.one_mulVec, LinkExpansion.nsq_eq]
  simp_rw [hd, Complex.normSq_mul, hs, hsq]
  rw [← Finset.mul_sum]
  simp only [jumpSq, Int.cast_sum, Int.cast_pow]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem jump_certificate : ∀ (wall : Bool) (j : Fin 6),
    jumpSq wall j = (if wall then ![0, 0, 16, 0, 0, 0] else ![0, 16, 8, 0, 0, 0]) j := by
  decide +kernel

/-- The third root moves the whole active-wall seed. On the static wall
the second and third roots have flags one half and one quarter. -/
theorem primitive_setup_flags (wall : Bool) (j : Fin 6) :
    visitFlag wall j =
      (if wall then ![0, 0, 1 / 2, 0, 0, 0] else ![0, 1 / 2, 1 / 4, 0, 0, 0]) j := by
  rw [flag_cast, jump_certificate]
  cases wall <;> fin_cases j <;> norm_num

theorem primitive_setup_sum (wall : Bool) :
    ∑ j : Fin 6, visitFlag wall j = if wall then 1 / 2 else 3 / 4 := by
  simp_rw [primitive_setup_flags]
  cases wall <;> norm_num [Fin.sum_univ_succ]

/-- An equal active/static population contributes the average setup flag
when each slot undergoes its corresponding prepared setup. -/
theorem equal_slot_setup_sum :
    ((∑ j : Fin 6, visitFlag true j) + ∑ j : Fin 6, visitFlag false j) / 2 = 5 / 8 := by
  rw [primitive_setup_sum, primitive_setup_sum]
  norm_num

end PMElementaryParticles.ElectricCompanionSetupFlagCosts
