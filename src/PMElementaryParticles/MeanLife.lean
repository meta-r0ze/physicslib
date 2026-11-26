import PersistenceMechanics.HazardForm
import PersistenceMechanics.Rates

/-!
# Mean life from an EP cost rate

Scale the ledger's cost rate by the persistence hazard coefficient.
A positive hazard gives a finite mean life.
-/

noncomputable section
namespace PMElementaryParticles

open PersistenceMechanics

/-- The hazard for a supplied cost rate and coefficient. -/
def persistenceRate (β costRate : ℝ) : ℝ := β * costRate

def persistenceMeanLife (β costRate : ℝ) (h : 0 < persistenceRate β costRate) : ℝ :=
  Rates.meanLife (persistenceRate β costRate) h

theorem persistenceMeanLife_pos {β costRate : ℝ} (hβ : 0 < β) (hZ : 0 < costRate) :
    0 < persistenceMeanLife β costRate (mul_pos hβ hZ) :=
  Rates.meanLife_pos (mul_pos hβ hZ)

/-- A constant cost rate instantiates the common hazard derived from
the persistence premises. The coefficient can be zero. -/
theorem survival_from_persistence (F : ℝ → ℝ)
    (hpos : ∀ s, 0 ≤ s → 0 < F s)
    (hmul : ∀ a b, 0 ≤ a → 0 ≤ b → F (a + b) = F a * F b)
    (hanti : ∀ a b, 0 ≤ a → a ≤ b → F b ≤ F a) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ Z T : ℝ, 0 ≤ Z * T →
      F (Z * T) = Rates.survive (persistenceRate β Z) T := by
  obtain ⟨β, hβ, hF⟩ := HazardForm.continuous_form F hpos hmul hanti
  refine ⟨β, hβ, fun Z T h => ?_⟩
  rw [hF _ h, Rates.survive_eq, persistenceRate]
  congr 1
  ring

end PMElementaryParticles
