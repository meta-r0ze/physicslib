import PMCosmology.Scaling
import PMSubstrate.Impedance
import PMConstants.Partition
import Mathlib.Data.Fintype.Prod

/-! Internal finite-budget bookkeeping and the conditional cosmological load law.
The numerical multiplier's cosmological interpretation is an explicit model input. -/
noncomputable section
namespace PMCosmology.SubstrateLoad
open Finset
open PMSubstrate

abbrev CoordinateSlots := Fin baseline.dimension × Fin baseline.period

def channelStress : ℝ := 1/(2*(baseline.sectorChannels : ℝ))
def boundaryStress : ℝ := baseline.eulerCharacteristic/(baseline.period : ℝ)
def manifoldStress : ℝ := 1/Fintype.card CoordinateSlots

def payloadFraction : ℝ := (Fintype.card CoordinateSlots-1 : ℕ)/
  (Fintype.card CoordinateSlots : ℝ)

theorem coordinate_slots : Fintype.card CoordinateSlots = 172 := by
  norm_num [CoordinateSlots, baseline, Fintype.card_prod]

theorem reserved_slot_fraction : manifoldStress = 1/172 := by
  rw [manifoldStress, coordinate_slots]
  norm_num

/-- Removing one named reference slot leaves exactly 171 payload slots. -/
theorem payload_slots (origin : CoordinateSlots) :
    (univ.erase origin).card = 171 := by
  rw [card_erase_of_mem (mem_univ origin)]
  norm_num [CoordinateSlots, baseline, Fintype.card_prod]

theorem complement_of_payload : manifoldStress = 1-payloadFraction := by
  norm_num [manifoldStress, payloadFraction, CoordinateSlots, baseline, Fintype.card_prod]

/-- Direct link to the earlier paper's already formalized payload fraction. -/
theorem earlier_payload_complement : manifoldStress = 1-PMConstants.overhead := by
  rw [reserved_slot_fraction]
  norm_num [PMConstants.overhead]

theorem load_from_budget_terms : loadFactor = 1+channelStress+boundaryStress+manifoldStress := by
  norm_num [loadFactor, channelStress, boundaryStress, manifoldStress, coordinate_slots, baseline]

theorem added_term_exact : loadFactor-(1+1/32+2/43) = (1 : ℝ)/172 := by
  norm_num [loadFactor]

theorem load_spectral_relation : loadFactor = 2-scalarIndex+(9 : ℝ)/(4*43) := by
  norm_num [loadFactor, scalarIndex]

theorem revised_numerical_outputs :
    (674 : ℝ)/10*loadFactor = 502467/6880 ∧
    (832 : ℝ)/1000/loadFactor = 143104/186375 := by
  norm_num [loadFactor]

/-- Exact rational bounds certify the displayed rounding, not experimental inputs. -/
theorem output_rounding :
    (7303299 : ℝ)/100000 < (674 : ℝ)/10*loadFactor ∧
    (674 : ℝ)/10*loadFactor < (7303300 : ℝ)/100000 ∧
    (7678283 : ℝ)/10000000 < (832 : ℝ)/1000/loadFactor ∧
    (832 : ℝ)/1000/loadFactor < (7678284 : ℝ)/10000000 := by
  norm_num [loadFactor]

/-- Interval propagation assumes a fixed load factor; it does not bound model error. -/
theorem input_error_propagation {H H0 ε : ℝ} (h : |H-H0| ≤ ε) :
    |H*loadFactor-H0*loadFactor| ≤ ε*loadFactor := by
  rw [← sub_mul, abs_mul, abs_of_pos (by norm_num [loadFactor] : 0 < loadFactor)]
  exact mul_le_mul_of_nonneg_right h (by norm_num [loadFactor])

theorem clustering_error_propagation {S S0 ε : ℝ} (h : |S-S0| ≤ ε) :
    |S/loadFactor-S0/loadFactor| ≤ ε/loadFactor := by
  rw [← sub_div, abs_div, abs_of_pos (by norm_num [loadFactor] : 0 < loadFactor)]
  exact (div_le_div_iff_of_pos_right (by norm_num [loadFactor] : 0 < loadFactor)).mpr h

/-- One shared multiplier can fit four exact targets only if the product constraint holds. -/
theorem joint_targets_require_product (H0 S0 H1 S1 L : ℝ)
    (hL : L ≠ 0) (hH : H1=H0*L) (hS : S1=S0/L) : H1*S1=H0*S0 := by
  rw [hH, hS]
  field_simp

/-- These are the draft's frozen central inputs, not a statistical rejection. -/
theorem draft_central_targets_not_exact :
    (674 : ℝ)/10*((832 : ℝ)/1000) ≠ (73 : ℝ)*((776 : ℝ)/1000) := by norm_num

end PMCosmology.SubstrateLoad
