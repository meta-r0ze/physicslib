import PMAction.RefreshSchedule
import PMConstants.GaugeLedgers

/-! Compatibility names; generic schedule proofs now live in Paper II. -/
namespace PMConstants.MinimalRefresh
export PMAction.RefreshSchedule
  (cost admissible cost_ge_toFinset admissible_cost_ge minimal_attained
   minimal_is_ledger strict_if_extra)
end PMConstants.MinimalRefresh
