import PMAction.ReferenceMaintenance
import PMConstants.MinimalRefresh

/-! Compatibility names; generic reversible tasks now live in Paper II. -/
namespace PMConstants.ReferenceMaintenance
export PMAction.ReferenceMaintenance
  (State event event_involutive event_commute run
   run_injective untouched run_nodup prepare Restores
   restoring_visits restores_iff_visits canonical_record canonical_restores Frame
   execute reference_preserved execute_injective live live_restored
   canonical_twice minimum_executable_cost no_record_free_reset no_closed_universal_reset)
end PMConstants.ReferenceMaintenance
