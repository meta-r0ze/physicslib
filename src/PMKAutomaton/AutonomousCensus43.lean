import PMKAutomaton.AutonomousCensus

/-!
# Exact 43-site static-mirror witness and its failed robustness test

The supplied single marker gives an autonomous native orbit with 86 ticks,
2 reversals and zero lifted displacement. Its mean is one reversal per 43
root updates. This is a candidate count, not an electron identification.
The orbit visits the whole ring, so it is not a proof of bounded localization
on an infinite substrate. Removing its sole marker changes the mean to zero
and gives a circulating packet: the requested one-marker robustness fails.
These concrete certificates use kernel decision, not the Python census.
-/
namespace PMKAutomaton.AutonomousRing

def mirror43 : OnePacket 43 := ((0,false),fun x => decide (x = 0))
def clear43 : OnePacket 43 := ((0,false),fun _ => false)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mirror43_return (b : Bool) : (packetStep (explicitRule 0 b))^[86] mirror43 = mirror43 := by
  rw [static_packet_step]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mirror43_minimal (b : Bool) : ∀ t : Fin 86, 0 < t.val →
    (packetStep (explicitRule 0 b))^[t.val] mirror43 ≠ mirror43 := by
  rw [static_packet_step]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mirror43_reversals (b : Bool) : nativeReversals (explicitRule 0 b) mirror43 86 = 2 := by
  unfold nativeReversals
  rw [static_packet_step]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mirror43_rest (b : Bool) : displacement (explicitRule 0 b) mirror43 86 = 0 := by
  unfold displacement
  rw [static_packet_step]
  decide +kernel

theorem mirror43_average (b : Bool) : average (nativeReversals (explicitRule 0 b) mirror43 86) 86 = 1 := by
  rw [mirror43_reversals]
  norm_num [average,PMSubstrate.E8Values.Delta,PMSubstrate.E8Values.Delta_eq]

theorem remove_mirror : perturbMarker mirror43 0 = clear43 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clear43_observations (b : Bool) :
    (packetStep (explicitRule 0 b))^[43] clear43 = clear43 ∧
    nativeReversals (explicitRule 0 b) clear43 43 = 0 ∧
    displacement (explicitRule 0 b) clear43 43 = 43 := by
  unfold nativeReversals displacement
  rw [static_packet_step]
  decide +kernel

theorem mirror43_resting (b : Bool) : RestingAtRate (explicitRule 0 b) mirror43 1 :=
  ⟨86,by norm_num,mirror43_return b,mirror43_rest b,mirror43_average b⟩

theorem mirror43_not_robust (b : Bool) : ¬ MarkerRateRobust (explicitRule 0 b) mirror43 1 := by
  intro h
  have hp := h 0 0
  rw [Function.iterate_zero_apply,remove_mirror] at hp
  obtain ⟨t,_,_,hr⟩ := hp
  have hz : nativeReversals (explicitRule 0 b) clear43 t = 0 := cleared_reversals b 0 t
  rw [hz] at hr
  norm_num [average] at hr

end PMKAutomaton.AutonomousRing
