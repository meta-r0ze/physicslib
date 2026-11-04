import PMConstants.CarrierActions
import PMAction.InvolutionComparison
import PMAction.SpatialComparison

/-!
# The marker-free comparison identity on the actual packet permutations

Weak sign exchange and colour-axis exchange are involutions on the existing
packet. Paper II's reconstructed phase therefore has an exact comparison
circuit with no independent branch Z marker. Nine forward spectral-phase calls
give a construction, not a minimum primitive price. The additional comparison
branch, controlled packet gate, its preparation, admission and location are
still physical contracts; this module does not identify them with spare walls.
-/

noncomputable section
namespace PMConstants.CarrierPhaseComparison
open Matrix PMAction PMAction.InvolutionComparison

theorem weak_involutive : Function.Involutive CarrierActions.weak :=
  CarrierActions.weak.left_inv

theorem colour_involutive (a b : Fin 3) : Function.Involutive (CarrierActions.colour a b) :=
  (CarrierActions.colour a b).left_inv

/-- Applies to the native weak/colour involutions above, without fitting any parameter. -/
theorem packet_comparison (e : Equiv.Perm CarrierActions.Packet) (he : Function.Involutive e)
    (p t : ℝ) :
    (forwardStage (e.permMatrix ℂ)
      (Complex.exp (-(RootTransferPhase.gap p * t : ℝ) * Complex.I))).prod =
        CoherentComparisonRepair.compare (RootTransferPhase.phase e p t) := by
  rw [reconstructed e he]
  exact forward_correct _ (RootTransferPhase.permutation_square e he) _

/-- The comparison branches can be allocated to two supplied spatial cells.
This retains the packet's internal wall/chirality label and gives exact readout
on all ambient amplitudes. It does not supply clean cells or their event prices. -/
theorem spatial_packet_comparison {X : Type*} [Fintype X] [DecidableEq X]
    (live record : X) (h : live ≠ record) (e : Equiv.Perm CarrierActions.Packet)
    (he : Function.Involutive e) (z : ℂ) :
    NativeObservation.Obs (SpatialComparison.encoding live record)
      (SpatialComparison.circuit live record h e z)
      (CoherentComparisonRepair.compare (phase (e.permMatrix ℂ) z)) :=
  SpatialComparison.circuit_observed live record h e he z

end PMConstants.CarrierPhaseComparison
