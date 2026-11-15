import PMFlavor.TransferGraph
import PMConstants.GenerationWeak

/-!
# The label changes of one charged-current event

A charged-current event changes the protocol (for example up into down). It acts on one wall, the
reference's (`PMAction.WallChiralCurrent`, `PMConstants.CarrierActions.weak_chiral`), so it can also
change the label state: on one wall every label change is one single-wall carrier plus one glue move,
and the changes form a directed 3-cycle (`PMAction.GenerationCurrent`). On the reference's wall
(`false`, the wall of the reference background) the change `g → g − 1` uses a carrier of class
`g + 1` (`GenerationCurrent.shift_false_then_glue`).

`J κ` is the label-change matrix of one event (rows: label after, columns: label before), with
amplitude `1` for no change and `κ c` for the change that uses a carrier of class `c`.

* `entry_of_class`: the change through class `c` takes label `c − 1` to `c + 1`, with amplitude `κ c`;
  these are the three transfers of `TransferGraph` (`ends c = (c + 1, c − 1)`).
* `reverse_zero`: one event does not make the reverse change; that is the conjugate event (`Jᴴ`).
* `weak_carrier_entry`: the change through the reference's class `0` (labels `2 → 1`) uses the weak
  carrier itself (`PMConstants.GenerationWeak.weak_carrier_is_vector`, `weak_edge_false`), and it is
  the in-cycle transfer (`TransferGraph.inCycle_iff`).
* `node_entries`: the changes through classes `1` and `2` (`0 → 2` and `1 → 0`) need a spinor carrier
  (`GenerationWeak.heavy_edges_spinor`), which only the reference node supplies (`TransferGraph`).

The amplitudes `κ c` depend on where the carriers sit relative to the reference axis (off the axis:
two legs, amplitude; on the axis: one leg, probability; `NodeElimination`): `ConductionRule` gives the
in-cycle one, `TransferAmplitude` the other-wall node one; the reference-wall node one is open. So
there are two matrices, `J` for carriers off the axis and for carriers on it. If the persisting states
are the label states, the observed matrix is `J` (normalized, with the dressing); otherwise it is
`U_uᴴ J U_d`, with `U` the persistence rotation of each protocol (PMAction's wire; protocols from
PMElementaryParticles).
-/

namespace PMFlavor.EventTransfer

/-- **The label-change matrix of one event** on the reference's wall. -/
def J {R : Type*} [One R] [Zero R] (κ : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of ![![1, κ 2, 0], ![0, 1, κ 0], ![κ 1, 0, 1]]

variable {R : Type*} [One R] [Zero R] (κ : Fin 3 → R)

/-- **The change through class `c` takes label `c − 1` to `c + 1`, amplitude `κ c`.** -/
theorem entry_of_class (c : Fin 3) : J κ (c + 1) (c - 1) = κ c := by
  fin_cases c <;> rfl

/-- **The three changes are the three transfers of `TransferGraph`.** -/
theorem entry_is_transfer (c : Fin 3) :
    J κ (TransferGraph.ends c).1 (TransferGraph.ends c).2 = κ c := entry_of_class κ c

/-- **One event makes no reverse change.** -/
theorem reverse_zero (c : Fin 3) : J κ (c - 1) (c + 1) = 0 := by
  fin_cases c <;> rfl

/-- **No change keeps amplitude `1`.** -/
theorem diag_one (g : Fin 3) : J κ g g = 1 := by
  fin_cases g <;> rfl

/-- **The weak carrier's own change:** through class `0`, labels `2 → 1`, in the cycle. -/
theorem weak_carrier_entry :
    J κ 1 2 = κ 0 ∧ (TransferGraph.InCycle 0) ∧ ((2 : Fin 3) - 1 = 1) := by
  exact ⟨rfl, (TransferGraph.inCycle_iff 0).2 rfl, by decide⟩

/-- **The node changes:** through classes `1` (`0 → 2`) and `2` (`1 → 0`), out of the cycle. -/
theorem node_entries :
    J κ 2 0 = κ 1 ∧ J κ 0 1 = κ 2 ∧ ¬ TransferGraph.InCycle 1 ∧ ¬ TransferGraph.InCycle 2 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [TransferGraph.inCycle_iff]; decide
  · rw [TransferGraph.inCycle_iff]; decide

end PMFlavor.EventTransfer
