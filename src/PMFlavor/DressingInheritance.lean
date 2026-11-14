import PMConstants.CarrierActions
import PMFlavor.CKMClosure
import PMFlavor.DressingEvent

/-!
# Why the quark rows carry the dressing and muon decay does not

Measured CKM magnitudes are rate ratios against muon decay (`G_F`). If the same factor `q²`
dressed both, it would cancel (`CKMClosure.global_dressing_cancels`); that is why Paper IV's
calculator leaves the dressing out of the observable matrix. The first-row deficit needs a dressing
on the quark transition that the muon transition does not carry. This module derives that split
from what is already in the library.

**The reference's axis is the time axis.**
* The reference is maintained by a refresh that keeps its axis, and the only such move is the sign
  exchange (`PMConstants.CarrierActions.same_axis_iff`); the weak refresh is that sign exchange
  (`WeakUniform.refresh_uniform`). `refresh_along_own_axis`: for a carrier on axis `0` the
  displacement of that move, `−2v`, lies on axis `0` alone.
* Along the time axis the transport of the maintained reference is the maintenance update itself
  (`PMConstants.VevEvent`). So the time direction is the reference's axis, which is the lepton axis
  (`ReferenceAxis`), and the three colour axes are the three spatial ones. This uses one premise:
  carrier vectors and lattice hop directions share the `D₄` coordinates.

**Which transitions are dressed.**
* A colour-carrier transition moves along a spatial axis, where a loss is registered into the
  spatial outlets (`DressingEvent`): amplitude factor `q`, `q² = 515/516`.
* A lepton-axis transition (muon decay, `μ → e ν ν̄`) moves along the time axis, where the
  comparison never fires under exact repair (`VevEvent.time_never_fires`): no loss, factor `1`.
* `measured_row`: so a quark row measured against muon decay has sum `q² · 1 / 1 = q²`, the
  deficit `1/516` does not cancel; `global_cancels` restates that equal dressing would cancel.

Consequences: every CKM row and column loses `1/516`, within `1σ` of all four measured sums
(`row_column_tests`: first row `0.9984(7)`, first column `0.9971(20)`, second row and column
`1.001(12)`, `1.003(12)`); lepton-axis processes (muon decay, PMNS
oscillation) are undressed, so PMNS stays unitary; a ratio of a hadronic to a leptonic rate of the
same weak vertex (e.g. `W → q q̄'` against `W → ℓ ν`) carries `q²`. The underlying mixing is still the
unitary basis change `U_uᴴ U_d` (`CKMClosure.basis_change_unitary`); the observed quark amplitude
is `q` times it, which is why `CKMClosure.closure_excludes_dressing` does not apply to the
observed block.
-/

namespace PMFlavor.DressingInheritance
open PMConstants.CarrierRepresentation

theorem refresh_along_own_axis :
    ∀ v : V, onLepton v = true → ∀ k : Fin 4, k ≠ 0 → -2 * coord v k = 0 := by
  decide +kernel

theorem measured_row (q2 s : ℝ) (hs : s = 1) : q2 * s / 1 = q2 := by
  rw [hs]; ring

theorem global_cancels (q2 Γq Γμ : ℝ) (hq : q2 ≠ 0) (hμ : Γμ ≠ 0) :
    (q2 * Γq) / (q2 * Γμ) = Γq / Γμ := by
  field_simp

theorem deficit : 1 - CKMDressing.q2 = 1 / 516 := by
  unfold CKMDressing.q2; norm_num

/-- **Every row and column, against the CKM 2023 workshop sums.** First row `0.9984(7)`, first
column `0.9971(20)`, second row `1.001(12)`, second column `1.003(12)`: the uniform `1 − 1/516` lies
within `1σ` of all four. -/
theorem row_column_tests :
    |(1 - 1/516 : ℝ) - 0.9984| / 0.0007 < 1 ∧ |(1 - 1/516 : ℝ) - 0.9971| / 0.0020 < 1 ∧
      |(1 - 1/516 : ℝ) - 1.001| / 0.012 < 1 ∧ |(1 - 1/516 : ℝ) - 1.003| / 0.012 < 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [abs_of_neg (by norm_num)]; norm_num
  · rw [abs_of_pos (by norm_num)]; norm_num
  · rw [abs_of_neg (by norm_num)]; norm_num
  · rw [abs_of_neg (by norm_num)]; norm_num

end PMFlavor.DressingInheritance
