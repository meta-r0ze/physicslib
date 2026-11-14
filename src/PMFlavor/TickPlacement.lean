import PMFlavor.ExchangeAxis
import PMFlavor.MassInsertion
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Where in the tick an insertion sits does not change its light-mode element

`MassInsertion` needs class-dependent diagonal masses; `PMAction.ZeroModeCoupling` locates a direct
light-mode coupling as the off-Wilson part of the inter-wall hop. This module asks whether the
discrete-time update makes the classes differ.

**The classes in time.** The library already identifies time with axis `0`, the reference (lepton)
axis, under the premise that carrier vectors and lattice hop directions share the `D₄` coordinates
(`DressingInheritance`). In the doubled coordinates of `PMAction.Machine.CarrierEvents` a `D₄`
root one tick forward is `(2, ±2, 0, 0)` up to spatial permutation, an axis move of the walk, so one
tick is `2` units on axis `0`. Then (`ExchangeAxis`):
* vector-class carriers: `6` are equal-time axis displacements (`vector_free`), `2` are pure ticks
  (`vector_touch`);
* spinor-class carriers: every one has time component `±1` (`spinor_touch`), **half a tick**.

**Placement is invisible at the light mode.** `placement_invisible`: if the factors before and after
an insertion `X` fix the light mode (`B v = v`, `Aᴴ w = w`), then `⟨w, A X B v⟩ = ⟨w, X v⟩`. The
light modes have energy `0` (`PMAction.DomainWall.update_zero_mode`), so a tick `e^{−iτH}` and a half
tick `e^{−iτH/2}` both fix them. An insertion at a half tick, at a full tick or at equal time has the
same light-mode element. The time component of a class cannot make the classes differ through the
update.

Something outside the update acting between ticks could, and the only candidate is the weak
refresh. But the refresh has no special tick: weak reaches all `43` clock addresses
(`PMConstants.WeakLocality`, `RequirementRows`; the same fact that contradicts `VcbEnvelope`'s tick
reading). So the discrete-time route gives no class dependence. The class dependence of the
diagonal masses is then the node passage the library already has: spinor insertions touch the
reference axis and cross the node (`NodeElimination`), while six of eight vector insertions stay
in-cycle. A class-dependent Wilson departure `r_m − 1` (`ZeroModeCoupling`) is not needed; the
direct light-mode term needs `r ≠ 1` (or another off-Wilson source) only as a common factor.
-/

namespace PMFlavor.TickPlacement
open Matrix

variable {n : Type*} [Fintype n]

/-- **Placement is invisible at a fixed mode.** If `B` fixes `v` and `Aᴴ` fixes `w`, the element of
`A X B` between them is the element of `X`. -/
theorem placement_invisible (A X B : Matrix n n ℂ) (v w : n → ℂ)
    (hB : B *ᵥ v = v) (hA : Aᴴ *ᵥ w = w) :
    star w ⬝ᵥ ((A * X * B) *ᵥ v) = star w ⬝ᵥ (X *ᵥ v) := by
  have h1 : (A * X * B) *ᵥ v = A *ᵥ (X *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, hB, ← Matrix.mulVec_mulVec]
  have h2 : star w ᵥ* A = star w := by
    have h := congrArg star hA
    rwa [Matrix.star_mulVec, conjTranspose_conjTranspose] at h
  rw [h1, Matrix.dotProduct_mulVec, h2]

end PMFlavor.TickPlacement
