import PMFlavor.ExchangeAxis
import PMAction.MassInsertion
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Where in the tick an insertion sits does not change its light-mode element

`MassInsertion` needs class-dependent diagonal masses; `PMAction.ZeroModeCoupling` locates a direct
light-mode coupling as the off-Wilson part of the inter-wall hop. This module asks whether the
discrete-time update makes the classes differ.

**The classes in time (stronger than the library).** The library identifies time with axis `0`,
the reference (lepton) axis, as a shared axis label (`DressingInheritance`). The counts below read
carrier vectors as spacetime displacements, which the library does not hold: a carrier label is not a
site (`PMConstants.WeakLocality`). They are kept as the strongest case; `placement_invisible` and
`node_denominator_real` do not depend on them, and with the library's weaker premise there is no
placement in time to vary at all. In the doubled coordinates of `PMAction.Machine.CarrierEvents` a `D₄`
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

**The node's own phase gives no CP flux.** A spinor carrier crossing the node evolves for some time
on the odd sector, phase `e^{−i·gap(p)·t}` (`PMAction.Machine.OddCarrierPhase.phase_sector`), the same
in both directions since time runs forward. In the zero-energy reduction that evolution becomes a
real energy denominator: `node_denominator_real`, the coupling `t₁ t̄₂ / d` with real `d` is the
conjugate of the reverse coupling, so the reduced link stays Hermitian and the loop flux is the
product of the leg phases alone. A crossing time or node energy, however large its phase, does not
enter the flux.
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

/-- **A real node denominator keeps the reduced coupling Hermitian.** -/
theorem node_denominator_real (t₁ t₂ : ℂ) (d : ℝ) :
    (starRingEnd ℂ) (t₁ * (starRingEnd ℂ) t₂ / d) = t₂ * (starRingEnd ℂ) t₁ / d := by
  rw [map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

end PMFlavor.TickPlacement
