import PMFlavor.NativeFlavourCurrent
import PMAction.WeakVertex
import Mathlib.Tactic

/-!
# The native flavour current *is* the Paper-II V−A chiral current

An earlier review item asked whether the flavour current is a free choice. Within the
chosen four-component chiral representation, part of it is not: the chiral
projector the native current uses is exactly Paper II's `P_L = ½(1 − γ⁵)`.
This module proves the identification, so the native current's chirality is
inherited from Paper II's charged-current vertex rather than chosen separately.

**Where the projector comes from.** PMAction's `ChiralityConvention` now proves
that `projector = fromBlocks P_L 0 0 P_L` (`projector_eq_fromBlocks_PL`) and that
any operator killing the unphysical first-wall background and fixing the exchanged
physical reference agrees with it on every zero mode
(`projector_unique_on_kernel`). So the chiral projector is forced on the zero kernel
by the reference, not chosen there.

**Remaining caveat.** `PMAction.ConcreteFermion` states that its four-component
representation "verifies a representation; it does not derive its physical gauge
content." Attaching the weak gauge representation and extending the projector off
the zero kernel remain inputs.

* `spinProjector_eq_PL` — `NativeFlavourCurrent.spinProjector = WeakVertex.PL`.
* `spinProjector_idempotent`, `spinProjector_hermitian`, `spinProjector_trace` —
  the native projector is a rank-two projector, transported from Paper II's
  `PL_idempotent`, `PL_hermitian`, `PL_trace`.
* `vertex_eq_native` — the V−A vertex `(g/√2) γ^μ P_L` is written with the native
  projector.
* `modelCurrent_eq_PL` — the native current is `P_L ⊗ G` on both walls.

What this does **not** fix (and remains a physical input): the flavour generator
`G`, the carrier charge values, the mediator/statistics, and the chiral
representation itself. It only removes the chirality from the list of choices
inside the supplied representation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMFlavor.WeakCurrentBridge
open Matrix PMAction NativeFlavourCurrent
open scoped Kronecker

/-- **The native chiral projector is Paper II's weak V−A projector.** -/
theorem spinProjector_eq_PL :
    (NativeFlavourCurrent.spinProjector : Matrix (Fin 4) (Fin 4) ℂ) =
      PMAction.WeakVertex.PL := by
  rw [NativeFlavourCurrent.spinProjector, PMAction.WeakVertex.PL, PMAction.VATrace.L_eq]

/-- The native projector is idempotent (inherited from `P_L`). -/
theorem spinProjector_idempotent :
    NativeFlavourCurrent.spinProjector * NativeFlavourCurrent.spinProjector =
      NativeFlavourCurrent.spinProjector := by
  rw [spinProjector_eq_PL]
  exact PMAction.WeakVertex.PL_idempotent

/-- The native projector is Hermitian. -/
theorem spinProjector_hermitian : NativeFlavourCurrent.spinProjector.IsHermitian := by
  rw [spinProjector_eq_PL]
  exact PMAction.WeakVertex.PL_hermitian

/-- The native projector has rank two. -/
theorem spinProjector_trace : NativeFlavourCurrent.spinProjector.trace = 2 := by
  rw [spinProjector_eq_PL]
  exact PMAction.WeakVertex.PL_trace

/-- **The V−A vertex is written with the native projector.** -/
theorem vertex_eq_native (gw : ℝ) (μ : Fin 4) :
    PMAction.WeakVertex.vertex gw μ =
      (((gw / Real.sqrt 2 : ℝ) : ℂ)) •
        (PMAction.VATrace.g μ * NativeFlavourCurrent.spinProjector) := by
  rw [PMAction.WeakVertex.vertex, ← spinProjector_eq_PL]

/-- **The native flavour current is `P_L ⊗ G` on both walls.** -/
theorem modelCurrent_eq_PL {f : Type*} [Fintype f] [DecidableEq f] (G : Matrix f f ℂ) :
    NativeFlavourCurrent.modelCurrent G =
      (fromBlocks (PMAction.WeakVertex.PL ⊗ₖ G) 0 0 (PMAction.WeakVertex.PL ⊗ₖ G) :
        Matrix (NativeFlavourWall.Modes (f := f)) (NativeFlavourWall.Modes (f := f)) ℂ) := by
  rw [NativeFlavourCurrent.modelCurrent, spinProjector_eq_PL]

end PMFlavor.WeakCurrentBridge
