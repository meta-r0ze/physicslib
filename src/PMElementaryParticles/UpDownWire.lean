import PMAction.ReferenceWallRotation

/-!
# Up and down over one wire: what the doublet reflection fixes

`DoubletReflection`: reflecting a colour axis fixes the reference's axis, exchanges up and down
(`flip_doublet`), and exchanges the two light classes `s ↔ c` (`flip_spinor`, `flip_cospinor`). The
weak refresh `v ↦ −v` commutes with it. So, if the two protocols use the wire with the same detuning
`δ_O` and vector carrier `K`, the down wire is the up wire with the two light carriers' amplitudes
exchanged: rows `(K, k_s, k_c)` and shift `(K, k_c, k_s)` (`UndetunedWall`'s bookkeeping) become rows
`(K, k_c, k_s)` and shift `(K, k_s, k_c)`.

* `product_equal`: the two light-mass matrices have the same determinant,
  `K k_s k_c (δ³ + K k_s k_c)`. So the product of the three masses is the same for up and down.
* Numerically (outside Lean): with `|k_s| = |k_c|` (Closure's one node price) and only a relative
  sign (the repair) the spectra are identical; with `|k_s| ≠ |k_c|` they differ, because the cycle is
  directed and the exchange reverses which light label the vector entry feeds.

**Consequences.**
1. An up/down mass difference over one wire needs `|k_s| ≠ |k_c|`: a magnitude asymmetry between the
   light classes that Closure's node price does not give. The same asymmetry is what PMFlavor's item 2
   needs between the two node changes (`|V_cb|/|V_ub| ≈ 10.7`, reference-wall versus other-wall) and
   what splits the light pair. One asymmetry, three readouts: a target for the derivation.
2. `product_equal` is a test. Recorded (2026-11, PDG, quarks `MS̄` at mixed scales, rough):
   `m_u m_c m_t / (m_d m_s m_b) ≈ 260`, not `1`. So up and down do not share `δ_O` and `K` with masses
   read as the wire's singular values: at least one of `δ_O`, `K` is protocol-set (the open "set by what
   a protocol occupies on that wall", PMAction REVIEW), or the masses are not those singular values.
-/

namespace PMElementaryParticles.UpDownWire
open Matrix PMAction.ReferenceWallRotation

/-- **Up and down have the same mass product.** -/
theorem product_equal (K ks kc δ : ℂ) :
    (diagonal ![K, ks, kc] * X δ ![K, kc, ks]).det =
      (diagonal ![K, kc, ks] * X δ ![K, ks, kc]).det := by
  rw [det_M, det_M]
  simp
  all_goals ring

end PMElementaryParticles.UpDownWire
