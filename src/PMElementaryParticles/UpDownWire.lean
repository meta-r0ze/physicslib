import PMAction.WireMass

/-!
# Up and down over one wire: what the doublet reflection fixes

`DoubletReflection`: reflecting a colour axis fixes the reference's axis, exchanges up and down
(`flip_doublet`), and exchanges the two light classes `s ↔ c` (`flip_spinor`, `flip_cospinor`). The
weak refresh `v ↦ −v` commutes with it. So, if the two protocols use the wire with the same detuning
`δ_O` and vector carrier `K`, the down wire is the up wire with the two light carriers' amplitudes
exchanged: reference-wall carriers `(K, k_s, k_c)` and other-wall carriers `(K, k_c, k_s)` by class (placed by
`PMAction.WireMass.shift`) become `(K, k_c, k_s)` and `(K, k_s, k_c)`.

* `product_equal`: the two light-mass matrices have the same determinant,
  `K k_s k_c (δ³ + K k_s k_c)`. So the product of the three masses is the same for up and down.
* Numerically (outside Lean): with `|k_s| = |k_c|` (Closure's one node price) and only a relative
  sign (the repair) the spectra are identical; with `|k_s| ≠ |k_c|` they differ, because the cycle is
  directed and the exchange reverses which light label the vector entry feeds.

**Consequences.**
1. An up/down mass difference over one wire, with shared `δ_O` and `K`, needs `|k_s| ≠ |k_c|`: a
   magnitude asymmetry between the light classes that Closure's node price does not give.
2. `product_equal` is a test. Recorded (2026-11, PDG, quarks `MS̄` at mixed scales, rough):
   `m_u m_c m_t / (m_d m_s m_b) ≈ 260`, not `1`. So up and down do not share `δ_O` and `K` with masses
   read as the wire's singular values: at least one of `δ_O`, `K` is protocol-set (the open "set by what
   a protocol occupies on that wall", PMAction REVIEW), or the masses are not those singular values.
-/

namespace PMElementaryParticles.UpDownWire
open Matrix PMAction.WireMass

/-- **Up and down have the same mass product.** -/
theorem product_equal (K ks kc δ : ℂ) :
    (mass δ ![K, ks, kc] ![K, kc, ks]).det = (mass δ ![K, kc, ks] ![K, ks, kc]).det := by
  rw [det_mass, det_mass]
  simp
  ring

end PMElementaryParticles.UpDownWire
