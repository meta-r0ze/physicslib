import PMAction.Machine.RootWordControls

/-!
# An edge's link depends only on the controls along that edge

To realize a general substrate configuration (every edge with its own root word) by one set of
controls, the per-edge controls of `RootWordControls` must be put together without disturbing
each other. This module proves the principle that makes that possible.

* `transport_local`: two transports whose generators agree on `[0, s]` agree at `s`. This is the
  interval form of `NativePacketUpdate.transport_unique`; only the generator along the edge
  matters.
* `edge_local`, `edge_local_native`: the realized link on the edge from `y` along `v` depends only
  on the controls on the segment `y + [0, 1] v`, on the packet and on all eight carrier labels.
* `packetA_add`: the generator is additive in the controls.
* `edge_add_vanishing`: adding controls that vanish on an edge's segment does not change that
  edge's link.
* `root_word_add_vanishing`: so the root word of `RootWordControls.root_word_link` survives any
  added controls that vanish on its edge.

**Still open:** the geometry. For a finite set of edges, choose per-edge staggered controls
supported in a thin tube around the middle of each edge, so that each tube misses every other
edge's segment. Then the sum realizes every edge's root word at once.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.EdgeLocality
open Matrix NativeCoherentLinks NativePacketUpdate Set
open scoped Matrix.Norms.L2Operator

/-- **Transport is local in the generator.** -/
theorem transport_local {ι : Type*} [Fintype ι] [DecidableEq ι] {B C : ℝ → Matrix ι ι ℂ}
    (hskew : ∀ t, star (C t) = -C t) {T U : ℝ → Matrix ι ι ℂ} (hT0 : T 0 = 1) (hU0 : U 0 = 1)
    (hT : ∀ t, HasDerivAt T (T t * B t) t) (hU : ∀ t, HasDerivAt U (U t * C t) t)
    (hUu : ∀ t, U t ∈ unitary (Matrix ι ι ℂ)) (s : ℝ) (hs : 0 ≤ s)
    (hBC : ∀ t ∈ Icc 0 s, B t = C t) : T s = U s := by
  have hF (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt (fun r => T r * star (U r)) 0 r := by
    have h := FiniteMatrixTransport.rectangular_deriv (hT r) (hU r).star
    convert h using 1
    rw [star_mul, hskew, hBC r hr]
    noncomm_ring
  have hc := constant_of_has_deriv_right_zero (f := fun r => T r * star (U r)) (a := 0) (b := s)
    (fun r hr => (hF r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hF r (Ico_subset_Icc_self hr)).hasDerivWithinAt) s ⟨hs, le_rfl⟩
  simp only [hT0, hU0, star_one, Matrix.mul_one] at hc
  have hu := (Unitary.mem_iff.mp (hUu s)).1
  calc T s = T s * (star (U s) * U s) := by rw [hu, Matrix.mul_one]
    _ = U s := by rw [← Matrix.mul_assoc, hc, Matrix.one_mul]

/-- **An edge's packet link depends only on the generator along its segment.** -/
theorem edge_local (c : Fin 3) {w w' : Controls} (r : Realization c w) (r' : Realization c w')
    (y v : V) (h : ∀ t ∈ Icc (0 : ℝ) 1, packetA c w (y + t • v) v = packetA c w' (y + t • v) v) :
    r.packet y v 1 = r'.packet y v 1 :=
  transport_local (fun t => packet_skew c w' (y + t • v) v) (r.packet_zero y v)
    (r'.packet_zero y v) (r.packet_deriv y v) (r'.packet_deriv y v) (r'.packet_unitary y v) 1
    zero_le_one h

/-- **The same on all eight carrier labels.** -/
theorem edge_local_native (c : Fin 3) {w w' : Controls} (r : Realization c w)
    (r' : Realization c w') (y v : V)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, nativeA c w (y + t • v) v = nativeA c w' (y + t • v) v) :
    r.native y v 1 = r'.native y v 1 :=
  transport_local (fun t => native_skew c w' (y + t • v) v) (r.native_zero y v)
    (r'.native_zero y v) (r.native_deriv y v) (r'.native_deriv y v) (r'.native_unitary y v) 1
    zero_le_one h

/-- **The generator is additive in the controls.** -/
theorem packetA_add (c : Fin 3) (w z : Controls) (x v : V) :
    packetA c (w + z) x v = packetA c w x v + packetA c z x v := by
  simp [packetA, form, ContinuousLinearMap.smulRight_apply, add_smul, Finset.sum_add_distrib]

/-- **Controls that vanish on an edge do not change its link.** -/
theorem edge_add_vanishing (c : Fin 3) {w z : Controls} (r : Realization c (w + z))
    (r' : Realization c w) (y v : V) (hz : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, z j (y + t • v) v = 0) :
    r.packet y v 1 = r'.packet y v 1 :=
  edge_local c r r' y v fun t ht => by
    rw [packetA_add]
    have h0 : packetA c z (y + t • v) v = 0 := by
      simp [packetA, form, ContinuousLinearMap.smulRight_apply, hz t ht]
    rw [h0, add_zero]

/-- **The root word survives added controls that vanish on its edge.** -/
theorem root_word_add_vanishing (c : Fin 3) (f : V →L[ℝ] ℝ) (a : Fin 4 → ℝ) {z : Controls}
    (r : Realization c (RootWordControls.stagger f a + z))
    (y v : V) (hv : f v = 1) (hy : f y = 0)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, z j (y + t • v) v = 0) :
    r.packet y v 1 = NormedSpace.exp (RootWordControls.R c a 0) *
      (NormedSpace.exp (RootWordControls.R c a 1) *
        (NormedSpace.exp (RootWordControls.R c a 2) * NormedSpace.exp (RootWordControls.R c a 3))) := by
  rw [edge_add_vanishing c r (realized c _ (RootWordControls.stagger_c2 f a)) y v hz]
  exact RootWordControls.root_word_link c f a _ y v hv hy

end PMAction.EdgeLocality
