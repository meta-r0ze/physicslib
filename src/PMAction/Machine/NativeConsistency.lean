import PMAction.Machine.D4EdgeSeparation
import PMAction.CompactTransport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The substrate's links meet the continuum premises

`D4EdgeSeparation.d4_configuration_realized` realizes every finite configuration of distinct `D₄`
edges, each carrying its own root word, by C² controls. `CompactTransport` derives the continuum
premises (`C^{1,1}` connection, cubic link consistency) for transports of a compactly supported
C² connection. This module joins them.

* `form_compact`: compactly supported controls give a compactly supported generator.
* `native_premises`: for compactly supported C² controls, the native packet links are cubically
  consistent with `packetA` at every point, and `packetA` has a globally Lipschitz derivative.
* `d4_configuration_compact`: the controls of a finite configuration can be cut off by a smooth
  bump that is `1` on every edge, so they have compact support and the same links.
* `d4_configuration_consistent`: **every finite configuration of distinct `D₄` edges with its own
  root word on each is realized by native packet links that satisfy the continuum premises**. The
  premises "`C^{1,1}` connection" and "links cubically consistent with it" of
  `ReferenceSampling.ref_limit`, `SummedReference.sum_limit` and the gauge-factor limits hold for
  these links.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.NativeConsistency
open Matrix NativeCoherentLinks NativePacketUpdate D4EdgeSeparation ConfigurationControls Set
open scoped Matrix.Norms.L2Operator

/-- **Compactly supported controls give a compactly supported generator.** -/
lemma form_compact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (B : Fin 4 → F)
    (w : Controls) (hwc : ∀ j, HasCompactSupport (w j)) : HasCompactSupport (form B w) := by
  have h : ∀ j, HasCompactSupport fun x => (w j x).smulRight (B j) := fun j =>
    (hwc j).comp_left (g := fun l : V →L[ℝ] ℝ => l.smulRight (B j)) (by simp)
  have e : form B w = fun x => (w 0 x).smulRight (B 0) + (w 1 x).smulRight (B 1) +
      (w 2 x).smulRight (B 2) + (w 3 x).smulRight (B 3) := by
    funext x; simp [form, Fin.sum_univ_four]
  rw [e]
  exact (((h 0).add (h 1)).add (h 2)).add (h 3)

/-- **Native packet links of compactly supported C² controls meet the continuum premises.** -/
theorem native_premises (c : Fin 3) (w : Controls) (hw : ∀ j, ContDiff ℝ 2 (w j))
    (hwc : ∀ j, HasCompactSupport (w j)) (r : Realization c w) :
    ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧ (∀ y, HasFDerivAt (packetA c w) (fderiv ℝ (packetA c w) y) y) ∧
      (∀ x y, ‖fderiv ℝ (packetA c w) y - fderiv ℝ (packetA c w) x‖ ≤ L * ‖y - x‖) ∧
      ∀ x, LinkConsistency.CubicConsistent r.packet (packetA c w) x K :=
  CompactTransport.compact_transport_premises (form_c2 _ w hw) (form_compact _ w hwc)
    (packet_skew c w) r.packet r.packet_zero r.packet_deriv r.packet_unitary

/-- **The configuration's controls can be taken with compact support.** -/
theorem d4_configuration_compact {ι : Type*} [Fintype ι] (c : Fin 3) (Y : ι → Fin 4 → ℤ)
    (hY : ∀ e, Even (∑ i, Y e i)) (r : ι → AxisHop.Tri) (hr : ∀ e, AxisHop.IsRoot (r e))
    (a : ι → Fin 4 → ℝ) (hdist : ∀ e e', e ≠ e' → ¬ sameSeg (Y e) (r e) (Y e') (r e')) :
    ∃ w : Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧ (∀ j, HasCompactSupport (w j)) ∧
      ∀ (R : Realization c w) (e : ι), R.packet (pt (Y e)) (dir (r e)) 1 = word c (a e) := by
  obtain ⟨w, hw, hlink⟩ := d4_configuration_realized c Y hY r hr a hdist
  let S : Set V := ⋃ e, (fun t : ℝ => pt (Y e) + t • dir (r e)) '' Icc 0 1
  have hS : IsCompact S := isCompact_iUnion fun e => isCompact_Icc.image (by fun_prop)
  obtain ⟨R0, hR0⟩ := isBounded_iff_forall_norm_le.1 hS.isBounded
  let ψ : ContDiffBump (0 : V) := ⟨|R0| + 1, |R0| + 2, by positivity, by linarith⟩
  let w' : Controls := fun j x => ψ x • w j x
  refine ⟨w', fun j => ψ.contDiff.smul (hw j), fun j => ψ.hasCompactSupport.smul_right,
    fun R e => ?_⟩
  have hagree : ∀ t ∈ Icc (0 : ℝ) 1, packetA c w' (pt (Y e) + t • dir (r e)) (dir (r e)) =
      packetA c w (pt (Y e) + t • dir (r e)) (dir (r e)) := fun t ht =>
    packetA_congr c _ _ fun j => by
      have hx : pt (Y e) + t • dir (r e) ∈ S := mem_iUnion.2 ⟨e, t, ht, rfl⟩
      have hn := hR0 _ hx
      have h1 : ψ (pt (Y e) + t • dir (r e)) = 1 := ψ.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [le_abs_self R0])
      show ψ (pt (Y e) + t • dir (r e)) • w j (pt (Y e) + t • dir (r e)) = _
      rw [h1, one_smul]
  rw [EdgeLocality.edge_local c R (realized c w hw) _ _ hagree]
  exact hlink _ e

/-- **The substrate's configurations meet the continuum premises.** Every finite configuration of
distinct `D₄` edges, each with its own root word, is realized by native packet links that are
cubically consistent with a `C^{1,1}` connection at every point. -/
theorem d4_configuration_consistent {ι : Type*} [Fintype ι] (c : Fin 3) (Y : ι → Fin 4 → ℤ)
    (hY : ∀ e, Even (∑ i, Y e i)) (r : ι → AxisHop.Tri) (hr : ∀ e, AxisHop.IsRoot (r e))
    (a : ι → Fin 4 → ℝ) (hdist : ∀ e e', e ≠ e' → ¬ sameSeg (Y e) (r e) (Y e') (r e')) :
    ∃ w : Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧
      (∀ (R : Realization c w) (e : ι), R.packet (pt (Y e)) (dir (r e)) 1 = word c (a e)) ∧
      ∀ R : Realization c w, ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧
        (∀ y, HasFDerivAt (packetA c w) (fderiv ℝ (packetA c w) y) y) ∧
        (∀ x y, ‖fderiv ℝ (packetA c w) y - fderiv ℝ (packetA c w) x‖ ≤ L * ‖y - x‖) ∧
        ∀ x, LinkConsistency.CubicConsistent R.packet (packetA c w) x K := by
  obtain ⟨w, hw, hwc, hlink⟩ := d4_configuration_compact c Y hY r hr a hdist
  exact ⟨w, hw, hlink, fun R => native_premises c w hw hwc R⟩

end PMAction.NativeConsistency
