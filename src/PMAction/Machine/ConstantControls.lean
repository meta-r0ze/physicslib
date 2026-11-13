import PMAction.Machine.NativePacketUpdate

/-!
# Controls from the substrate's links: homogeneous configurations

`NativeCoherentLinks` builds lattice links from C² control one-forms `w`: `w j x v` is the rate at
which root-cost generator `j` runs along direction `v` at `x`. The control is the gauge-field
configuration. This module goes the other way, from the substrate to the controls: given the links
the substrate produces, are they realized by C² controls?

On the substrate, one lattice step of coherent root evolution with real rates `aⱼ` gives the link
`exp (Σⱼ aⱼ • packetRoot c j)` (`packetRoot c j = −i · cost`, the root-response generator).

* `constant`, `constant_c2`: rates that do not depend on the site are constant controls, hence
  smooth.
* `packet_link_exp`, `native_link_exp`: for constant controls the realized transport along `v` is
  exactly `exp (s • gen v)`, on the packet and on all eight carrier labels. This is
  `transport_unique`, not an extra assumption.
* `homogeneous_realized`: for any basis of edge directions `b μ` and any rates `a μ j`, constant
  controls realize the link `exp (Σⱼ a μ j • packetRoot c j)` on every edge along `b μ`.

So for homogeneous configurations (the same rates on every edge of a given direction), the C²
hypothesis is a consequence of the substrate, not an input. **Still open:** site-varying
configurations, where each edge has its own rates. That needs controls localized along edges
(bump functions supported near each edge segment) whose transports reproduce each edge's link.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PMAction.ConstantControls
open Matrix NativeCoherentLinks NativePacketUpdate
open scoped Matrix.Norms.L2Operator

/-- Site-independent rates: root `j` runs at rate `ℓ j v` along `v`, everywhere. -/
def constant (ℓ : Fin 4 → V →L[ℝ] ℝ) : Controls := fun j _ => ℓ j

/-- **Constant controls are smooth.** -/
theorem constant_c2 (ℓ : Fin 4 → V →L[ℝ] ℝ) : ∀ j, ContDiff ℝ 2 (constant ℓ j) :=
  fun _ => contDiff_const

/-- The packet step generator along `v`. -/
def gen (c : Fin 3) (ℓ : Fin 4 → V →L[ℝ] ℝ) (v : V) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ j, ℓ j v • packetRoot c j

/-- The full eight-label step generator along `v`. -/
def nativeGen (c : Fin 3) (ℓ : Fin 4 → V →L[ℝ] ℝ) (v : V) :
    Matrix (CarrierEvents.Carrier c) (CarrierEvents.Carrier c) ℂ :=
  ∑ j, ℓ j v • nativeRoot c j

lemma packetA_constant (c : Fin 3) (ℓ : Fin 4 → V →L[ℝ] ℝ) (y v : V) :
    packetA c (constant ℓ) y v = gen c ℓ v := by
  simp [packetA, form, constant, gen, ContinuousLinearMap.smulRight_apply]

lemma nativeA_constant (c : Fin 3) (ℓ : Fin 4 → V →L[ℝ] ℝ) (y v : V) :
    nativeA c (constant ℓ) y v = nativeGen c ℓ v := by
  simp [nativeA, form, constant, nativeGen, ContinuousLinearMap.smulRight_apply]

/-- **The packet link of constant controls is an exponential.** -/
theorem packet_link_exp (c : Fin 3) (ℓ : Fin 4 → V →L[ℝ] ℝ) (r : Realization c (constant ℓ))
    (y v : V) (s : ℝ) : r.packet y v s = NormedSpace.exp (s • gen c ℓ v) := by
  symm
  refine transport_unique (B := fun _ => gen c ℓ v) (fun _ => ?_) ?_ (r.packet_zero y v)
    (fun t => hasDerivAt_exp_smul_const (𝕂 := ℝ) _ t) (fun t => ?_) (r.packet_unitary y v) s
  · have h := packet_skew c (constant ℓ) 0 v
    rwa [packetA_constant] at h
  · simp
  · have h := r.packet_deriv y v t
    rwa [packetA_constant] at h

/-- **The full eight-label link of constant controls is an exponential.** -/
theorem native_link_exp (c : Fin 3) (ℓ : Fin 4 → V →L[ℝ] ℝ) (r : Realization c (constant ℓ))
    (y v : V) (s : ℝ) : r.native y v s = NormedSpace.exp (s • nativeGen c ℓ v) := by
  symm
  refine transport_unique (B := fun _ => nativeGen c ℓ v) (fun _ => ?_) ?_ (r.native_zero y v)
    (fun t => hasDerivAt_exp_smul_const (𝕂 := ℝ) _ t) (fun t => ?_) (r.native_unitary y v) s
  · have h := native_skew c (constant ℓ) 0 v
    rwa [nativeA_constant] at h
  · simp
  · have h := r.native_deriv y v t
    rwa [nativeA_constant] at h

/-- **Homogeneous substrate links are realized by smooth controls.** For edge directions `b μ`
and rates `a μ j`, constant controls give the link `exp (Σⱼ a μ j • packetRoot c j)` on every
edge along `b μ`. -/
theorem homogeneous_realized (c : Fin 3) (b : Module.Basis (Fin 4) ℝ V) (a : Fin 4 → Fin 4 → ℝ) :
    ∃ w : Controls, (∀ j, ContDiff ℝ 2 (w j)) ∧
      ∀ (r : Realization c w) (y : V) (μ : Fin 4),
        r.packet y (b μ) 1 = NormedSpace.exp (∑ j, a μ j • packetRoot c j) := by
  refine ⟨constant fun j => ∑ ν, a ν j • LinearMap.toContinuousLinearMap (b.coord ν),
    constant_c2 _, fun r y μ => ?_⟩
  rw [packet_link_exp]
  congr 1
  simp [gen, Finsupp.single_apply]

end PMAction.ConstantControls
