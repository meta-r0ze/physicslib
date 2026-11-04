import PMConstants.CarrierActions

/-! Paper V's internal-address interpretation, as a precise finite quotient.
The boundary observable and its physical interpretation are explicit. This does
not establish confinement, continuous SU(3), or a spacetime propagation law. -/
noncomputable section
namespace PMConstants.ColourRouting
open Finset CarrierActions CarrierRepresentation

/-- The observer retains sector, sign and lepton status, but not the colour address. -/
def boundary (v : Packet) : Bool × Bool × Bool :=
  (v.isLeft, positive (carried v), onLepton (carried v))

theorem boundary_invariant : ∀ (a b : Fin 3) (v : Packet),
    boundary (colour a b v)=boundary v := by decide +kernel

/-- Every two states with the same retained data differ only by a colour exchange.
The indexed formulation keeps finite checking independent of function equality. -/
lemma same_boundary_index : ∀ v w : Packet, boundary v=boundary w →
    ∃ a b : Fin 3, index (colour a b v)=index w := by decide +kernel

theorem same_boundary_iff (v w : Packet) :
    boundary v=boundary w ↔ ∃ a b : Fin 3, colour a b v=w := by
  constructor
  · intro h
    obtain ⟨a,b,hab⟩ := same_boundary_index v w h
    exact ⟨a,b,index_bijective.1 hab⟩
  · rintro ⟨a,b,rfl⟩; exact (boundary_invariant a b v).symm

/-- Thus the fibres are the full finite colour orbits, not arbitrary groupings. -/
def fibre (v : Packet) : Finset Packet := univ.filter (fun w => boundary w=boundary v)

theorem fibre_card : ∀ v : Packet,
    (fibre v).card=if onLepton (carried v) then 1 else 3 := by decide +kernel

theorem colour_changes_only_address (a b : Fin 3) (v : Packet) :
    boundary (colour a b v)=boundary v ∧ colour a b v ∈ fibre v := by
  simp [fibre, boundary_invariant]

/-- This internal motion also preserves the assigned boundary flux and channel type. -/
def electric (v : Packet) : ℚ := bl (carried v)/2+t3 (carried v)

theorem electric_invariant : ∀ (a b : Fin 3) (v : Packet),
    electric (colour a b v)=electric v := by decide +kernel

theorem type_invariant : ∀ (a b : Fin 3) (v : Packet),
    channelType (colour a b v)=channelType v := by decide +kernel

/-- Exactly which observables are insensitive to all these internal operations. -/
theorem invariant_iff_fibre_constant {A : Type*} (O : Packet → A) :
    (∀ a b v, O (colour a b v)=O v) ↔
      (∀ v w, boundary v=boundary w → O v=O w) := by
  constructor
  · intro hi v w h
    obtain ⟨a,b,rfl⟩ := (same_boundary_iff v w).mp h
    exact (hi a b v).symm
  · intro hf a b v
    exact hf _ _ (boundary_invariant a b v)

/-- The one-third law follows for an invariant load inside a coloured fibre.
Neither its total load nor invariance is inferred just from the number three. -/
theorem fibre_load (μ : Packet → ℚ)
    (hi : ∀ a b v, μ (colour a b v)=μ v) (v : Packet) :
    (∑ w ∈ fibre v, μ w)=(fibre v).card * μ v := by
  calc
    _ = ∑ _w ∈ fibre v, μ v := by
      apply sum_congr rfl
      intro w hw
      exact (invariant_iff_fibre_constant μ).mp hi w v ((mem_filter.mp hw).2)
    _ = _ := by simp

theorem third_of_coloured_load (μ : Packet → ℚ)
    (hi : ∀ a b v, μ (colour a b v)=μ v) (v : Packet)
    (hv : onLepton (carried v)=false) :
    μ v=(∑ w ∈ fibre v, μ w)/3 := by
  have h := fibre_load μ hi v
  rw [fibre_card, hv] at h
  norm_num at h
  linarith

/-- Coarse observer invariance does not imply that the internal update is identity. -/
theorem invisible_nontrivial : ∃ v : Packet,
    index (colour 0 1 v) ≠ index v ∧ boundary (colour 0 1 v)=boundary v := by
  decide +kernel

end PMConstants.ColourRouting
