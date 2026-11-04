import PMConstants.CarrierActions
import PersistenceMechanics.LawSelection

/-! Classify basis-preparation weights invariant under the actual weak flip
and colour-axis exchanges. This is a classification of incoherent basis laws,
not arbitrary quantum density matrices or a derivation of their physical use. -/
noncomputable section
namespace PMConstants.CarrierReadoutOrbits
open CarrierActions Finset
open RequirementTable

def Symmetric (μ : Packet → ℝ) : Prop :=
  (∀ v, μ (weak v)=μ v) ∧ ∀ a b v, μ (colour a b v)=μ v

/-- The existing operations have exactly the six type orbits. One colour
exchange and an optional weak flip suffice; no new physical operation is added. -/
private theorem orbit_index_iff : ∀ v w : Packet, channelType v=channelType w ↔
    ∃ f : Bool, ∃ a b : Fin 3,
      index (if f then weak (colour a b v) else colour a b v)=index w := by decide +kernel

theorem orbit_iff (v w : Packet) : channelType v=channelType w ↔
    ∃ f : Bool, ∃ a b : Fin 3,
      (if f then weak (colour a b v) else colour a b v)=w := by
  rw [orbit_index_iff]
  constructor
  · rintro ⟨f,a,b,h⟩; exact ⟨f,a,b,index_bijective.1 h⟩
  · rintro ⟨f,a,b,h⟩; exact ⟨f,a,b,congrArg index h⟩

theorem type_weak : ∀ v : Packet, channelType (weak v)=channelType v := by decide +kernel
theorem type_colour : ∀ a b : Fin 3, ∀ v : Packet,
    channelType (colour a b v)=channelType v := by decide +kernel

/-- Protocols formed only from the already defined carrier operations. -/
inductive Gate | weak | colour (a b : Fin 3)

def gate : Gate → Equiv.Perm Packet
  | .weak => CarrierActions.weak
  | .colour a b => CarrierActions.colour a b

def run : List Gate → Packet → Packet
  | [],v => v
  | g::gs,v => run gs (gate g v)

theorem protocol_preserves_type (gs : List Gate) (v : Packet) :
    channelType (run gs v)=channelType v := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    rw [run,ih]
    cases g with
    | weak => exact type_weak v
    | colour a b => exact type_colour a b v

/-- Every finite protocol in this gate set preserves all carrier distinctions. -/
theorem protocol_bijective (gs : List Gate) : Function.Bijective (run gs) := by
  induction gs with
  | nil => exact Function.bijective_id
  | cons g gs ih => exact ih.comp (gate g).bijective

/-- Exactly these six components are reachable by finite words in this gate
set. This classifies the gate set, not all possible particle protocols. -/
theorem protocol_reachable_iff (v w : Packet) :
    (∃ gs : List Gate, run gs v=w) ↔ channelType v=channelType w := by
  constructor
  · rintro ⟨gs,rfl⟩; exact (protocol_preserves_type gs v).symm
  · intro ht
    obtain ⟨f,a,b,he⟩ := (orbit_iff v w).mp ht
    cases f
    · exact ⟨[.colour a b],he⟩
    · exact ⟨[.colour a b,.weak],he⟩

def typed (w : Ty → ℝ) (v : Packet) : ℝ := w (channelType v)

theorem typed_symmetric (w : Ty → ℝ) : Symmetric (typed w) := by
  constructor
  · intro v; simp only [typed,type_weak]
  · intro a b v; simp only [typed,type_colour]

def repIndex : Ty → Fin 16
  | .Q => 0 | .u => 6 | .d => 9 | .L => 12 | .e => 14 | .n => 15

def representative (t : Ty) : Packet := enumeration.symm (repIndex t)

lemma enumeration_type (i : Fin 16) : channelType (enumeration.symm i)=ty i := by
  have h := type_preserved (enumeration.symm i)
  have hi : index (enumeration.symm i)=i := enumeration.apply_symm_apply i
  rw [hi] at h
  exact h.symm

lemma representative_type (t : Ty) : channelType (representative t)=t := by
  rw [representative,enumeration_type]
  cases t <;> decide

theorem invariant_same_type {μ : Packet → ℝ} (hμ : Symmetric μ)
    (v w : Packet) (ht : channelType v=channelType w) : μ v=μ w := by
  obtain ⟨f,a,b,he⟩ := (orbit_iff v w).mp ht
  rw [← he]
  cases f <;> simp only [Bool.false_eq_true,ite_false,ite_true,hμ.1,hμ.2]

/-- Every invariant basis law, including every positive normalized one, has
exactly one weight per type; no equality between different types is implied. -/
theorem symmetric_iff (μ : Packet → ℝ) : Symmetric μ ↔ ∃ w : Ty → ℝ, μ=typed w := by
  constructor
  · intro hμ
    refine ⟨fun t => μ (representative t),funext fun v => ?_⟩
    exact invariant_same_type hμ v _ (representative_type _).symm
  · rintro ⟨w,rfl⟩; exact typed_symmetric w

theorem weights_unique (w z : Ty → ℝ) (h : typed w=typed z) : w=z := by
  funext t
  have he := congrFun h (representative t)
  simpa only [typed,representative_type] using he

theorem total_mass (w : Ty → ℝ) :
    (∑ v : Packet, typed w v)=6*w .Q+3*w .u+3*w .d+2*w .L+w .e+w .n := by
  rw [← Equiv.sum_comp enumeration.symm (typed w)]
  simp only [typed,enumeration_type]
  norm_num [Fin.sum_univ_succ,ty]
  ring

theorem positive_law_iff (w : Ty → ℝ) : PersistenceMechanics.LawSelection.PosLaw (typed w) ↔
    (∀ t, 0 < w t) ∧ 6*w .Q+3*w .u+3*w .d+2*w .L+w .e+w .n=1 := by
  rw [PersistenceMechanics.LawSelection.PosLaw,total_mass]
  constructor
  · rintro ⟨hp,hn⟩
    exact ⟨fun t => by simpa only [typed,representative_type] using hp (representative t),hn⟩
  · rintro ⟨hp,hn⟩; exact ⟨fun v => hp _,hn⟩

end PMConstants.CarrierReadoutOrbits
