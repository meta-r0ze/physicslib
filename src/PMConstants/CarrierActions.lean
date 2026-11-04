import PMConstants.CarrierRepresentation
import PMAction.CarrierResponse

/-! Actual finite carrier operations behind two representation columns.
The axis/sign interpretation is inherited; no continuous gauge group or
clock-refresh assignment is inferred from the cardinalities alone. -/
noncomputable section
namespace PMConstants.CarrierActions
open PMAction.CarrierEvents PMConstants.CarrierRepresentation
open Matrix Finset

abbrev Packet := V ⊕ V

/-- Simultaneous sign reversal on the actual doubled-coordinate carrier. -/
def negativeBox (v : V) : Box := fun i => (v.1 i).rev
lemma negative_valid : ∀ v : V, valid 0 (negativeBox v) := by decide +kernel

def signExchange : Equiv.Perm V where
  toFun v := ⟨negativeBox v, negative_valid v⟩
  invFun v := ⟨negativeBox v, negative_valid v⟩
  left_inv v := by apply Subtype.ext; funext i; simp [negativeBox]
  right_inv v := by apply Subtype.ext; funext i; simp [negativeBox]

/-- The left-sector sign exchange acts on all four doublet pairs. -/
def weak : Equiv.Perm Packet := Equiv.sumCongr signExchange (Equiv.refl V)

def colourAxis (a : Fin 3) : Fin 4 := ⟨a.val+1, by omega⟩
def axisExchange (a b : Fin 3) : Equiv.Perm V :=
  permute 0 (Equiv.swap (colourAxis a) (colourAxis b))

/-- Colour-axis exchanges act in both sectors and leave the lepton axis fixed. -/
def colour (a b : Fin 3) : Equiv.Perm Packet :=
  Equiv.sumCongr (axisExchange a b) (axisExchange a b)

def weakSupport : Finset Packet := univ.filter (fun v => weak v ≠ v)
def carried : Packet → V := Sum.elim id id

def colourChanges (a b : Fin 3) (v : Packet) : Prop :=
  coord (carried v) (colourAxis a) ≠ coord (carried v) (colourAxis b)
instance (a b : Fin 3) (v : Packet) : Decidable (colourChanges a b v) :=
  inferInstanceAs (Decidable (_ ≠ _))

lemma axis_fixed_iff (a b : Fin 3) (v : V) :
    axisExchange a b v = v ↔ coord v (colourAxis a) = coord v (colourAxis b) := by
  constructor
  · intro h
    have hh := congrArg (fun w : V => coord w (colourAxis a)) h
    change coord v (Equiv.swap (colourAxis a) (colourAxis b) (colourAxis a)) = _ at hh
    simpa using hh.symm
  · intro h
    apply vector_injective 0
    funext i
    change coord v (Equiv.swap (colourAxis a) (colourAxis b) i) = coord v i
    by_cases ha : i = colourAxis a
    · subst i; simpa using h.symm
    by_cases hb : i = colourAxis b
    · subst i; simpa using h
    simp [Equiv.swap_apply_def, ha, hb]

lemma colour_changed_iff (a b : Fin 3) (v : Packet) :
    colour a b v ≠ v ↔ colourChanges a b v := by
  cases v <;> simpa [colour, colourChanges, carried] using not_congr (axis_fixed_iff a b _)

def colourSupport : Finset Packet := univ.filter (fun v =>
  colourChanges 0 1 v ∨ colourChanges 0 2 v ∨ colourChanges 1 2 v)

lemma changes_generators_cover : ∀ (a b : Fin 3) (v : Packet),
    colourChanges a b v → v ∈ colourSupport := by decide +kernel

lemma colour_generators_cover (a b : Fin 3) (v : Packet)
    (h : colour a b v ≠ v) : v ∈ colourSupport :=
  changes_generators_cover a b v ((colour_changed_iff a b v).mp h)

lemma colour_exists_iff (v : Packet) : (∃ a b : Fin 3, colour a b v ≠ v) ↔ v ∈ colourSupport := by
  constructor
  · rintro ⟨a,b,h⟩; exact colour_generators_cover a b v h
  · intro h
    simp only [colourSupport, mem_filter, mem_univ, true_and] at h
    rcases h with h | h | h
    · exact ⟨0,1,(colour_changed_iff 0 1 v).mpr h⟩
    · exact ⟨0,2,(colour_changed_iff 0 2 v).mpr h⟩
    · exact ⟨1,2,(colour_changed_iff 1 2 v).mpr h⟩

def channelType : Packet → RequirementTable.Ty := Sum.elim leftType rightType

/-- The affected-state columns now follow from specified carrier operations. -/
theorem weak_support_column : ∀ v : Packet,
    v ∈ weakSupport ↔ RequirementTable.isoDim (channelType v)=2 := by decide +kernel

theorem colour_support_column : ∀ v : Packet,
    v ∈ colourSupport ↔ RequirementTable.colourDim (channelType v)=3 := by decide +kernel

theorem support_counts : weakSupport.card=8 ∧ colourSupport.card=12 := by
  constructor <;> decide +kernel

theorem commute : ∀ (a b : Fin 3) (v : Packet), weak (colour a b v)=colour a b (weak v) := by
  decide +kernel

/-- Index of the unique nonzero coordinate in the vector-class carrier. -/
def axis (v : V) : Fin 4 :=
  if coord v 1 ≠ 0 then 1 else if coord v 2 ≠ 0 then 2 else if coord v 3 ≠ 0 then 3 else 0

def leftIndex (v : V) : Fin 16 :=
  if positive v then (![12,0,2,4] : Fin 4 → Fin 16) (axis v)
  else (![13,1,3,5] : Fin 4 → Fin 16) (axis v)
def rightIndex (v : V) : Fin 16 :=
  if positive v then (![15,6,7,8] : Fin 4 → Fin 16) (axis v)
  else (![14,9,10,11] : Fin 4 → Fin 16) (axis v)
def index : Packet → Fin 16 := Sum.elim leftIndex rightIndex

theorem index_bijective : Function.Bijective index := by decide +kernel

def enumeration : Packet ≃ Fin 16 := Equiv.ofBijective index index_bijective

theorem type_preserved : ∀ v : Packet, RequirementTable.ty (index v)=channelType v := by
  decide +kernel

/-- The old channel table is connected to actual carrier support by a bijection. -/
theorem indexed_weak_column : ∀ v : Packet,
    ResourceLedger.activeBoundary (index v)=true ↔ v ∈ weakSupport := by decide +kernel

theorem indexed_colour_column : ∀ v : Packet,
    ResourceLedger.colourBulk (index v)=true ↔ v ∈ colourSupport := by decide +kernel

theorem indexed_supports : weakSupport.image index=ResourceLedger.activeSet ∧
    colourSupport.image index=ResourceLedger.colouredSet := by
  constructor <;> decide +kernel

theorem weak_unitary : weak.permMatrix ℂ ∈ unitary (Matrix Packet Packet ℂ) :=
  PMAction.CarrierResponse.perm_unitary weak

theorem colour_unitary (a b : Fin 3) : (colour a b).permMatrix ℂ ∈ unitary (Matrix Packet Packet ℂ) :=
  PMAction.CarrierResponse.perm_unitary (colour a b)

end PMConstants.CarrierActions
