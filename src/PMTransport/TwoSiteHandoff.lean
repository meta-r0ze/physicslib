import PMTransport.Machine.NativeCarrierProtocol
import PMTransport.Machine.OpenReferenceFlow

/-!
# A two-site handoff on the native carrier ports

Sites 1 and 0 are the sender and receiver. The two-site edge transports
both streams. Bypass ends after this transport. Exchange applies the
existing receiver root after arrival and retains the other arriving state
in the record port. The finite edge is closed, so it also tests repeat
operation with a returning record. The spatial update and occupied
preparation are supplied. The root time is conditional on admitting the
reconstructed phase at the receiver.
-/

noncomputable section
namespace PMTransport.TwoSiteHandoff

open Matrix PMAction
open scoped Matrix.Norms.Operator

abbrev Site := Fin 2
abbrev Carrier := ActualRootRepair.C
abbrev State (V : Type*) := OpenReferenceFlow.State Site V

/-- Two sites with two live and two record carrier modes at each site. -/
theorem port_count : Fintype.card (Site × ActualRootRepair.Ports) = 8 := by
  decide +kernel

def edge : Equiv.Perm Site := Equiv.swap 0 1

/-- Bypass is the stream lookup extended to all labels at the two sites. -/
def hop : Equiv.Perm (Site × Carrier) :=
  (NativeCarrierProtocol.stream edge).viaEmbedding NativeCarrierProtocol.labels

private theorem hop_unused (x : Site) (c : Carrier)
    (hc : c ∉ Set.range ActualRootRepair.label) : hop (x, c) = (x, c) := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨⟨y, j⟩, h⟩
  exact hc ⟨j, congrArg Prod.snd h⟩

/-- The existing root acts on the receiver. The sender is fixed. -/
def receiverRoot : Equiv.Perm (Site × Carrier) :=
  Equiv.prodCongrRight fun x => if x = 0 then ActualRootRepair.root else Equiv.refl Carrier

theorem receiverRoot_involutive : Function.Involutive receiverRoot := by
  rintro ⟨x, c⟩
  by_cases h : x = 0
  · simp [receiverRoot, h, CarrierEvents.reflection_involutive 0 c]
  · simp [receiverRoot, h]

/-- Factor the native exchange lookup into the receiver root and the stream
lookup. In the corresponding amplitude update the stream executes first. -/
theorem exchange_lookup : receiverRoot.trans hop = NativeCarrierProtocol.lookup 0 edge := by
  apply Equiv.ext
  rintro ⟨x, c⟩
  by_cases hc : c ∈ Set.range ActualRootRepair.label
  · obtain ⟨j, rfl⟩ := hc
    have hr : receiverRoot (x, ActualRootRepair.label j) =
        NativeCarrierProtocol.labels (NativeCarrierProtocol.couple 0 (x, j)) := by
      by_cases hx : x = 0 <;>
        simp [receiverRoot, NativeCarrierProtocol.couple, hx, ActualRootRepair.label_exchange]
    rw [NativeCarrierProtocol.lookup_label, Equiv.trans_apply, hr, hop,
      Equiv.Perm.viaEmbedding_apply]
    rfl
  · have hfix : ActualRootRepair.root c = c := by
      have hn : c ∉ CarrierEvents.active 0 := by
        rw [← ActualRootRepair.moving_modes_exact]
        simpa using hc
      simpa [CarrierEvents.active] using hn
    rw [NativeCarrierProtocol.lookup_unused _ _ _ _ hc]
    have hr : receiverRoot (x, c) = (x, c) := by
      by_cases hx : x = 0 <;> simp [receiverRoot, hx, hfix]
    rw [Equiv.trans_apply, hr, hop_unused x c hc]

def step (exchange : Bool) {V : Type*} : State V ≃ State V :=
  if exchange then OpenReferenceFlow.evolution 0 edge else OpenReferenceFlow.shiftEquiv edge

/-- The order of the actual two primitive visits, with a supplied decision
whether to invoke the receiver root. -/
def nativeStep (exchange : Bool) : Matrix (Site × Carrier) (Site × Carrier) ℂ :=
  if exchange then receiverRoot.permMatrix ℂ * hop.permMatrix ℂ else hop.permMatrix ℂ

theorem native_step_unitary (exchange : Bool) : nativeStep exchange ∈ unitary _ := by
  cases exchange
  · exact CarrierResponse.perm_unitary hop
  · exact mul_mem (CarrierResponse.perm_unitary receiverRoot) (CarrierResponse.perm_unitary hop)

def field (s : State (Fin 2 → ℂ)) : Site × Carrier → ℂ :=
  RootCarrierWalk.field (fun x => (s x).1) (fun x => (s x).2)

theorem arrivals_observed (s : State (Fin 2 → ℂ)) :
    hop.permMatrix ℂ *ᵥ field s = field (step false s) := by
  rw [Matrix.permMatrix_mulVec]
  ext p
  rcases p with ⟨x, c⟩
  by_cases hc : c ∈ Set.range ActualRootRepair.label
  · obtain ⟨j, rfl⟩ := hc
    change field s (hop (x, ActualRootRepair.label j)) = _
    rw [← NativeCarrierProtocol.labels_apply (x, j)]
    rw [hop, Equiv.Perm.viaEmbedding_apply, NativeCarrierProtocol.labels_apply]
    rcases j with i | i <;>
      simp [field, step, OpenReferenceFlow.shiftEquiv, OpenReferenceFlow.streamShift,
        NativeCarrierProtocol.stream, RootCarrierWalk.field, ActualRootRepair.pack,
        ActualRootRepair.encoded_coordinate]
  · change field s (hop (x, c)) = field (step false s) (x, c)
    rw [hop_unused x c hc]
    exact (NativeCarrierProtocol.field_unused
      (fun y => (s y).1) (fun y => (s y).2) x c hc).trans
      (NativeCarrierProtocol.field_unused
        (fun y => (step false s y).1) (fun y => (step false s y).2) x c hc).symm

theorem native_step_observed (exchange : Bool) (s : State (Fin 2 → ℂ)) :
    nativeStep exchange *ᵥ field s = field (step exchange s) := by
  cases exchange
  · exact arrivals_observed s
  · change (receiverRoot.permMatrix ℂ * hop.permMatrix ℂ) *ᵥ field s = _
    have h : hop * receiverRoot = NativeCarrierProtocol.lookup 0 edge := exchange_lookup
    rw [← Matrix.permMatrix_mul, h]
    unfold field
    rw [NativeCarrierProtocol.field_step]
    congr 1 <;> funext x <;>
      by_cases hx : x = 0 <;> simp [step, OpenReferenceFlow.evolution_apply, hx]

/-- Complete register trace. Both incoming states arrive at the receiver.
Exchange swaps their roles. The old receiver pair goes to the sender. -/
theorem step_trace {V : Type*} (exchange : Bool) (s : State V) :
    step exchange s 0 = (if exchange then ((s 1).2, (s 1).1) else s 1) ∧
      step exchange s 1 = s 0 := by
  cases exchange <;> constructor <;> rfl

/-- The closed edge gives the same receiver update as the open line when
its two arrivals are the line's independently supplied incoming states. -/
theorem receiver_agrees_with_line {V : Type*} (exchange : Bool) (s : State V)
    (lineState : OpenReferenceFlow.State ℤ V)
    (arrivals : s 1 = ((lineState (-1)).1, (lineState 1).2)) :
    step exchange s 0 =
      if exchange then OpenReferenceFlow.evolution 0 OpenReferenceFlow.line lineState 0
      else OpenReferenceFlow.streamShift OpenReferenceFlow.line lineState 0 := by
  rw [(step_trace exchange s).1, arrivals]
  cases exchange <;> rfl

/-- The state in the receiver record port after the visit is at the sender
after the next shift. On this closed edge the export returns to the sender. -/
theorem export_trace {V : Type*} (exchange : Bool) (s : State V) :
    step false (step exchange s) 1 =
      if exchange then ((s 1).2, (s 1).1) else s 1 := by
  rw [(step_trace false _).2, (step_trace exchange s).1]

/-- The first exchange restores the live register exactly when the arriving
record holds the reference. The other arrival is retained in the record port. -/
theorem first_reference_iff {V : Type*} (s : State V) (reference : V) :
    (step true s 0).1 = reference ↔ (s 1).2 = reference :=
  Iff.rfl

/-- A second exchange needs the original receiver record as its reference.
The first exchange alone does not supply it. -/
theorem second_reference_iff {V : Type*} (s : State V) (reference : V) :
    (step true (step true s) 0).1 = reference ↔ (s 0).2 = reference := by
  rw [(step_trace true _).1]
  simp only [ite_true]
  rw [(step_trace true s).2]

theorem exchange_four_returns {V : Type*} (s : State V) :
    (step true)^[4] s = s := by
  funext x
  fin_cases x <;> rfl

/-- Four successive receiver outputs sample all four initial slots.
A closed pair restores the reference throughout that period exactly when
every slot already holds it. -/
theorem four_restorations_iff {V : Type*} (s : State V) (reference : V) :
    (∀ k : Fin 4, (((step true)^[k.val + 1]) s 0).1 = reference) ↔
      s = fun _ => (reference, reference) := by
  constructor
  · intro h
    have senderRecord : (s 1).2 = reference := h 0
    have receiverRecord : (s 0).2 = reference := h 1
    have senderLive : (s 1).1 = reference := h 2
    have receiverLive : (s 0).1 = reference := h 3
    funext x
    fin_cases x
    · exact Prod.ext receiverLive receiverRecord
    · exact Prod.ext senderLive senderRecord
  · rintro rfl k
    fin_cases k <;> rfl

private theorem field_sub (s t : State (Fin 2 → ℂ)) :
    field s - field t =
      field (fun x => ((s x).1 - (t x).1, (s x).2 - (t x).2)) := by
  funext ⟨x, c⟩
  change (ActualRootRepair.pack (s x).1 (s x).2 -
    ActualRootRepair.pack (t x).1 (t x).2) c = _
  simp only [field, RootCarrierWalk.field, ActualRootRepair.pack]
  rw [← Matrix.mulVec_sub]
  congr 1
  funext j
  cases j <;> rfl

private theorem field_population (s : State (Fin 2 → ℂ)) :
    CommonResponse.nsq (field s) =
      ∑ x, (CommonResponse.nsq (s x).1 + CommonResponse.nsq (s x).2) := by
  rw [LinkExpansion.nsq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ c, Complex.normSq (ActualRootRepair.pack (s x).1 (s x).2 c)) = _
  rw [← LinkExpansion.nsq_eq, ActualRootRepair.population]

private theorem nsq_sub_comm (a b : Fin 2 → ℂ) :
    CommonResponse.nsq (a - b) = CommonResponse.nsq (b - a) := by
  rw [show a - b = -(b - a) by abel]
  simp only [LinkExpansion.nsq_eq, Pi.neg_apply, Complex.normSq_neg]

/-- The spatial comparison sees the initial discrepancy in both streams. -/
theorem hop_flag (s : State (Fin 2 → ℂ)) :
    CommonResponse.stateFlag (hop.permMatrix ℂ) (field s) =
      (CommonResponse.nsq ((s 0).1 - (s 1).1) +
        CommonResponse.nsq ((s 0).2 - (s 1).2)) / 2 := by
  rw [CommonResponse.stateFlag, arrivals_observed, field_sub, field_population]
  simp only [Fin.sum_univ_two, (step_trace false s).1, (step_trace false s).2,
    Bool.false_eq_true, ite_false]
  rw [nsq_sub_comm (s 1).1 (s 0).1, nsq_sub_comm (s 1).2 (s 0).2]
  ring

/-- Only the receiver contributes to the second comparison. Its flag is the
discrepancy of the two states that arrived, including the supplied reference. -/
theorem exchange_flag (s : State (Fin 2 → ℂ)) :
    CommonResponse.stateFlag (receiverRoot.permMatrix ℂ) (field (step false s)) =
      CommonResponse.nsq ((s 1).1 - (s 1).2) / 2 := by
  have hs := native_step_observed true s
  change (receiverRoot.permMatrix ℂ * hop.permMatrix ℂ) *ᵥ field s = _ at hs
  rw [← Matrix.mulVec_mulVec, arrivals_observed] at hs
  rw [CommonResponse.stateFlag, hs, field_sub, field_population]
  simp only [Fin.sum_univ_two, (step_trace false s).1, (step_trace false s).2,
    (step_trace true s).1, (step_trace true s).2, Bool.false_eq_true, ite_false, ite_true,
    sub_self]
  have hz : CommonResponse.nsq (0 : Fin 2 → ℂ) = 0 := by simp [LinkExpansion.nsq_eq]
  rw [nsq_sub_comm (s 1).2 (s 1).1, hz]
  ring

/-- Conditional receiver duration for the reconstructed phase. The separate
spatial visit still has its own physical timing. -/
theorem receiver_half_pulse (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    RootTransferPhase.phase receiverRoot p (2 * RootTransferPhase.quarterTime p) =
      receiverRoot.permMatrix ℂ :=
  RootTransferPhase.half_pulse _ receiverRoot_involutive p hp hp'

end PMTransport.TwoSiteHandoff
