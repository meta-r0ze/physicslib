import PMConstants.CarrierImplementation
import PMConstants.LocalMaintenance

/-! Concrete reversible two-field implementations of the carrier gates.
The primitive here is an internal register swap, not a derived E8 spatial update.
Every intermediate step conserves bit population. Resource weights, clock refresh
and the statistics of active swaps remain separate operational questions. -/
set_option maxHeartbeats 1000000

noncomputable section
namespace PMConstants.CarrierSwapSchedule
open Finset CarrierActions

abbrev Pair := Fin 16 × Fin 16
abbrev Bits := Fin 16 → Bool

def weakPairs : List Pair := [(0,1),(2,3),(4,5),(12,13)]
def colourPairs (g : Fin 3) : List Pair :=
  (![[(0,2),(1,3),(6,7),(9,10)],
     [(0,4),(1,5),(6,8),(9,11)],
     [(2,4),(3,5),(7,8),(10,11)]] : Fin 3 → List Pair) g

def generator (g : Fin 3) : Fin 3 × Fin 3 := ![(0,1),(0,2),(1,2)] g

/-- Schedule order is explicit: the head swap runs first. -/
def labels : List Pair → Equiv.Perm (Fin 16)
  | [] => Equiv.refl _
  | (a,b)::L => (Equiv.swap a b).trans (labels L)

/-- Equality is checked on the actual carrier vectors, through their proved index. -/
theorem weak_realized : ∀ v : Packet, index (weak v)=labels weakPairs (index v) := by
  decide +kernel

theorem colour_realized : ∀ (g : Fin 3) (v : Packet),
    index (colour (generator g).1 (generator g).2 v)=labels (colourPairs g) (index v) := by
  decide +kernel

def gate (e : Equiv.Perm (Fin 16)) : Equiv.Perm Bits where
  toFun p := p ∘ e.symm
  invFun p := p ∘ e
  left_inv p := by funext i; simp
  right_inv p := by funext i; simp

def run : List Pair → Bits → Bits
  | [], p => p
  | (a,b)::L, p => run L (gate (Equiv.swap a b) p)

theorem run_eq (L : List Pair) (p : Bits) : run L p=gate (labels L) p := by
  induction L generalizing p with
  | nil => rfl
  | cons ab L ih =>
    rcases ab with ⟨a,b⟩
    rw [run, ih]
    rfl

/-- This is an exact encoding of the original packet update, not just its counts. -/
def encode (p : CarrierImplementation.Payload) : Bits := p ∘ enumeration.symm

lemma gate_intertwines (e : Equiv.Perm Packet) (f : Equiv.Perm (Fin 16))
    (h : ∀ v, index (e v)=f (index v)) (p : CarrierImplementation.Payload) :
    gate f (encode p)=encode (CarrierImplementation.onPayload e p) := by
  funext i
  change p (enumeration.symm (f.symm i))=p (e.symm (enumeration.symm i))
  congr 1
  apply enumeration.injective
  apply f.injective
  have hh := h (e.symm (enumeration.symm i))
  simp only [Equiv.apply_symm_apply]
  change i=f (index (e.symm (enumeration.symm i)))
  have hi : index (enumeration.symm i)=i := enumeration.apply_symm_apply i
  simpa only [Equiv.apply_symm_apply, hi] using hh

theorem weak_schedule (p : CarrierImplementation.Payload) :
    run weakPairs (encode p)=encode (CarrierImplementation.onPayload weak p) := by
  rw [run_eq]; exact gate_intertwines weak _ weak_realized p

theorem colour_schedule (g : Fin 3) (p : CarrierImplementation.Payload) :
    run (colourPairs g) (encode p)=
      encode (CarrierImplementation.onPayload (colour (generator g).1 (generator g).2) p) := by
  rw [run_eq]; exact gate_intertwines _ _ (colour_realized g) p

def population (p : Bits) : ℕ := ∑ i, (p i).toNat

theorem gate_population (e : Equiv.Perm (Fin 16)) (p : Bits) :
    population (gate e p)=population p := by
  change (∑ i, (p (e.symm i)).toNat)=∑ i, (p i).toNat
  exact Equiv.sum_comp e.symm (fun i => (p i).toNat)

/-- Applies to every prefix, so intermediate states conserve population too. -/
theorem run_population (L : List Pair) (p : Bits) : population (run L p)=population p := by
  rw [run_eq]; exact gate_population _ p

/-- The primitive only exchanges the two addressed fields. -/
theorem primitive_local (a b i : Fin 16) (p : Bits) (ha : i ≠ a) (hb : i ≠ b) :
    gate (Equiv.swap a b) p i=p i := by simp [gate, Equiv.swap_apply_def, ha, hb]

theorem primitive_reversible (a b : Fin 16) :
    Function.Involutive (gate (Equiv.swap a b)) := by
  intro p; funext i; simp [gate]

/-- An inactive primitive has no state transition. -/
theorem primitive_active_iff (a b : Fin 16) (p : Bits) :
    gate (Equiv.swap a b) p ≠ p ↔ p a ≠ p b := by
  constructor
  · contrapose!
    intro h; funext i
    by_cases ha : i=a
    · subst i; simpa [gate] using h.symm
    by_cases hb : i=b
    · subst i; simpa [gate] using h
    simp [gate, Equiv.swap_apply_def, ha, hb]
  · intro h he
    have hh := congrFun he a
    exact h (by simpa [gate] using hh.symm)

/-- Unit primitive-event count along the actual evolving history. -/
def events : List Pair → Bits → ℕ
  | [], _ => 0
  | (a,b)::L, p => (if p a=p b then 0 else 1)+events L (gate (Equiv.swap a b) p)

theorem events_le (L : List Pair) (p : Bits) : events L p ≤ L.length := by
  induction L generalizing p with
  | nil => simp [events]
  | cons ab L ih =>
    rcases ab with ⟨a,b⟩
    simp only [events, List.length_cons]
    split <;> have := ih (gate (Equiv.swap a b) p) <;> omega

theorem four_primitives : weakPairs.length=4 ∧ ∀ g, (colourPairs g).length=4 := by
  decide +kernel

def touched : List Pair → Finset (Fin 16)
  | [] => ∅
  | (a,b)::L => insert a (insert b (touched L))

lemma fixed_outside (L : List Pair) (i : Fin 16) (hi : i ∉ touched L) : labels L i=i := by
  induction L with
  | nil => rfl
  | cons ab L ih =>
    rcases ab with ⟨a,b⟩
    simp only [touched, mem_insert, not_or] at hi
    change labels L (Equiv.swap a b i)=i
    rw [Equiv.swap_apply_of_ne_of_ne hi.1 hi.2.1]
    exact ih hi.2.2

lemma touched_bound (L : List Pair) : (touched L).card ≤ 2*L.length := by
  induction L with
  | nil => simp [touched]
  | cons ab L ih =>
    rcases ab with ⟨a,b⟩
    have h1 := card_insert_le a (insert b (touched L))
    have h2 := card_insert_le b (touched L)
    simp only [touched, List.length_cons]
    omega

def moved (e : Equiv.Perm (Fin 16)) : Finset (Fin 16) := univ.filter (fun i => e i ≠ i)

lemma moved_bound (L : List Pair) : (moved (labels L)).card ≤ 2*L.length := by
  have hs : moved (labels L) ⊆ touched L := by
    intro i hi
    by_contra hn
    exact (mem_filter.mp hi).2 (fixed_outside L i hn)
  exact (card_le_card hs).trans (touched_bound L)

lemma moved_counts : (moved (labels weakPairs)).card=8 ∧
    ∀ g, (moved (labels (colourPairs g))).card=8 := by decide +kernel

/-- Exact optimality within the specified two-field-swap instruction set.
This counts instructions, not active events or an E8 propagation cost. -/
theorem four_minimal (L : List Pair) (e : Equiv.Perm (Fin 16))
    (he : (moved e).card=8) (hL : labels L=e) : 4 ≤ L.length := by
  have h := moved_bound L
  rw [hL, he] at h
  omega

theorem weak_minimal (L : List Pair) (hL : labels L=labels weakPairs) : 4 ≤ L.length :=
  four_minimal L _ moved_counts.1 hL

theorem colour_minimal (g : Fin 3) (L : List Pair)
    (hL : labels L=labels (colourPairs g)) : 4 ≤ L.length :=
  four_minimal L _ (moved_counts.2 g) hL

theorem touched_counts : (touched weakPairs).card=8 ∧
    (∀ g, (touched (colourPairs g)).card=8) ∧
    ((univ : Finset (Fin 3)).biUnion (fun g => touched (colourPairs g))).card=12 := by
  decide +kernel

theorem touched_table : touched weakPairs=ResourceLedger.activeSet ∧
    (univ : Finset (Fin 3)).biUnion (fun g => touched (colourPairs g))=ResourceLedger.colouredSet := by
  decide +kernel

/-- Same gate, finite conservative dynamics, different activation counts.
Neither a constant four-event cost nor an ensemble is forced by the schedule. -/
def zero : Bits := fun _ => false
def alternating : Bits := fun i => i.val % 2=0

theorem weak_event_witnesses : events weakPairs zero=0 ∧ events weakPairs alternating=4 := by
  decide +kernel

end PMConstants.CarrierSwapSchedule
