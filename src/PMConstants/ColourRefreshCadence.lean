import PMConstants.CarrierSwapSchedule
import PMConstants.MinimalRefresh
import PMConstants.General.Service

/-! Capability, requests and refresh cadence are distinct operational contracts.
The gate menu is the actual carrier menu from CarrierSwapSchedule. Executability
means an exact two-field-swap implementation using only available fields. A
weighted readiness-refresh law is stated separately from gate execution. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace PMConstants.ColourRefreshCadence
open Finset CarrierSwapSchedule

/-- Immediate gate capability using only the currently available fields. -/
def canExecute (ready : Finset (Fin 16)) (g : Fin 3) : Prop :=
  ∃ L : List Pair, labels L=labels (colourPairs g) ∧ touched L ⊆ ready

def required (requests : Finset (Fin 3)) : Finset (Fin 16) :=
  requests.biUnion (fun g => touched (colourPairs g))

def capable (requests : Finset (Fin 3)) (ready : Finset (Fin 16)) : Prop :=
  ∀ g ∈ requests, canExecute ready g

lemma moved_eq_touched : ∀ g : Fin 3,
    moved (labels (colourPairs g))=touched (colourPairs g) := by decide +kernel

/-- Necessity follows from locality of any implementation; sufficiency has a
concrete reversible witness, rather than an arbitrary coverage list. -/
theorem executable_iff (ready : Finset (Fin 16)) (g : Fin 3) :
    canExecute ready g ↔ touched (colourPairs g) ⊆ ready := by
  constructor
  · rintro ⟨L,hL,hr⟩ i hi
    apply hr
    by_contra hn
    have hm : i ∈ moved (labels L) := by simpa [hL, moved_eq_touched] using hi
    exact (mem_filter.mp hm).2 (fixed_outside L i hn)
  · intro h; exact ⟨colourPairs g,rfl,h⟩

theorem capable_iff (requests : Finset (Fin 3)) (ready : Finset (Fin 16)) :
    capable requests ready ↔ required requests ⊆ ready := by
  simp only [capable, executable_iff, required, biUnion_subset]

theorem required_card : ∀ S : Finset (Fin 3),
    (required S).card=if S.card=0 then 0 else if S.card=1 then 8 else 12 := by
  decide +kernel

/-- Any two different generators already require the full coloured field set. -/
theorem two_requests_full : ∀ S : Finset (Fin 3), 2 ≤ S.card →
    required S=ResourceLedger.colouredSet := by decide +kernel

/-- A composite colour operation can move all twelve fields in a single gate.
The eight-field count for an individual exchange is not a general colour bound. -/
def cyclePairs : List Pair := colourPairs 0 ++ colourPairs 1

theorem cycle_full_support : moved (labels cyclePairs)=ResourceLedger.colouredSet := by
  decide +kernel

theorem cycle_realized : ∀ v : CarrierActions.Packet,
    CarrierActions.index
      (CarrierActions.colour 0 2 (CarrierActions.colour 0 1 v))=
      labels cyclePairs (CarrierActions.index v) := by decide +kernel

theorem full_required : required univ=ResourceLedger.colouredSet := touched_table.2

theorem universal_capability (ready : Finset (Fin 16)) :
    (∀ g, canExecute ready g) ↔ ResourceLedger.colouredSet ⊆ ready := by
  simpa [capable, full_required] using capable_iff univ ready

/-- This counts readiness maintenance only under the additional contract that
all available required fields must be refreshed each phase at the stated weights. -/
theorem readiness_refresh_minimum (requests : Finset (Fin 3))
    (w : Fin 16 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    IsLeast {c | ∃ L : List (Fin 16), capable requests L.toFinset ∧
      MinimalRefresh.cost w L=c} (∑ i ∈ required requests, w i) := by
  have he : ∀ L : List (Fin 16), capable requests L.toFinset ↔
      MinimalRefresh.admissible (required requests) L := by
    intro L
    rw [capable_iff]
    simp only [Finset.subset_iff, MinimalRefresh.admissible, List.mem_toFinset]
  simpa only [← he] using MinimalRefresh.minimal_is_ledger w hw (required requests)

/-- The proposed twelve-field colour ledger follows under universal per-phase
readiness refresh. The hypothesis is operational and stronger than persistence. -/
theorem universal_refresh_minimum :
    IsLeast {c | ∃ L : List (Fin 16), capable univ L.toFinset ∧
      MinimalRefresh.cost (fun _ => overhead) L=c} (12*overhead) := by
  have h := readiness_refresh_minimum univ (fun _ => overhead) (fun _ => overhead_bounds.1.le)
  simpa [full_required, ResourceLedger.coloured_card] using h

/-- One selected generator does not require twelve available fields. -/
theorem singleton_required (g : Fin 3) : (required {g}).card=8 := by
  simp [required, touched_counts.2.1 g]

/-! A finite reversible, fair request scheduler. Its extra three-state
controller is explicit; it is a witness, not a selected vacuum update. -/
abbrev RotorState := Fin 3 × Bits

def controlled : Equiv.Perm RotorState where
  toFun s := (s.1, gate (labels (colourPairs s.1)) s.2)
  invFun s := (s.1, (gate (labels (colourPairs s.1))).symm s.2)
  left_inv s := by rcases s with ⟨g,p⟩; simp
  right_inv s := by rcases s with ⟨g,p⟩; simp

def rotor : Equiv.Perm RotorState :=
  controlled.trans (Equiv.prodCongr (finRotate 3) (Equiv.refl Bits))

abbrev Clocked := Fin 43 × RotorState

def clockedStep : Equiv.Perm Clocked := Equiv.prodCongr (finRotate 43) rotor

theorem finite_state_count : Fintype.card Clocked=43*3*2^16 := by
  simp [Clocked, RotorState, Bits, Fintype.card_prod]

theorem reversible : Function.Injective clockedStep := clockedStep.injective

theorem clock_advance (s : Clocked) : (clockedStep s).1=finRotate 43 s.1 := rfl

theorem request_advance (s : Clocked) : (clockedStep s).2.1=finRotate 3 s.2.1 := rfl

theorem payload_update (s : Clocked) :
    (clockedStep s).2.2=run (colourPairs s.2.1) s.2.2 := by
  change gate (labels (colourPairs s.2.1)) s.2.2=run (colourPairs s.2.1) s.2.2
  rw [run_eq]

theorem population_preserved (s : Clocked) :
    population (clockedStep s).2.2=population s.2.2 := gate_population _ _

def phaseAt (start t : Fin 3) : Fin 3 := ((finRotate 3)^[t.val]) start

theorem request_iterate (n : ℕ) (s : Clocked) :
    ((clockedStep^[n]) s).2.1=((finRotate 3)^[n]) s.2.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', request_advance, ih,
      Function.iterate_succ_apply']

def readyAt (start t : Fin 3) : Finset (Fin 16) := touched (colourPairs (phaseAt start t))

theorem fair_three : ∀ start g : Fin 3, ∃ t, phaseAt start t=g := by decide +kernel

theorem each_phase_eight : ∀ start t : Fin 3, (readyAt start t).card=8 := by decide +kernel

theorem each_phase_capable (start t : Fin 3) : canExecute (readyAt start t) (phaseAt start t) :=
  (executable_iff _ _).mpr (Subset.refl _)

theorem each_phase_omits_four : ∀ start t : Fin 3,
    (ResourceLedger.colouredSet \ readyAt start t).card=4 := by decide +kernel

theorem three_phase_coverage : ∀ start : Fin 3,
    univ.biUnion (readyAt start)=ResourceLedger.colouredSet := by decide +kernel

/-- Every consecutive two-phase window already covers every coloured field. -/
theorem two_phase_coverage : ∀ start : Fin 3,
    readyAt start 0 ∪ readyAt start 1=ResourceLedger.colouredSet := by decide +kernel

/-- Every coloured field is available twice in each three-phase sweep. -/
theorem field_cadence : ∀ (start : Fin 3) (i : Fin 16),
    (univ.filter (fun t => i ∈ readyAt start t)).card=
      if i ∈ ResourceLedger.colouredSet then 2 else 0 := by decide +kernel

/-- If demand charges each addressed field once per request, the cadence gives
24 field charges per sweep, hence eight per phase. Primitive swaps are a
separate count; active swaps also depend on payload contents. -/
def demand (start t : Fin 3) : ℝ := ∑ _i ∈ readyAt start t, overhead

theorem demand_eight (start t : Fin 3) : demand start t=8*overhead := by
  simp [demand, each_phase_eight]

theorem demand_cycle (start : Fin 3) : (∑ t, demand start t)=24*overhead := by
  simp [demand_eight]; ring

theorem mean_demand (start : Fin 3) : (∑ t, demand start t)/3=8*overhead := by
  rw [demand_cycle]; ring

/-- Bounded persistent queues enforce the workload actually supplied; they
cannot replace the request cadence by a universal readiness charge. -/
theorem persistent_request_service (start : Fin 3)
    (q : ℕ → Fin 4 → ℝ) (service : Fin 3 → ℝ) (rate C : ℝ)
    (hstep : ∀ n t, q n t.succ=q n t.castSucc+rate*demand start t-service t)
    (hlink : ∀ n, q (n+1) 0=q n (Fin.last 3))
    (hb : ∀ n, 0 ≤ q n 0 ∧ q n 0 ≤ C) :
    (∑ t, service t)=rate*(24*overhead) := by
  have h := General.Service.persistent_cycle_service q (demand start) service rate C hstep hlink hb
  simpa only [demand_cycle] using h

/-- A zero-backlog, unit-rate service witness exists for this request contract. -/
theorem zero_backlog_witness (start : Fin 3) :
    (∀ (_n : ℕ) (t : Fin 3), (0 : ℝ)=0+1*demand start t-demand start t) ∧
      (∑ t, demand start t) ≠ 3*(12*overhead) := by
  constructor
  · intros; ring
  · rw [demand_cycle]; norm_num [overhead]

end PMConstants.ColourRefreshCadence
