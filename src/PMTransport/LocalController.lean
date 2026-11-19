import PMTransport.Interface

/-!
# Autonomous guards for the two-stream update

This encoding checks the shift followed by an on-site choice of exchange or
bypass. The guard reads the retained trial requests and the two arriving
port values. A Boolean names either of two distinct supplied port values.
A second Boolean names a point on a supplied moving root orbit. This is
a finite test of the certified operations, with no physical preparation
or writer encoding assumed.
-/

namespace PMTransport.LocalController

open PMAction

abbrev Requests := Bool × Bool
abbrev Ports := Bool × Bool
abbrev Phase := Fin Delta
abbrev Guard := Ports → Bool
abbrev Rule := Phase → Requests → Guard
abbrev Registers := (ℤ → Requests × Bool) × OpenReferenceFlow.State ℤ Bool
abbrev State := Phase × Registers

/-- Exchange the two arrivals or keep their order. -/
def applyGuard (guard : Guard) (p : Ports) : Ports :=
  if guard p then (p.2, p.1) else p

/-- The discrete labels of a supplied reflection orbit. -/
def orbitPoint (z : SubstrateReflection.Lattice) (side : Bool) :
    SubstrateReflection.Lattice :=
  if side then SubstrateReflection.reflect z else z

def advanceProbe (phase : Phase) (c : Requests × Bool) : Requests × Bool :=
  (c.1, if ClockedRootTrials.fire c.1 phase then !c.2 else c.2)

theorem probe_realises_trial (phase : Phase) (c : Requests × Bool)
    (z : SubstrateReflection.Lattice) :
    ClockedRootTrials.tick (c.1, (orbitPoint z c.2, phase)) =
      ((advanceProbe phase c).1,
        (orbitPoint z (advanceProbe phase c).2, finRotate Delta phase)) := by
  change (c.1, (if ClockedRootTrials.fire c.1 phase then
    SubstrateReflection.reflect (orbitPoint z c.2) else orbitPoint z c.2,
    finRotate Delta phase)) = _
  rcases c with ⟨requests, side⟩
  cases side <;> cases h : ClockedRootTrials.fire requests phase <;>
    simp [advanceProbe, orbitPoint, h, SubstrateReflection.involutive z]

/-- The common stream shift precedes the guarded local step. The guard
    reads only the two arrivals and the retained controller at this site. -/
def rawStep (rule : Rule) (phase : Phase) (s : Registers) : Registers :=
  (advanceProbe phase ∘ s.1, fun x =>
    applyGuard (rule phase (s.1 x).1) (OpenReferenceFlow.streamShift OpenReferenceFlow.line s.2 x))

def rawTick (rule : Rule) (s : State) : State :=
  (finRotate Delta s.1, rawStep rule s.1 s.2)

theorem radius_one (rule : Rule) (phase : Phase) (s t : Registers) (x : ℤ)
    (hc : s.1 x = t.1 x) (hl : (s.2 (x - 1)).1 = (t.2 (x - 1)).1)
    (hr : (s.2 (x + 1)).2 = (t.2 (x + 1)).2) :
    (rawStep rule phase s).1 x = (rawStep rule phase t).1 x ∧
    (rawStep rule phase s).2 x = (rawStep rule phase t).2 x := by
  constructor
  · exact congrArg (advanceProbe phase) hc
  · change applyGuard (rule phase (s.1 x).1) ((s.2 (x - 1)).1, (s.2 (x + 1)).2) =
      applyGuard (rule phase (t.1 x).1) ((t.2 (x - 1)).1, (t.2 (x + 1)).2)
    rw [hc, hl, hr]

theorem receiver_realisation (rule : Rule) (phase : Phase) (s : Registers) (x : ℤ)
    (edge : TwoSiteHandoff.State Bool)
    (h : edge 1 = OpenReferenceFlow.streamShift OpenReferenceFlow.line s.2 x) :
    (rawStep rule phase s).2 x = TwoSiteHandoff.step (rule phase (s.1 x).1 (edge 1)) edge 0 := by
  rw [(TwoSiteHandoff.step_trace _ edge).1]
  change applyGuard (rule phase (s.1 x).1) (OpenReferenceFlow.streamShift OpenReferenceFlow.line s.2 x) = _
  rw [← h]
  rfl


/-- The two unequal arrivals must use the same decision. Equal arrivals
    can use either operation and still keep their values. -/
def Compatible (guard : Guard) : Prop :=
  guard (false, true) = guard (true, false)

instance (guard : Guard) : Decidable (Compatible guard) :=
  inferInstanceAs (Decidable (guard (false, true) = guard (true, false)))

private theorem compatible_twice :
    ∀ (guard : Guard), Compatible guard → ∀ p : Ports,
      applyGuard guard (applyGuard guard p) = p := by
  decide +kernel

private theorem incompatible_collision :
    ∀ (guard : Guard), ¬ Compatible guard →
      applyGuard guard (false, true) = applyGuard guard (true, false) := by
  decide +kernel

private def scatter (rule : Rule) (phase : Phase) (s : Registers) : Registers :=
  (advanceProbe phase ∘ s.1, fun x => applyGuard (rule phase (s.1 x).1) (s.2 x))

private theorem scatter_involutive (rule : Rule) (phase : Phase)
    (h : ∀ c, Compatible (rule phase c)) :
    Function.Involutive (scatter rule phase) := by
  intro s
  apply Prod.ext
  · funext x
    change advanceProbe phase (advanceProbe phase (s.1 x)) = s.1 x
    rcases s.1 x with ⟨requests, side⟩
    cases hf : ClockedRootTrials.fire requests phase <;> simp [advanceProbe, hf]
  · funext x
    exact compatible_twice _ (h (s.1 x).1) _

/-- The whole line update is reversible exactly for the compatible rows.
    The inverse undoes the new clock phase, then the local operation,
    then the two-stream shift. -/
theorem reversible_iff_rows (rule : Rule) :
    Function.Bijective (rawTick rule) ↔ ∀ phase c, Compatible (rule phase c) := by
  constructor
  · intro h phase c
    by_contra hn
    let s : State := (phase, (fun _ => (c, false), fun _ => (false, true)))
    let t : State := (phase, (fun _ => (c, false), fun _ => (true, false)))
    have hg := incompatible_collision (rule phase c) hn
    have he : rawTick rule s = rawTick rule t := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · funext x
          exact hg
    have hp := congrArg (fun u : State => (u.2.2 0).1) (h.1 he)
    exact Bool.false_ne_true hp
  · intro h
    let step (phase : Phase) : Equiv.Perm Registers :=
      (Equiv.prodCongr (Equiv.refl _) (OpenReferenceFlow.shiftEquiv OpenReferenceFlow.line)).trans
        ((scatter_involutive rule phase (h phase)).toPerm _)
    let full : Equiv.Perm State :=
      (Equiv.prodCongrRight step).trans (Equiv.prodCongr (finRotate Delta) (Equiv.refl _))
    exact full.bijective

/-- Enumerate the 16 possible Boolean rows individually. No row is
    identified with another, even when their output values coincide. -/
def reversibleRows : Finset Guard := Finset.univ.filter Compatible

theorem reversible_rows_count : reversibleRows.card = 8 := by
  decide +kernel

/-- An independent certified row at each phase and request pair. -/
abbrev EnumeratedRule := Phase → Requests → ↥reversibleRows

def EnumeratedRule.rule (table : EnumeratedRule) : Rule :=
  fun phase c => (table phase c).val

theorem enumerated_rule_iff (rule : Rule) :
    Function.Bijective (rawTick rule) ↔
      ∃ table : EnumeratedRule, table.rule = rule := by
  rw [reversible_iff_rows]
  constructor
  · intro h
    exact ⟨fun phase c => ⟨rule phase c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h phase c⟩⟩,
      rfl⟩
  · rintro ⟨table, rfl⟩ phase c
    exact (Finset.mem_filter.mp (table phase c).property).2

theorem enumerated_rule_count : Fintype.card EnumeratedRule = 8 ^ (4 * 43) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_coe, reversible_rows_count, ← pow_mul]
  simp [Requests]


/-- Read the independently supplied root probe at one node. -/
def readTrial (z : SubstrateReflection.Lattice) (x : ℤ) (s : State) :
    Requests × ClockControlledRoot.State :=
  ((s.2.1 x).1, (orbitPoint z (s.2.1 x).2, s.1))

theorem read_trial_iterate (rule : Rule) (z : SubstrateReflection.Lattice)
    (x : ℤ) (s : State) (n : ℕ) :
    readTrial z x ((rawTick rule)^[n] s) =
      (ClockedRootTrials.tick^[n]) (readTrial z x s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    exact (probe_realises_trial _ _ z).symm

/-- Equal uniform ports stay equal through every guard table. -/
theorem uniform_ports_iterate (rule : Rule) (s : State) (v : Bool)
    (hs : ∀ x, s.2.2 x = (v, v)) (n : ℕ) :
    ∀ x, ((rawTick rule)^[n] s).2.2 x = (v, v) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply']
    change applyGuard _ (((((rawTick rule)^[n]) s).2.2 (x - 1)).1,
      ((((rawTick rule)^[n]) s).2.2 (x + 1)).2) = (v, v)
    rw [ih (x - 1), ih (x + 1)]
    simp [applyGuard]

/-- Conditional attachment of the open receiver pattern to internal tags. -/
def OpenCompatible (rule : Rule) : Prop :=
  ∀ phase p, rule phase (false, false) p = false ∧ rule phase (true, true) p = true

def CentreTagged (s : State) : Prop :=
  ∀ x, (s.2.1 x).1 = if x = 0 then (true, true) else (false, false)

theorem tagged_open_iterate (rule : Rule) (h : OpenCompatible rule)
    (s : State) (hs : CentreTagged s) (n : ℕ) :
    ((rawTick rule)^[n] s).2.2 = OpenHandoff.run s.2.2 n := by
  have keep (k : ℕ) : CentreTagged ((rawTick rule)^[k] s) := by
    induction k with
    | zero => exact hs
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply']
      exact ih x
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := keep n
    let u := (rawTick rule)^[n] s
    rw [Function.iterate_succ_apply']
    unfold OpenHandoff.run
    rw [Function.iterate_succ_apply', ← show u.2.2 =
      (OpenReferenceFlow.evolution 0 OpenReferenceFlow.line)^[n] s.2.2 from ih]
    funext x
    have hx := ht x
    change (u.2.1 x).1 = _ at hx
    simp only [OpenReferenceFlow.evolution_apply]
    change applyGuard (rule u.1 (u.2.1 x).1)
      (((u.2.2) (x - 1)).1, ((u.2.2) (x + 1)).2) = _
    rw [hx]
    by_cases h0 : x = 0
    · simp [h0, applyGuard, (h _ _).2, OpenReferenceFlow.line]
    · simp [h0, applyGuard, (h _ _).1, OpenReferenceFlow.line]

def exchangeOnBoth : Rule := fun _ c _ => c.1 && c.2
def exchangeOnEither : Rule := fun _ c _ => c.1 || c.2

/-- Even requiring identical certified open-line traces for the tagged
    receiver leaves different autonomous rules on mixed requests. -/
theorem two_open_compatible_rules :
    Function.Bijective (rawTick exchangeOnBoth) ∧ OpenCompatible exchangeOnBoth ∧
      Function.Bijective (rawTick exchangeOnEither) ∧ OpenCompatible exchangeOnEither ∧
      exchangeOnBoth ≠ exchangeOnEither := by
  refine ⟨(reversible_iff_rows _).mpr (fun _ _ => rfl), fun _ _ => ⟨rfl, rfl⟩,
    (reversible_iff_rows _).mpr (fun _ _ => rfl), fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  intro h
  have hc := congrArg (fun f : Rule => f 0 (true, false) (false, true)) h
  exact Bool.false_ne_true hc

theorem mixed_requests_different_destinations (s : State) (x : ℤ)
    (hc : (s.2.1 x).1 = (true, false)) (hl : (s.2.2 (x - 1)).1 = false)
    (hr : (s.2.2 (x + 1)).2 = true) :
    (rawTick exchangeOnBoth s).2.2 x = (false, true) ∧
      (rawTick exchangeOnEither s).2.2 x = (true, false) := by
  change applyGuard (exchangeOnBoth s.1 (s.2.1 x).1)
      ((s.2.2 (x - 1)).1, (s.2.2 (x + 1)).2) = _ ∧
    applyGuard (exchangeOnEither s.1 (s.2.1 x).1)
      ((s.2.2 (x - 1)).1, (s.2.2 (x + 1)).2) = _
  rw [hc, hl, hr]
  exact ⟨rfl, rfl⟩


open scoped BigOperators

/-- The output comparison account for one supplied exchange decision. -/
noncomputable def exchangeFlag (guard : Guard) (p : Ports)
    (value : Bool → Fin 2 → ℂ) : ℝ :=
  if guard p then CommonResponse.nsq (value p.1 - value p.2) / 2 else 0

theorem exchange_flag_realisation (guard : Guard) (p : Ports)
    (value : Bool → Fin 2 → ℂ) (edge : TwoSiteHandoff.State (Fin 2 → ℂ))
    (h : edge 1 = (value p.1, value p.2)) :
    exchangeFlag guard p value =
      if guard p then CommonResponse.stateFlag (TwoSiteHandoff.receiverRoot.permMatrix ℂ)
        (TwoSiteHandoff.field (TwoSiteHandoff.step false edge)) else 0 := by
  rw [TwoSiteHandoff.exchange_flag, h]
  rfl

/-- For a supplied weighted set of visits, sum the certified exchange
    output flags along a trace. The caller supplies the paid visits and
    their weights. The shift, root trial and other accounts are separate. -/
noncomputable def traceExchangeToll (rule : Rule) (s : State) (x : ℤ)
    (value : Bool → Fin 2 → ℂ) {N : ℕ} (weights : Fin N → ℝ) : ℝ :=
  TollAmplitude.scheduleToll 0 weights fun j =>
    let state := (rawTick rule)^[j.val] s
    exchangeFlag (rule state.1 (state.2.1 x).1)
      (OpenReferenceFlow.streamShift OpenReferenceFlow.line state.2.2 x) value

theorem uniform_trace_exchange_toll (rule : Rule) (s : State) (x : ℤ) (v : Bool)
    (hs : ∀ i, s.2.2 i = (v, v)) (value : Bool → Fin 2 → ℂ)
    {N : ℕ} (weights : Fin N → ℝ) :
    traceExchangeToll rule s x value weights = 0 := by
  unfold traceExchangeToll TollAmplitude.scheduleToll
  simp only [zero_add]
  apply Finset.sum_eq_zero
  intro j _
  have hl := uniform_ports_iterate rule s v hs j.val (x - 1)
  have hr := uniform_ports_iterate rule s v hs j.val (x + 1)
  change weights j * exchangeFlag _ (((((rawTick rule)^[j.val]) s).2.2 (x - 1)).1,
    ((((rawTick rule)^[j.val]) s).2.2 (x + 1)).2) value = 0
  rw [hl, hr]
  simp [exchangeFlag, LinkExpansion.nsq_eq]

/-- On a homogeneous supplied input, every member of a supplied family
    ties in the certified exchange flag account with a common baseline. -/
theorem uniform_flag_persistence_tie (F : Set Rule) (i : Rule) (hi : i ∈ F)
    (s : State) (x : ℤ) (v : Bool) (hs : ∀ j, s.2.2 j = (v, v))
    (value : Bool → Fin 2 → ℂ) {N : ℕ} (weights : Fin N → ℝ) (baseline : ℝ) :
    ∀ j ∈ F,
      TollAmplitude.wireAmplitude (baseline + traceExchangeToll j s x value weights) ≤
      TollAmplitude.wireAmplitude (baseline + traceExchangeToll i s x value weights) := by
  let cost := fun rule => traceExchangeToll rule s x value weights
  have h := (PersistenceSelection.within_family_iff_cheapest (1 / 2) (by norm_num)
    cost F baseline i).mpr ⟨hi, fun j _ => by
      simp only [cost, uniform_trace_exchange_toll _ s x v hs value weights, le_refl]⟩
  intro j hj
  simpa [TollAmplitude.wireAmplitude, cost, div_eq_mul_inv, mul_comm] using h.2 j hj

/-- On these inputs a strict preference requires a difference in the
    remaining paid work. The certified exchange flags cancel. -/
theorem uniform_remaining_cost_iff (a b : Rule) (s : State) (x : ℤ) (v : Bool)
    (hs : ∀ j, s.2.2 j = (v, v)) (value : Bool → Fin 2 → ℂ)
    {N : ℕ} (weights : Fin N → ℝ) (remaining : Rule → ℝ) :
    TollAmplitude.wireAmplitude (traceExchangeToll b s x value weights + remaining b) <
        TollAmplitude.wireAmplitude (traceExchangeToll a s x value weights + remaining a) ↔
      remaining a < remaining b := by
  rw [TollAmplitude.wireAmplitude_lt_iff,
    uniform_trace_exchange_toll a s x v hs value weights,
    uniform_trace_exchange_toll b s x v hs value weights]
  simp

end PMTransport.LocalController
