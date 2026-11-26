import PMKAutomaton.Interface

/-!
# Autonomous guards for the two-stream update

This encoding checks the shift followed by an on-site choice of exchange or
bypass. The guard reads the retained trial requests and the two arriving
port values. A Boolean names either of two distinct supplied port values.
A second Boolean names a point on a supplied moving root orbit. This is
a finite test of the certified operations, with no physical preparation
or writer encoding assumed.
-/

namespace PMKAutomaton.LocalController

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

theorem guard_decisions_eq_iff (phase : Phase) (c : Requests) (p : Ports) :
    exchangeOnBoth phase c p = exchangeOnEither phase c p ↔ c.1 = c.2 := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> simp [exchangeOnBoth, exchangeOnEither]

theorem guard_outputs_eq_iff (phase : Phase) (c : Requests) (p : Ports) :
    applyGuard (exchangeOnBoth phase c) p = applyGuard (exchangeOnEither phase c) p ↔
      c.1 = c.2 ∨ p.1 = p.2 := by
  rcases c with ⟨a, b⟩
  rcases p with ⟨l, r⟩
  cases a <;> cases b <;> cases l <;> cases r <;>
    simp [exchangeOnBoth, exchangeOnEither, applyGuard]

/-- At a common start the phase, requests and probe evolve independently
    of the receiver guard. -/
theorem control_iterates_eq (a b : Rule) (s : State) (n : ℕ) :
    (((rawTick a)^[n] s).1, ((rawTick a)^[n] s).2.1) =
      (((rawTick b)^[n] s).1, ((rawTick b)^[n] s).2.1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg (fun q : Phase × (ℤ → Requests × Bool) =>
      (finRotate Delta q.1, advanceProbe q.1 ∘ q.2)) ih

/-- The tagged open route agrees as a full retained state at every tick,
    including the request and probe fields, from the same start. -/
theorem tagged_ticks_equal (s : State) (hs : CentreTagged s) (n : ℕ) :
    (rawTick exchangeOnBoth)^[n] s = (rawTick exchangeOnEither)^[n] s := by
  have h := control_iterates_eq exchangeOnBoth exchangeOnEither s n
  have ha : OpenCompatible exchangeOnBoth := fun _ _ => ⟨rfl, rfl⟩
  have hb : OpenCompatible exchangeOnEither := fun _ _ => ⟨rfl, rfl⟩
  refine Prod.ext (congrArg (fun c : Phase × (ℤ → Requests × Bool) => c.1) h) ?_
  exact Prod.ext (congrArg (fun c : Phase × (ℤ → Requests × Bool) => c.2) h)
    ((tagged_open_iterate _ ha s hs n).trans (tagged_open_iterate _ hb s hs n).symm)

/-- Any read of the common tagged trace is invariant under the rule
    choice. This statement applies to supplied readouts at fixed inputs. -/
theorem tagged_trace_observable_eq {A : Type*} (readout : (ℕ → State) → A)
    (s : State) (hs : CentreTagged s) :
    readout (fun n => (rawTick exchangeOnBoth)^[n] s) =
      readout (fun n => (rawTick exchangeOnEither)^[n] s) :=
  congrArg readout (funext (tagged_ticks_equal s hs))

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


/-- One mixed receiver and one arriving marked value. All other
    receivers have idle requests. -/
def mixedArrival : State :=
  (0, (fun x => ((decide (x = 0), false), false),
    fun x => (false, decide (x = 1))))

theorem mixed_open_receiver_ports :
    (rawTick exchangeOnBoth mixedArrival).2.2 0 = (false, true) ∧
      (rawTick exchangeOnEither mixedArrival).2.2 0 = (true, false) :=
  mixed_requests_different_destinations mixedArrival 0 rfl rfl rfl

/-- The next shift sends the marked arrival through to the record at
    minus one under AND, or back to the live port at plus one under OR. -/
theorem mixed_open_receiver_destinations :
    ((rawTick exchangeOnBoth)^[2] mixedArrival).2.2 (-1) = (false, true) ∧
      ((rawTick exchangeOnBoth)^[2] mixedArrival).2.2 1 = (false, false) ∧
      ((rawTick exchangeOnEither)^[2] mixedArrival).2.2 (-1) = (false, false) ∧
      ((rawTick exchangeOnEither)^[2] mixedArrival).2.2 1 = (true, false) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Complementing the requests -/

def complementRequests (c : Requests) : Requests := (!c.1, !c.2)

theorem complemented_guard (phase : Phase) (c : Requests) (p : Ports) :
    exchangeOnEither phase (complementRequests c) p = !exchangeOnBoth phase c p := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- De Morgan's law compares two decisions on the same arrivals.
    It appends a swap to the AND output. -/
theorem complemented_output (phase : Phase) (c : Requests) (p : Ports) :
    applyGuard (exchangeOnEither phase (complementRequests c)) p =
      (applyGuard (exchangeOnBoth phase c) p).swap := by
  rcases c with ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- The proposed state relabeling complements local requests and swaps
    the live and record values. The clock and probe side are kept. -/
def receiverDual (s : State) : State :=
  (s.1, (fun x => (complementRequests (s.2.1 x).1, (s.2.1 x).2),
    fun x => (s.2.2 x).swap))

/-- The output swap identity does not intertwine the ticks. A field with
    two different constant streams already distinguishes the port outputs. -/
theorem receiver_dual_not_conjugate :
    ¬ ∀ s : State,
      receiverDual (rawTick exchangeOnBoth s) = rawTick exchangeOnEither (receiverDual s) := by
  intro h
  let s : State := (0, (fun _ => ((false, false), false), fun _ => (false, true)))
  have hport := congrArg (fun t : State => (t.2.2 0).1) (h s)
  change true = false at hport
  cases hport

/-- The proposed relabeling is a reversible, on-site operation. -/
theorem receiver_dual_involutive : Function.Involutive receiverDual := by
  intro s
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext x
      change (complementRequests (complementRequests (s.2.1 x).1), (s.2.1 x).2) =
        s.2.1 x
      rcases s.2.1 x with ⟨⟨a, b⟩, side⟩
      cases a <;> cases b <;> rfl
    · funext x
      exact Prod.swap_swap _

theorem receiver_dual_local (s t : State) (x : ℤ)
    (hc : s.2.1 x = t.2.1 x) (hp : s.2.2 x = t.2.2 x) :
    (receiverDual s).2.1 x = (receiverDual t).2.1 x ∧
      (receiverDual s).2.2 x = (receiverDual t).2.2 x :=
  ⟨congrArg (fun p : Requests × Bool => (complementRequests p.1, p.2)) hc,
    congrArg Prod.swap hp⟩

/-- Commutation with the bare clock is weaker than commutation with a tick. -/
theorem receiver_dual_bare_clock (s : State) :
    receiverDual (finRotate Delta s.1, s.2) =
      (finRotate Delta (receiverDual s).1, (receiverDual s).2) := rfl

theorem receiver_dual_population (s : State) (x : ℤ) (pop : Bool → ℝ) :
    pop ((receiverDual s).2.2 x).1 + pop ((receiverDual s).2.2 x).2 =
      pop (s.2.2 x).1 + pop (s.2.2 x).2 := add_comm _ _

/-- At phase zero complementing the idle requests starts a real probe
    reflection, even if the two port values are equal. -/
theorem receiver_dual_probe_counterexample :
    ∃ s : State,
      ((receiverDual (rawTick exchangeOnBoth s)).2.1 0).2 = false ∧
        ((rawTick exchangeOnEither (receiverDual s)).2.1 0).2 = true := by
  exact ⟨(0, (fun _ => ((false, false), false), fun _ => (false, false))), rfl, rfl⟩

private theorem retained_request (rule : Rule) (s : State) (n : ℕ) (x : ℤ) :
    ((((rawTick rule)^[n]) s).2.1 x).1 = (s.2.1 x).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih

private theorem or_double_swap_ports (s : State)
    (h : ∀ x, (s.2.1 x).1 = (true, true)) :
    (rawTick exchangeOnEither (rawTick exchangeOnEither s)).2.2 = s.2.2 := by
  have step (u : State) (hu : ∀ x, (u.2.1 x).1 = (true, true)) (x : ℤ) :
      (rawTick exchangeOnEither u).2.2 x =
        ((u.2.2 (x + 1)).2, (u.2.2 (x - 1)).1) := by
    change applyGuard (exchangeOnEither u.1 (u.2.1 x).1)
      ((u.2.2 (x - 1)).1, (u.2.2 (x + 1)).2) = _
    rw [hu x]
    rfl
  funext x
  rw [step (rawTick exchangeOnEither s) (fun y => h y) x,
    step s h (x + 1), step s h (x - 1)]
  simp

private def probeClock (u : Phase × (Requests × Bool)) : Phase × (Requests × Bool) :=
  (finRotate Delta u.1, advanceProbe u.1 u.2)

private theorem probe_return :
    ∀ c : Requests, ∀ b : Bool, (probeClock^[2 * Delta]) (0, (c, b)) = (0, (c, b)) := by
  decide +kernel

private theorem probeClock_trace (rule : Rule) (s : State) (x : ℤ) (n : ℕ) :
    ((((rawTick rule)^[n]) s).1, (((rawTick rule)^[n]) s).2.1 x) =
      (probeClock^[n]) (s.1, s.2.1 x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

private theorem state_eq_of_observations {u s : State} (ports : u.2.2 = s.2.2)
    (probe : ∀ x, (u.1, u.2.1 x) = (s.1, s.2.1 x)) : u = s := by
  have hp : u.1 = s.1 := congrArg (fun p : Phase × (Requests × Bool) => p.1) (probe 0)
  have hr : u.2.1 = s.2.1 := funext fun x =>
    congrArg (fun p : Phase × (Requests × Bool) => p.2) (probe x)
  exact Prod.ext hp (Prod.ext hr ports)

private theorem or_returns_after_two_periods (s : State) (hp : s.1 = 0)
    (h : ∀ x, (s.2.1 x).1 = (true, true)) :
    (rawTick exchangeOnEither)^[2 * Delta] s = s := by
  have ports (n : ℕ) : (((rawTick exchangeOnEither)^[2 * n]) s).2.2 = s.2.2 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Nat.add_comm (2 * n) 2, Function.iterate_add_apply]
      exact (or_double_swap_ports _ (fun x =>
        (retained_request _ _ _ _).trans (h x))).trans ih
  let u := (rawTick exchangeOnEither)^[2 * Delta] s
  have probe (x : ℤ) : (u.1, u.2.1 x) = (s.1, s.2.1 x) := by
    calc
      _ = (probeClock^[2 * Delta]) (s.1, s.2.1 x) :=
        probeClock_trace exchangeOnEither s x (2 * Delta)
      _ = _ := by
        rw [hp]
        exact probe_return (s.2.1 x).1 (s.2.1 x).2
  exact state_eq_of_observations (u := u) (s := s) (ports Delta) probe

private theorem and_idle_live (s : State)
    (h : ∀ x, (s.2.1 x).1 = (false, false)) (n : ℕ) (x : ℤ) :
    ((((rawTick exchangeOnBoth)^[n]) s).2.2 x).1 =
      (s.2.2 (x - (n : ℤ))).1 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    let u := (rawTick exchangeOnBoth)^[n] s
    rw [Function.iterate_succ_apply']
    change (applyGuard (exchangeOnBoth u.1 (u.2.1 x).1)
      ((u.2.2 (x - 1)).1, (u.2.2 (x + 1)).2)).1 = _
    rw [(retained_request exchangeOnBoth s n x).trans (h x)]
    change (u.2.2 (x - 1)).1 = _
    rw [ih (x - 1), show (x - 1) - (n : ℤ) = x - ((n + 1 : ℕ) : ℤ) by omega]

/-- No injective clock-preserving relabeling that complements the requests
    everywhere can intertwine these updates. On the complemented pair
    the OR transport returns after two periods, while an AND input can
    carry its live value off the original site. -/
theorem no_request_complement_conjugacy (d : State → State) (hinj : Function.Injective d)
    (hp : ∀ s, (d s).1 = s.1)
    (hc : ∀ s x, ((d s).2.1 x).1 = complementRequests ((s.2.1 x).1)) :
    ¬ ∀ s, d (rawTick exchangeOnBoth s) = rawTick exchangeOnEither (d s) := by
  intro h
  let s : State := (0, (fun _ => ((false, false), false), fun x => (decide (x = 0), false)))
  have he (n : ℕ) : d ((rawTick exchangeOnBoth)^[n] s) =
      (rawTick exchangeOnEither)^[n] (d s) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]
  have hr := hinj ((he (2 * Delta)).trans
    (or_returns_after_two_periods (d s) (hp s) (fun x => hc s x)))
  have hx := and_idle_live s (fun _ => rfl) (2 * Delta) 0
  rw [hr] at hx
  change true = false at hx
  cases hx

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

/-- On the same arrivals the complemented guard moves the mismatch flag
    from one conditional exchange account to the other. -/
theorem complemented_exchange_flags (phase : Phase) (c : Requests)
    (p : Ports) (value : Bool → Fin 2 → ℂ) :
    exchangeFlag (exchangeOnBoth phase c) p value +
      exchangeFlag (exchangeOnEither phase (complementRequests c)) p value =
        CommonResponse.nsq (value p.1 - value p.2) / 2 := by
  unfold exchangeFlag
  rw [complemented_guard]
  cases exchangeOnBoth phase c p <;> simp

/-- A supplied pair of orthogonal basis values gives a unit flag on
    exchange and zero receiver flag on bypass. Even swapping the input
    pair with the requests does not preserve this registration. -/
theorem receiver_dual_flag_counterexample :
    let value : Bool → Fin 2 → ℂ :=
      fun b => Pi.single (if b then 1 else 0) 1
    exchangeFlag (exchangeOnBoth 0 (false, false)) (false, true) value = 0 ∧
      exchangeFlag (exchangeOnEither 0 (complementRequests (false, false)))
        ((false, true) : Ports).swap value = 1 := by
  norm_num [exchangeFlag, exchangeOnBoth, exchangeOnEither, complementRequests,
    LinkExpansion.nsq_eq, Fin.sum_univ_two, Pi.single_apply, Complex.normSq_apply]

/-- For a supplied weighted set of visits, sum the certified exchange
    output flags along a trace. The caller supplies the paid visits and
    their weights. The shift, root trial and other accounts are separate. -/
noncomputable def traceExchangeToll (rule : Rule) (s : State) (x : ℤ)
    (value : Bool → Fin 2 → ℂ) {N : ℕ} (weights : Fin N → ℝ) : ℝ :=
  TollAmplitude.weightedFlagCost 0 weights fun j =>
    let state := (rawTick rule)^[j.val] s
    exchangeFlag (rule state.1 (state.2.1 x).1)
      (OpenReferenceFlow.streamShift OpenReferenceFlow.line state.2.2 x) value

theorem uniform_trace_exchange_toll (rule : Rule) (s : State) (x : ℤ) (v : Bool)
    (hs : ∀ i, s.2.2 i = (v, v)) (value : Bool → Fin 2 → ℂ)
    {N : ℕ} (weights : Fin N → ℝ) :
    traceExchangeToll rule s x value weights = 0 := by
  unfold traceExchangeToll TollAmplitude.weightedFlagCost
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
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (baseline + traceExchangeToll j s x value weights) ≤
      PersistenceMechanics.EffectiveAction.attenuationWeight 1 (baseline + traceExchangeToll i s x value weights) := by
  let cost := fun rule => traceExchangeToll rule s x value weights
  have h := (PersistenceSelection.within_family_iff_cheapest (1 / 2) (by norm_num)
    cost F baseline i).mpr ⟨hi, fun j _ => by
      simp only [cost, uniform_trace_exchange_toll _ s x v hs value weights, le_refl]⟩
  intro j hj
  simpa [PersistenceMechanics.EffectiveAction.attenuationWeight, one_mul, cost, div_eq_mul_inv, mul_comm] using h.2 j hj

/-- On these inputs a strict preference requires a difference in the
    remaining paid work. The certified exchange flags cancel. -/
theorem uniform_remaining_cost_iff (a b : Rule) (s : State) (x : ℤ) (v : Bool)
    (hs : ∀ j, s.2.2 j = (v, v)) (value : Bool → Fin 2 → ℂ)
    {N : ℕ} (weights : Fin N → ℝ) (remaining : Rule → ℝ) :
    PersistenceMechanics.EffectiveAction.attenuationWeight 1 (traceExchangeToll b s x value weights + remaining b) <
        PersistenceMechanics.EffectiveAction.attenuationWeight 1 (traceExchangeToll a s x value weights + remaining a) ↔
      remaining a < remaining b := by
  rw [TollAmplitude.wireAmplitude_lt_iff,
    uniform_trace_exchange_toll a s x v hs value weights,
    uniform_trace_exchange_toll b s x v hs value weights]
  simp

end PMKAutomaton.LocalController
