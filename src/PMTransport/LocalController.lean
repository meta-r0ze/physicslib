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

end PMTransport.LocalController
