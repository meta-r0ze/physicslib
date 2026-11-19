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

end PMTransport.LocalController
