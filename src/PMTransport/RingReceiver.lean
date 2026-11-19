import PMTransport.LocalController
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Closed two-stream receiver

A periodic identification closes the encoded root line. It supplies a
finite state space with internal arrivals. The retained requests still
belong to that state. The test keeps every initial request and port field.
-/

namespace PMTransport.RingReceiver

open PMAction LocalController

abbrev RequestsField (n : ℕ) := Fin n → Requests
abbrev ProbeField (n : ℕ) := Fin n → Bool
abbrev PortField (n : ℕ) := OpenReferenceFlow.State (Fin n) Bool
abbrev Fields (n : ℕ) := RequestsField n × (ProbeField n × PortField n)
abbrev State (n : ℕ) := Phase × Fields n

/-- False selects AND and true selects OR. -/
def exchange (either : Bool) (c : Requests) : Bool :=
  if either then c.1 || c.2 else c.1 && c.2

def arrivals {n : ℕ} (ports : PortField n) :=
  OpenReferenceFlow.streamShift (finRotate n) ports

private def scatter {n : ℕ} (either : Bool) (requests : RequestsField n)
    (ports : PortField n) : PortField n :=
  fun x => applyGuard (fun _ => exchange either (requests x)) (ports x)

private theorem scatter_twice {n : ℕ} (either : Bool) (requests : RequestsField n) :
    Function.Involutive (scatter either requests) := by
  intro ports
  funext x
  rcases hp : ports x with ⟨live, record⟩
  cases hx : exchange either (requests x) <;> simp [scatter, applyGuard, hx, hp]

def portStep {n : ℕ} (either : Bool) (requests : RequestsField n) : Equiv.Perm (PortField n) :=
  (OpenReferenceFlow.shiftEquiv (finRotate n)).trans ((scatter_twice either requests).toPerm _)

private def probeStep {n : ℕ} (phase : Phase) (requests : RequestsField n)
    (side : ProbeField n) : ProbeField n :=
  fun x => (advanceProbe phase (requests x, side x)).2

private theorem probe_twice {n : ℕ} (phase : Phase) (requests : RequestsField n) :
    Function.Involutive (probeStep phase requests) := by
  intro side
  funext x
  cases h : ClockedRootTrials.fire (requests x) phase <;> simp [probeStep, advanceProbe, h]

/-- Undo the phase advance, then both on-site involutions, then the
    stream shift. The resulting tick is a bijection for either rule. -/
def tick (n : ℕ) (either : Bool) : Equiv.Perm (State n) :=
  (Equiv.prodCongrRight fun phase =>
    Equiv.prodCongrRight fun requests =>
      Equiv.prodCongr ((probe_twice phase requests).toPerm _) (portStep either requests)).trans
    (Equiv.prodCongr (finRotate Delta) (Equiv.refl _))

theorem tick_bijective (n : ℕ) (either : Bool) : Function.Bijective (tick n either) :=
  (tick n either).bijective

theorem tick_ports {n : ℕ} (either : Bool) (s : State n) (x : Fin n) :
    (tick n either s).2.2.2 x =
      applyGuard (fun _ => exchange either (s.2.1 x)) (arrivals s.2.2.2 x) := rfl

theorem receiver_realisation {n : ℕ} (either : Bool) (s : State n) (x : Fin n)
    (edge : TwoSiteHandoff.State Bool) (h : edge 1 = arrivals s.2.2.2 x) :
    (tick n either s).2.2.2 x = TwoSiteHandoff.step (exchange either (s.2.1 x)) edge 0 := by
  rw [tick_ports, (TwoSiteHandoff.step_trace _ edge).1, ← h]
  rfl

theorem probe_realisation {n : ℕ} (either : Bool) (s : State n) (x : Fin n)
    (z : SubstrateReflection.Lattice) :
    ClockedRootTrials.tick (s.2.1 x, (orbitPoint z (s.2.2.1 x), s.1)) =
      ((tick n either s).2.1 x, (orbitPoint z ((tick n either s).2.2.1 x), (tick n either s).1)) :=
  LocalController.probe_realises_trial s.1 (s.2.1 x, s.2.2.1 x) z

/-- Two sites identify the incoming neighbours. Three and four sites
    both retain the centre and its two distinct neighbours. -/
theorem ring_neighbourhood :
    (∀ x : Fin 2, finRotate 2 x = (finRotate 2).symm x) ∧
    (∀ x : Fin 3, finRotate 3 x ≠ x ∧ (finRotate 3).symm x ≠ x ∧
      finRotate 3 x ≠ (finRotate 3).symm x) ∧
    (∀ x : Fin 4, finRotate 4 x ≠ x ∧ (finRotate 4).symm x ≠ x ∧
      finRotate 4 x ≠ (finRotate 4).symm x) := by
  decide +kernel

end PMTransport.RingReceiver
