import PMKAutomaton.AutonomousCensus
import Mathlib.Data.Fintype.Option

/-!
# What the Boolean double-occupancy variants do, and what they do not encode

The two variants change only the marker when both streams are occupied.
Their outgoing Boolean stream slots are both true. The one-packet reversal
observable has no supplied extension that identifies which occupied packet
went to which output. Two reversible labelled lifts have the same native
Boolean successor and different per-packet reversal counts. No native
per-packet collision mass can be inferred from the occupancy state alone.

For collision-only turning (single occupied inputs pass), conservation
forces the ENTIRE Boolean port action to be the identity. Its populations
are the free forward/backward streams, even if collisions write markers.
Labels routed at an overlap do not change that occupation flow. A finite
ring recurrence is not an at-rest localized bound state on its infinite
cover. Three unit-speed packets have nonzero odd total current.
-/
noncomputable section
namespace PMKAutomaton.CollisionBoundary
open PMKAutomaton.AutonomousRing

theorem double_ports : ∀ k b m,
    (explicitRule k b ((true,true),m)).1 = (true,true) := by decide +kernel

theorem double_variants_only_marker : ∀ k m,
    explicitRule k false ((true,true),m) = ((true,true),m) ∧
    explicitRule k true ((true,true),m) = ((true,true),!m) := by decide +kernel

abbrev Token := Bool
abbrev LabelledPorts := Option Token × Option Token
abbrev LabelledSite := LabelledPorts × Bool

def erase (s : LabelledSite) : Site := ((s.1.1.isSome,s.1.2.isSome),s.2)

/-- Both lifts conserve labels. Neither routing choice is selected by the Boolean rule. -/
def liftFunction (turn b : Bool) (s : LabelledSite) : LabelledSite :=
  if s.1.1.isSome && s.1.2.isSome then
    ((if turn then (s.1.2,s.1.1) else s.1),xor s.2 b)
  else if s.1.1.isSome || s.1.2.isSome then (s.1,!s.2) else s

theorem lifts_involutive : ∀ turn b, Function.Involutive (liftFunction turn b) := by
  unfold Function.Involutive
  decide +kernel

def lifted (turn b : Bool) : Equiv.Perm LabelledSite := (lifts_involutive turn b).toPerm _

theorem lifts_same_native_rule : ∀ turn b s,
    erase (lifted turn b s) = explicitRule 1 b (erase s) := by decide +kernel

def exampleAB : LabelledSite := ((some false,some true),false)

def side (p : LabelledPorts) (token : Token) : Bool := decide (p.2 = some token)

def namedTurns (input output : LabelledPorts) : ℕ :=
  ∑ token : Token, if side input token ≠ side output token then 1 else 0

theorem collision_lift_counts :
    namedTurns exampleAB.1 (lifted false false exampleAB).1 = 0 ∧
    namedTurns exampleAB.1 (lifted true false exampleAB).1 = 2 ∧
    erase (lifted false false exampleAB) = erase (lifted true false exampleAB) := by decide +kernel

/-- Thus the requested collision mass needs a labelled routing operation, not a guess of 0 or 2. -/
theorem no_native_collision_turn_readout :
    ¬ ∃ read : Site → Site → ℕ, ∀ turn,
      read (erase exampleAB) (erase (lifted turn false exampleAB)) =
        namedTurns exampleAB.1 (lifted turn false exampleAB).1 := by
  rintro ⟨read,h⟩
  have h0 := h false
  have h1 := h true
  rw [← collision_lift_counts.2.2] at h1
  rw [collision_lift_counts.1] at h0
  rw [collision_lift_counts.2.1] at h1
  omega

/-- Collision-only means no isolated packet is turned by a marker or phase fixture. -/
def SinglePass (f : Rule) : Prop := ∀ s, population s = 1 → (f s).1 = s.1

theorem single_pass_kinds : ∀ k b, SinglePass (explicitRule k b) ↔ k = 1 := by
  unfold SinglePass
  decide +kernel

theorem conserving_double (f : Rule) (h : Admissible f) (m : Bool) :
    (f ((true,true),m)).1 = (true,true) := by
  have hp := h.1 ((true,true),m)
  rcases he : f ((true,true),m) with ⟨⟨u,v⟩,a⟩
  cases u <;> cases v <;> simp_all [population]

theorem conserving_empty (f : Rule) (h : Admissible f) (m : Bool) :
    (f ((false,false),m)).1 = (false,false) := by
  have hp := h.1 ((false,false),m)
  rcases he : f ((false,false),m) with ⟨⟨u,v⟩,a⟩
  cases u <;> cases v <;> simp_all [population]

theorem collision_only_ports_identity (f : Rule) (h : Admissible f) (hs : SinglePass f) :
    ∀ s, (f s).1 = s.1 := by
  rintro ⟨⟨u,v⟩,m⟩
  cases u <;> cases v
  · exact conserving_empty f h m
  · exact hs _ rfl
  · exact hs _ rfl
  · exact conserving_double f h m

/-- This remains true phase by phase; writing collision markers does not bind the ports. -/
theorem collision_only_tick_ports (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f)
    (s : State n) : (fun x => (tick n f s x).1) = RingReceiver.arrivals (fun x => (s x).1) := by
  funext x
  change ((f (s ((finRotate n).symm x))).1.1,(f (s (finRotate n x))).1.2) = _
  rw [collision_only_ports_identity f h hs,collision_only_ports_identity f h hs]
  rfl

def forward (n : ℕ) (s : State n) : ℕ := ∑ x, if (s x).1.1 then 1 else 0
def backward (n : ℕ) (s : State n) : ℕ := ∑ x, if (s x).1.2 then 1 else 0
def current (n : ℕ) (s : State n) : ℤ := (forward n s : ℤ)-backward n s

theorem three_packet_current_nonzero (n : ℕ) (s : State n)
    (h : forward n s + backward n s = 3) : current n s ≠ 0 := by
  unfold current
  omega

theorem forward_conserved (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f) (s : State n) :
    forward n (tick n f s) = forward n s := by
  change (∑ x, if (f (s ((finRotate n).symm x))).1.1 then 1 else 0) = _
  simp_rw [collision_only_ports_identity f h hs]
  exact Equiv.sum_comp (finRotate n).symm (fun x => if (s x).1.1 then (1 : ℕ) else 0)

theorem backward_conserved (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f) (s : State n) :
    backward n (tick n f s) = backward n s := by
  change (∑ x, if (f (s (finRotate n x))).1.2 then 1 else 0) = _
  simp_rw [collision_only_ports_identity f h hs]
  exact Equiv.sum_comp (finRotate n) (fun x => if (s x).1.2 then (1 : ℕ) else 0)

theorem current_conserved (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f) (s : State n) :
    current n (tick n f s) = current n s := by
  simp only [current,forward_conserved n f h hs,backward_conserved n f h hs]

theorem current_iterate (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f) (s : State n) (t : ℕ) :
    current n ((tick n f)^[t] s) = current n s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',current_conserved n f h hs,ih]

def totalDisplacement (n : ℕ) (f : Rule) (s : State n) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range t, current n ((tick n f)^[j] s)

theorem collision_only_displacement (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f)
    (s : State n) (t : ℕ) : totalDisplacement n f s t = (t : ℤ)*current n s := by
  unfold totalDisplacement
  simp_rw [current_iterate n f h hs]
  simp

theorem three_packets_not_at_rest (n : ℕ) (f : Rule) (h : Admissible f) (hs : SinglePass f)
    (s : State n) (t : ℕ) (ht : 0 < t) (hn : forward n s + backward n s = 3) :
    totalDisplacement n f s t ≠ 0 := by
  rw [collision_only_displacement n f h hs]
  apply mul_ne_zero
  · exact_mod_cast (Nat.ne_of_gt ht)
  · exact three_packet_current_nonzero n s hn

/-- A free stream cannot remain in any fixed finite interval of the infinite line. -/
theorem forward_escapes (x upper : ℤ) : ∃ t : ℕ, upper < x+t := by
  have h : upper-x ≤ ((upper-x).natAbs : ℤ) := Int.le_natAbs
  exact ⟨(upper-x).natAbs+1,by omega⟩

theorem backward_escapes (x lower : ℤ) : ∃ t : ℕ, x-t < lower := by
  have h : x-lower ≤ ((x-lower).natAbs : ℤ) := Int.le_natAbs
  exact ⟨(x-lower).natAbs+1,by omega⟩

/-- Uniform local rule on the infinite cover, with the same scatter-then-stream stencil. -/
def lineTick (f : Rule) (s : ℤ → Site) : ℤ → Site := fun x =>
  (((f (s (x-1))).1.1,(f (s (x+1))).1.2),(f (s x)).2)

/-- A universal proof device, not an external-controller proposal: it includes every
native phase schedule whose isolated occupied ports pass at every phase. -/
def lineRun (r : ℕ → Rule) (s : ℤ → Site) : ℕ → (ℤ → Site)
  | 0 => s
  | t+1 => lineTick (r t) (lineRun r s t)

theorem line_forward_travels (r : ℕ → Rule) (h : ∀ t, Admissible (r t))
    (hp : ∀ t, SinglePass (r t)) (s : ℤ → Site) (x : ℤ) (t : ℕ) :
    (lineRun r s t (x+t)).1.1 = (s x).1.1 := by
  induction t with
  | zero => simp [lineRun]
  | succ t ih =>
    change (r t (lineRun r s t (x+(t+1)-1))).1.1 = _
    rw [collision_only_ports_identity _ (h t) (hp t)]
    have he : x+((t : ℤ)+1)-1 = x+(t : ℤ) := by omega
    rw [he]
    exact ih

theorem line_backward_travels (r : ℕ → Rule) (h : ∀ t, Admissible (r t))
    (hp : ∀ t, SinglePass (r t)) (s : ℤ → Site) (x : ℤ) (t : ℕ) :
    (lineRun r s t (x-t)).1.2 = (s x).1.2 := by
  induction t with
  | zero => simp [lineRun]
  | succ t ih =>
    change (r t (lineRun r s t (x-(t+1)+1))).1.2 = _
    rw [collision_only_ports_identity _ (h t) (hp t)]
    have he : x-((t : ℤ)+1)+1 = x-(t : ℤ) := by omega
    rw [he]
    exact ih

def Confined (r : ℕ → Rule) (s : ℤ → Site) (lo hi : ℤ) : Prop :=
  ∀ t x, (x < lo ∨ hi < x) → (lineRun r s t x).1 = (false,false)

/-- No nonempty collision-only pattern is a localized bound state, even with
phase-dependent collisions or labels that leave the same Boolean occupation law. -/
theorem no_confined_single_pass (r : ℕ → Rule) (h : ∀ t, Admissible (r t))
    (hp : ∀ t, SinglePass (r t)) (s : ℤ → Site)
    (occupied : ∃ x, (s x).1.1 = true ∨ (s x).1.2 = true) (lo hi : ℤ) : ¬ Confined r s lo hi := by
  intro hc
  obtain ⟨x,hx | hx⟩ := occupied
  · obtain ⟨t,ht⟩ := forward_escapes x hi
    have hf := line_forward_travels r h hp s x t
    have he := congrArg Prod.fst (hc t (x+t) (Or.inr ht))
    rw [hf,hx] at he
    cases he
  · obtain ⟨t,ht⟩ := backward_escapes x lo
    have hf := line_backward_travels r h hp s x t
    have he := congrArg Prod.snd (hc t (x-t) (Or.inl ht))
    rw [hf,hx] at he
    cases he

/-- Passing is required only at the encountered singleton input, not off the orbit. -/
theorem port_identity_at (f : Rule) (h : Admissible f) (z : Site)
    (hp : population z = 1 → (f z).1 = z.1) : (f z).1 = z.1 := by
  rcases z with ⟨⟨u,v⟩,m⟩
  cases u <;> cases v
  · exact conserving_empty f h m
  · exact hp rfl
  · exact hp rfl
  · exact conserving_double f h m

/-- The candidate orbit, rather than the whole rule, has no isolated turns. -/
def CollisionOnlyAlong (r : ℕ → Rule) (s : ℤ → Site) : Prop :=
  ∀ t x, population (lineRun r s t x) = 1 →
    (r t (lineRun r s t x)).1 = (lineRun r s t x).1

theorem along_forward_travels (r : ℕ → Rule) (h : ∀ t, Admissible (r t))
    (s : ℤ → Site) (hp : CollisionOnlyAlong r s) (x : ℤ) (t : ℕ) :
    (lineRun r s t (x+t)).1.1 = (s x).1.1 := by
  induction t with
  | zero => simp [lineRun]
  | succ t ih =>
    change (r t (lineRun r s t (x+(t+1)-1))).1.1 = _
    rw [port_identity_at _ (h t) _ (hp t _)]
    have he : x+((t : ℤ)+1)-1 = x+(t : ℤ) := by omega
    rw [he]
    exact ih

theorem along_backward_travels (r : ℕ → Rule) (h : ∀ t, Admissible (r t))
    (s : ℤ → Site) (hp : CollisionOnlyAlong r s) (x : ℤ) (t : ℕ) :
    (lineRun r s t (x-t)).1.2 = (s x).1.2 := by
  induction t with
  | zero => simp [lineRun]
  | succ t ih =>
    change (r t (lineRun r s t (x-(t+1)+1))).1.2 = _
    rw [port_identity_at _ (h t) _ (hp t _)]
    have he : x-((t : ℤ)+1)+1 = x-(t : ℤ) := by omega
    rw [he]
    exact ih

/-- Covers any candidate orbit whose only possible turns occur at collisions,
even if its rule would turn isolated packets at unvisited inputs. -/
theorem no_confined_collision_only (r : ℕ → Rule) (h : ∀ t, Admissible (r t))
    (s : ℤ → Site) (hp : CollisionOnlyAlong r s)
    (occupied : ∃ x, (s x).1.1 = true ∨ (s x).1.2 = true) (lo hi : ℤ) : ¬ Confined r s lo hi := by
  intro hc
  obtain ⟨x,hx | hx⟩ := occupied
  · obtain ⟨t,ht⟩ := forward_escapes x hi
    have hf := along_forward_travels r h s hp x t
    have he := congrArg Prod.fst (hc t (x+t) (Or.inr ht))
    rw [hf,hx] at he
    cases he
  · obtain ⟨t,ht⟩ := backward_escapes x lo
    have hf := along_backward_travels r h s hp x t
    have he := congrArg Prod.snd (hc t (x-t) (Or.inl ht))
    rw [hf,hx] at he
    cases he

end PMKAutomaton.CollisionBoundary
