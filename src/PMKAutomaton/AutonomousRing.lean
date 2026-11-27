import PMKAutomaton.RingReceiver
import PMKAutomaton.ClockSites
import PMKAutomaton.ClockSymmetryGenerators
import Mathlib.Data.Fintype.Perm

/-!
# Autonomous Boolean receiver rules and closed-cycle reversal parity

The site alphabet is the existing two Boolean stream slots and one local
marker. A specified site permutation is applied at every site, then the
existing stream shift moves its output. Markers are part of the state, not
an externally supplied request trace. Autonomy does not exclude initial data:
the old receiver is already autonomous with its retained requests as state.
Dynamical markers enlarge the tested successor space; no PM result here
requires that every autonomous marker must change. This is a restricted Boolean rule
space requested for this test, not a derivation of the full E8 successor.

The constraints use Conservation (site permutation and packet population),
the empty zero-marker vacuum, stream-exchange symmetry, and the existing
receiver guard for unchanged markers. The marker embeds as the OR request
(marker,false). RingReceiver shifts BEFORE scattering. Our incoming-port
chart scatters BEFORE shifting. The exact reduction is a conjugacy by the
stream shift on the port/marker subsystem, not equality of the full tick:
the full tick also has a 43-state phase and an independent probe.

The ring reflection below is the cyclic quotient of central lattice
negation, ClockSymmetry.reversingElement in Gpm, with streams exchanged.
It is a kinematic reflection commuting with evolution. This does not assert
that it conjugates the update to its inverse (dynamical time reversal).

A full periodic one-packet state returns its stream direction. Its number
of reversals is therefore even, for ANY update and ANY ring size. This
already excludes the requested one-reversal electron cycle, regardless of
localization and marker robustness. RingRates.one_site_exact counts an
observation window, not a full-state period. No Hamming-code price is used.
-/

noncomputable section
namespace PMKAutomaton.AutonomousRing

abbrev Site := (Bool × Bool) × Bool
abbrev Rule := Equiv.Perm Site

def population (s : Site) : ℕ := (if s.1.1 then 1 else 0)+(if s.1.2 then 1 else 0)
def vacuum : Site := ((false,false),false)
def exchangeStreams (s : Site) : Site := ((s.1.2,s.1.1),s.2)

def frozenReceiver (s : Site) : Bool × Bool :=
  LocalController.applyGuard (fun _ => RingReceiver.exchange true (s.2,false)) s.1

/-- These clauses constrain a site permutation; they are not an extra selection law. -/
def Admissible (f : Rule) : Prop :=
  (∀ s, population (f s) = population s) ∧ f vacuum = vacuum ∧
  (∀ s, f (exchangeStreams s) = exchangeStreams (f s)) ∧
  (∀ s, (f s).2 = s.2 → (f s).1 = frozenReceiver s)

instance (f : Rule) : Decidable (Admissible f) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def admissibleRules : Finset Rule := (permsOfFinset (Finset.univ : Finset Site)).filter Admissible

/-- Every permutation satisfying the stated clauses is in the enumeration. -/
theorem enumeration_complete (f : Rule) : f ∈ admissibleRules ↔ Admissible f := by
  simp [admissibleRules, mem_perms_of_finset_iff]

/-! ## Direction parity, independent of the rule-space restrictions -/

/-- Native direction changes in a finite observation window. -/
def reversals {S : Type*} (step : S → S) (direction : S → Bool) (s : S) : ℕ → ℕ
  | 0 => 0
  | t+1 => reversals step direction s t +
      if direction (step^[t+1] s) ≠ direction (step^[t] s) then 1 else 0

theorem reversals_eq_sum {S : Type*} (step : S → S) (direction : S → Bool) (s : S) (t : ℕ) :
    reversals step direction s t = ∑ j ∈ Finset.range t,
      if direction (step^[j+1] s) ≠ direction (step^[j] s) then 1 else 0 := by
  induction t with
  | zero => simp [reversals]
  | succ t ih => rw [reversals,Finset.sum_range_succ,ih]

theorem reversals_le_ticks {S : Type*} (step : S → S) (direction : S → Bool) (s : S) (t : ℕ) :
    reversals step direction s t ≤ t := by
  induction t with
  | zero => simp [reversals]
  | succ t ih =>
    rw [reversals]
    split <;> omega

theorem reversal_parity {S : Type*} (step : S → S) (direction : S → Bool) (s : S) (t : ℕ) :
    reversals step direction s t % 2 = if direction (step^[t] s) = direction s then 0 else 1 := by
  induction t with
  | zero => simp [reversals]
  | succ t ih =>
    rw [reversals, Nat.add_mod, ih]
    cases h0 : direction s <;> cases ht : direction (step^[t] s) <;>
      cases hn : direction (step^[t+1] s) <;> simp_all

theorem closed_cycle_even {S : Type*} (step : S → S) (direction : S → Bool) (s : S) (t : ℕ)
    (h : step^[t] s = s) : reversals step direction s t % 2 = 0 := by
  rw [reversal_parity,h]
  simp

theorem no_one_reversal_cycle {S : Type*} (step : S → S) (direction : S → Bool) (s : S) (t : ℕ)
    (h : step^[t] s = s) : reversals step direction s t ≠ 1 := by
  have hp := closed_cycle_even step direction s t h
  omega


/-! ## Explicit rule table -/

def ruleFunction (kind : Fin 5) (doubleFlip : Bool) (s : Site) : Site :=
  if s.1.1 = s.1.2 then
    (s.1, if s.1.1 then xor s.2 doubleFlip else s.2)
  else
    let turn := if kind = 0 then s.2 else if kind = 1 then false else
      if kind = 2 then s.2 else if kind = 3 then !s.2 else true
    ((if turn then (s.1.2,s.1.1) else s.1), if kind = 0 then s.2 else !s.2)

theorem ruleFunction_bijective : ∀ k b, Function.Bijective (ruleFunction k b) := by decide +kernel

def explicitRule (k : Fin 5) (b : Bool) : Rule := Equiv.ofBijective _ (ruleFunction_bijective k b)

theorem explicit_admissible : ∀ k b, Admissible (explicitRule k b) := by decide +kernel

def explicitRules : Finset Rule := Finset.univ.image fun kb : Fin 5 × Bool => explicitRule kb.1 kb.2

theorem explicit_rules_card : explicitRules.card = 10 := by decide +kernel

/-! ## Reversible spatial update, with local dynamical markers -/

abbrev State (n : ℕ) := Fin n → Site

def stream (n : ℕ) : Equiv.Perm (State n) where
  toFun s x := (((s ((finRotate n).symm x)).1.1,(s (finRotate n x)).1.2),(s x).2)
  invFun s x := (((s (finRotate n x)).1.1,(s ((finRotate n).symm x)).1.2),(s x).2)
  left_inv s := by funext x; simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Prod.eta]
  right_inv s := by funext x; simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply,Prod.eta]

def scatter (n : ℕ) (f : Rule) : Equiv.Perm (State n) := Equiv.piCongrRight fun _ => f

def tick (n : ℕ) (f : Rule) : Equiv.Perm (State n) := (scatter n f).trans (stream n)

theorem tick_bijective (n : ℕ) (f : Rule) : Function.Bijective (tick n f) := (tick n f).bijective

theorem stream_ports (n : ℕ) (s : State n) :
    (fun x => (stream n s x).1) = RingReceiver.arrivals (fun x => (s x).1) := rfl

def packetNumber (n : ℕ) (s : State n) : ℕ := ∑ x, population (s x)

theorem stream_conserves (n : ℕ) (s : State n) : packetNumber n (stream n s) = packetNumber n s := by
  simp only [packetNumber,population,stream,Equiv.coe_fn_mk,Finset.sum_add_distrib]
  congr 1
  · exact Equiv.sum_comp (finRotate n).symm (fun x => if (s x).1.1 then (1 : ℕ) else 0)
  · exact Equiv.sum_comp (finRotate n) (fun x => if (s x).1.2 then (1 : ℕ) else 0)

theorem tick_conserves (n : ℕ) (f : Rule) (h : Admissible f) (s : State n) :
    packetNumber n (tick n f s) = packetNumber n s := by
  rw [show tick n f s = stream n (scatter n f s) from rfl, stream_conserves]
  exact Finset.sum_congr rfl (fun _ _ => h.1 _)

theorem vacuum_fixed (n : ℕ) (f : Rule) (h : Admissible f) :
    tick n f (fun _ => vacuum) = fun _ => vacuum := by
  have hs : scatter n f (fun _ => vacuum) = fun _ => vacuum := by
    funext x; exact h.2.1
  change stream n (scatter n f (fun _ => vacuum)) = _
  rw [hs]; rfl

/-- The shift/scatter order differs by a change between incoming/outgoing port charts. -/
def outputTick (n : ℕ) (f : Rule) : Equiv.Perm (State n) := (stream n).trans (scatter n f)

theorem incoming_output_conjugacy (n : ℕ) (f : Rule) (s : State n) :
    stream n (outputTick n f s) = tick n f (stream n s) := rfl

/-- Exact frozen-marker reduction on ports; the full RingReceiver tick also has phase/probe. -/
theorem frozen_receiver_reduction (n : ℕ) (f : Rule) (h : Admissible f) (s : State n)
    (hm : ∀ x, (f (stream n s x)).2 = (s x).2) :
    (fun x => (outputTick n f s x).1) = RingReceiver.portStep true
      (fun x => ((s x).2,false)) (fun x => (s x).1) := by
  funext x
  exact h.2.2.2 (stream n s x) (hm x)

/-! ## Reflection induced by the existing clock-line negation -/

/-- Negation of the unwrapped aligned root line, then reduction modulo the ring length. -/
theorem clock_line_reflection (a : ℤ) :
    ClockSymmetry.reversingWeyl.val (a • PMSubstrate.ClockPlane.cu) =
      (-a) • PMSubstrate.ClockPlane.cu := by
  rw [ClockSymmetry.reversing_neg,neg_smul]

/-- On the actual 43-state clock reading this is exactly cyclic negation. -/
theorem clock_site_reflection (z : ClockRing.V) :
    ClockSites.site (ClockSymmetry.reversingWeyl.val z) = -ClockSites.site z := by
  rw [ClockSymmetry.reversing_neg]
  change ClockRing.toFin (ClockRing.clockReading (-z)) = -ClockRing.toFin (ClockRing.clockReading z)
  rw [ClockRing.clockReading_neg]
  rfl

def reflect {n : ℕ} [NeZero n] (s : State n) : State n :=
  fun x => exchangeStreams (s (-x))

theorem reflect_involutive {n : ℕ} [NeZero n] : Function.Involutive (reflect (n := n)) := by
  intro s; funext x
  simp [reflect,exchangeStreams]

theorem reflect_stream {n : ℕ} [NeZero n] (s : State n) :
    reflect (stream n s) = stream n (reflect s) := by
  funext x
  simp [reflect,stream,exchangeStreams,finRotate_apply,finRotate_symm_apply,sub_eq_add_neg,
    neg_add_rev,add_comm]

theorem reflect_tick {n : ℕ} [NeZero n] (f : Rule) (h : Admissible f) (s : State n) :
    reflect (tick n f s) = tick n f (reflect s) := by
  have hs : reflect (scatter n f s) = scatter n f (reflect s) := by
    funext x
    exact (h.2.2.1 (s (-x))).symm
  change reflect (stream n (scatter n f s)) = stream n (scatter n f (reflect s))
  rw [reflect_stream,hs]

/-! ## One-packet native dynamics and the empty electron-selected rule set -/

def single (d m : Bool) : Site := (( !d,d),m)

theorem single_output (f : Rule) (h : Admissible f) (d m : Bool) :
    f (single d m) = single (f (single d m)).1.2 (f (single d m)).2 := by
  have hp := h.1 (single d m)
  cases he : f (single d m) with
  | mk p a =>
    rcases p with ⟨u,v⟩
    cases d <;> cases u <;> cases v <;> simp_all [population,single]

/-- Native located packet and local marker field, observed immediately before scattering. -/
abbrev OnePacket (n : ℕ) := (Fin n × Bool) × (Fin n → Bool)

def packetStep {n : ℕ} (f : Rule) (s : OnePacket n) : OnePacket n :=
  let out := f (single s.1.2 (s.2 s.1.1))
  ((if out.1.2 then (finRotate n).symm s.1.1 else finRotate n s.1.1, out.1.2),
    fun x => if x = s.1.1 then out.2 else s.2 x)


/-- Conservation and the fixed zero-marker vacuum leave empty marked sites fixed as well. -/
theorem empty_fixed (f : Rule) (h : Admissible f) (m : Bool) :
    f ((false,false),m) = ((false,false),m) := by
  cases m
  · exact h.2.1
  · have hp := h.1 ((false,false),true)
    cases he : f ((false,false),true) with
    | mk p a =>
      rcases p with ⟨u,v⟩
      cases u <;> cases v <;> cases a <;> simp_all [population]
      have hh : f ((false,false),true) = f vacuum := he.trans h.2.1.symm
      have hn := f.injective hh
      cases hn

def embed {n : ℕ} (s : OnePacket n) : State n := fun x =>
  ((decide (x = s.1.1) && !s.1.2,decide (x = s.1.1) && s.1.2),s.2 x)

def move {n : ℕ} (x : Fin n) (d : Bool) : Fin n :=
  if d then (finRotate n).symm x else finRotate n x

theorem scatter_embed {n : ℕ} (f : Rule) (h : Admissible f) (s : OnePacket n) :
    scatter n f (embed s) = embed
      ((s.1.1,(f (single s.1.2 (s.2 s.1.1))).1.2),
       fun x => if x = s.1.1 then (f (single s.1.2 (s.2 s.1.1))).2 else s.2 x) := by
  funext x
  by_cases hx : x = s.1.1
  · subst x
    simpa [scatter,embed,single] using single_output f h s.1.2 (s.2 s.1.1)
  · simpa [scatter,embed,hx] using empty_fixed f h (s.2 x)

theorem stream_embed {n : ℕ} (s : OnePacket n) :
    stream n (embed s) = embed ((move s.1.1 s.1.2,s.1.2),s.2) := by
  funext x
  have hf : decide ((finRotate n).symm x = s.1.1) = decide (x = finRotate n s.1.1) :=
    decide_eq_decide.mpr (Equiv.symm_apply_eq (finRotate n))
  have hb : decide (finRotate n x = s.1.1) = decide (x = (finRotate n).symm s.1.1) :=
    decide_eq_decide.mpr (Equiv.eq_symm_apply (finRotate n)).symm
  cases hd : s.1.2 <;>
    simp only [stream,embed,move,hd,Equiv.coe_fn_mk,Bool.false_eq_true,ite_false,ite_true,
      Bool.not_false,Bool.not_true,Bool.and_false,Bool.and_true,hf,hb]

/-- Exact lifting to the full stream/marker automaton for every ring size, including 43. -/
theorem packetStep_realizes_tick {n : ℕ} (f : Rule) (h : Admissible f) (s : OnePacket n) :
    tick n f (embed s) = embed (packetStep f s) := by
  change stream n (scatter n f (embed s)) = _
  rw [scatter_embed f h,stream_embed]
  rfl

/-- The tracked marker word has no hidden time-dependent instruction field. -/
theorem packetStep_uses_local_state {n : ℕ} (f : Rule) (s t : OnePacket n)
    (hp : s.1 = t.1) (hm : s.2 s.1.1 = t.2 t.1.1) :
    (packetStep f s).1 = (packetStep f t).1 := by
  simp only [packetStep]
  rw [hp] at hm
  rw [hp,hm]

/-- No new code: the observable is the native stream slot of the sole packet. -/
def nativeReversals {n : ℕ} (f : Rule) (s : OnePacket n) (t : ℕ) : ℕ :=
  reversals (packetStep f) (fun a => a.1.2) s t


theorem embed_injective {n : ℕ} : Function.Injective (embed (n := n)) := by
  rintro ⟨⟨x,d⟩,m⟩ ⟨⟨y,e⟩,r⟩ h
  have hxy : x = y := by
    by_contra hn
    have hp := congrArg (fun u : State n => (u x).1) h
    cases d <;> simp [embed,hn] at hp
  subst y
  have hd : d = e := by
    have hp := congrArg (fun u : State n => (u x).1.2) h
    simpa [embed] using hp
  subst e
  have hm : m = r := by
    funext i
    exact congrArg (fun u : State n => (u i).2) h
  subst r
  rfl

theorem packet_iterate_realizes {n : ℕ} (f : Rule) (h : Admissible f) (s : OnePacket n) (t : ℕ) :
    (tick n f)^[t] (embed s) = embed ((packetStep f)^[t] s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,packetStep_realizes_tick f h,Function.iterate_succ_apply']

/-- Full-state native return also excludes one reversal; tracking discards no stream/marker data. -/
theorem native_closed_cycle_not_one {n : ℕ} (f : Rule) (h : Admissible f) (s : OnePacket n) (t : ℕ)
    (hc : (tick n f)^[t] (embed s) = embed s) : nativeReversals f s t ≠ 1 := by
  have ht : (packetStep f)^[t] s = s :=
    embed_injective ((packet_iterate_realizes f h s t).symm.trans hc)
  exact no_one_reversal_cycle (packetStep f) (fun a => a.1.2) s t ht

/-- The ten rules have five single-packet behaviours; double-occupancy updates are invisible here. -/
theorem double_flip_unseen : ∀ k d m,
    explicitRule k false (single d m) = explicitRule k true (single d m) := by decide +kernel

/-- Necessary cycle clauses only. Localization, identity and robustness can only restrict this set. -/
def ElectronCycle (n : ℕ) (f : Rule) : Prop :=
  ∃ s : OnePacket n, ∃ t : ℕ, 0 < t ∧ (packetStep f)^[t] s = s ∧ nativeReversals f s t = 1

theorem no_electron_cycle (n : ℕ) (f : Rule) : ¬ ElectronCycle n f := by
  rintro ⟨s,t,_,hc,hr⟩
  exact no_one_reversal_cycle (packetStep f) (fun a => a.1.2) s t hc hr

/-- Uniform certificate, stronger than individual tests on 3,5,7,9. -/
theorem requested_ring_tests (f : Rule) :
    ¬ ElectronCycle 3 f ∧ ¬ ElectronCycle 5 f ∧ ¬ ElectronCycle 7 f ∧ ¬ ElectronCycle 9 f :=
  ⟨no_electron_cycle _ _,no_electron_cycle _ _,no_electron_cycle _ _,no_electron_cycle _ _⟩

/-- The electron-selected census domain is empty, including every odd ring through 13 and 43. -/
theorem census_domain_empty : {f : Rule | Admissible f ∧ ElectronCycle 3 f} = ∅ := by
  ext f; simp [no_electron_cycle]

end PMKAutomaton.AutonomousRing
