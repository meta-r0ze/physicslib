import PMKAutomaton.AutonomousRing
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Native cycle averages, without an electron selection

The corrected test uses full native cycles and reports 43*R/T, not R.
Closed cycles still have even R. The period T need not divide 43: the
integer common return window lcm(T,43) contains both clocks.

The reproducible exhaustive finite census is tools/autonomous_ring_census.py.
It covers all positions, directions and marker words for odd n=3..13.
Its numerical cycle-cover tables are computation, not kernel-certified
classification theorems. The native all-n results below are separate.

Support is reported both as the visited sites and as the union of all
nonvacuum sites over the cycle (including spectator markers). A finite
ring alone does not certify localization on an infinite substrate. No
proper-support threshold is silently imposed. The perturbation test flips
one marker at every cycle phase and compares exact rational average rates;
it does not assert return to the identical orbit or self-correction.

Kinds 1,2,3 have respectively zero, half, half the tick count in reversals
on EVERY closed cycle. The half-rate identity telescopes the local marker
population; it is not a numerical fit. Kind 4 reverses every tick, and its
full state returns in four ticks. Its marker-robustness does not supply the
strict non-saturation Margin used by the old differing-ring account.

Kind 0 is the unchanged-marker receiver with a supplied initial reflector
layout. The finite census records its arbitrary-distance trapping family;
no persistence rule selects the distance. Static initial data are part of
an autonomous state, not a time-dependent external instruction.
-/
noncomputable section
namespace PMKAutomaton.AutonomousRing

/-- The exact common-window rate, in reversals per Delta root updates. -/
def average (r t : ℕ) : ℚ := (PMSubstrate.E8Values.Delta : ℚ)*r/t

def turns (k : Fin 5) (m : Bool) : Bool :=
  if k = 0 then m else if k = 1 then false else if k = 2 then m else if k = 3 then !m else true

theorem single_table : ∀ k b d m, explicitRule k b (single d m) =
    single (xor d (turns k m)) (if k = 0 then m else !m) := by decide +kernel

theorem packet_formula {n : ℕ} (k : Fin 5) (b : Bool) (s : OnePacket n) :
    packetStep (explicitRule k b) s =
      ((move s.1.1 (xor s.1.2 (turns k (s.2 s.1.1))),xor s.1.2 (turns k (s.2 s.1.1))),
       fun x => if x = s.1.1 then (if k = 0 then s.2 s.1.1 else !s.2 s.1.1) else s.2 x) := by
  unfold packetStep
  rw [single_table]
  rfl

/-- Native one-tick reversal, read from the actual stream slot. -/
def turnCount {n : ℕ} (f : Rule) (s : OnePacket n) : ℕ :=
  if (packetStep f s).1.2 ≠ s.1.2 then 1 else 0

theorem turn_table {n : ℕ} (k : Fin 5) (b : Bool) (s : OnePacket n) :
    turnCount (explicitRule k b) s = if turns k (s.2 s.1.1) then 1 else 0 := by
  rw [turnCount,packet_formula]
  cases s.1.2 <;> cases turns k (s.2 s.1.1) <;> simp

def markerTotal {n : ℕ} (m : Fin n → Bool) : ℤ := ∑ x, if m x then 1 else 0

theorem marker_update {n : ℕ} (m : Fin n → Bool) (x : Fin n) (v : Bool) :
    markerTotal (fun y => if y = x then v else m y) =
      markerTotal m + (if v then 1 else 0) - (if m x then 1 else 0) := by
  have hlocal (y : Fin n) : (if (if y = x then v else m y) then 1 else 0 : ℤ) =
      (if m y then 1 else 0) +
        (if y = x then (if v then 1 else 0)-(if m x then 1 else 0) else 0) := by
    by_cases h : y = x
    · subst y; cases v <;> cases m x <;> simp
    · simp [h]
  simp only [markerTotal,hlocal,Finset.sum_add_distrib]
  simp
  ring

/-- Generic discrete balance: no probabilistic or code-dependent cost enters. -/
theorem reversal_balance {S : Type*} (f : S → S) (d : S → Bool) (v : S → ℤ)
    (h : ∀ s, v (f s)+2*(if d (f s) ≠ d s then 1 else 0) = v s+1) (s : S) (t : ℕ) :
    v (f^[t] s)+2*(reversals f d s t : ℤ) = v s+t := by
  induction t with
  | zero => simp [reversals]
  | succ t ih =>
    have hs := h (f^[t] s)
    rw [reversals]
    push_cast
    rw [Function.iterate_succ_apply']
    split <;> split at hs <;> simp_all <;> omega

theorem marker_balance_two {n : ℕ} (b : Bool) (s : OnePacket n) :
    markerTotal (packetStep (explicitRule 2 b) s).2 +
      2*(turnCount (explicitRule 2 b) s : ℤ) = markerTotal s.2+1 := by
  rw [turn_table,packet_formula,marker_update]
  cases hm : s.2 s.1.1 <;> simp [turns,hm] <;> ring

theorem marker_balance_three {n : ℕ} (b : Bool) (s : OnePacket n) :
    -markerTotal (packetStep (explicitRule 3 b) s).2 +
      2*(turnCount (explicitRule 3 b) s : ℤ) = -markerTotal s.2+1 := by
  rw [turn_table,packet_formula,marker_update]
  cases hm : s.2 s.1.1 <;> simp [turns,hm] <;> ring

theorem closed_half_rate_two {n : ℕ} (b : Bool) (s : OnePacket n) (t : ℕ)
    (hc : (packetStep (explicitRule 2 b))^[t] s = s) :
    2*nativeReversals (explicitRule 2 b) s t = t := by
  have h := reversal_balance (packetStep (explicitRule 2 b)) (fun s => s.1.2)
    (fun s => markerTotal s.2) (by intro u; simpa [turnCount] using marker_balance_two b u) s t
  rw [hc] at h
  change _ + 2*(nativeReversals _ _ _ : ℤ) = _ at h
  omega

theorem closed_half_rate_three {n : ℕ} (b : Bool) (s : OnePacket n) (t : ℕ)
    (hc : (packetStep (explicitRule 3 b))^[t] s = s) :
    2*nativeReversals (explicitRule 3 b) s t = t := by
  have h := reversal_balance (packetStep (explicitRule 3 b)) (fun s => s.1.2)
    (fun s => -markerTotal s.2) (by intro u; simpa [turnCount] using marker_balance_three b u) s t
  rw [hc] at h
  change _ + 2*(nativeReversals _ _ _ : ℤ) = _ at h
  omega

/-- Per-tick certificates for both marker-independent scattering behaviours. -/
theorem passive_turn {n : ℕ} (b : Bool) (s : OnePacket n) :
    turnCount (explicitRule 1 b) s = 0 := by rw [turn_table]; simp [turns]

theorem saturated_turn {n : ℕ} (b : Bool) (s : OnePacket n) :
    turnCount (explicitRule 4 b) s = 1 := by rw [turn_table]; simp [turns]

theorem fixed_turn_count {n : ℕ} (f : Rule) (c : ℕ) (h : ∀ s : OnePacket n, turnCount f s = c)
    (s : OnePacket n) (t : ℕ) : nativeReversals f s t = t*c := by
  induction t with
  | zero => simp [nativeReversals,reversals]
  | succ t ih =>
    change reversals (packetStep f) (fun a => a.1.2) s (t+1) = _
    rw [reversals,Function.iterate_succ_apply']
    change nativeReversals f s t + turnCount f ((packetStep f)^[t] s) = _
    rw [ih,h]
    ring

theorem passive_reversals {n : ℕ} (b : Bool) (s : OnePacket n) (t : ℕ) :
    nativeReversals (explicitRule 1 b) s t = 0 := by
  simpa using fixed_turn_count _ 0 (passive_turn b) s t

theorem saturated_reversals {n : ℕ} (b : Bool) (s : OnePacket n) (t : ℕ) :
    nativeReversals (explicitRule 4 b) s t = t := by
  simpa using fixed_turn_count _ 1 (saturated_turn b) s t

/-- Every one-packet marker state recurs on a finite ring; no attractor is inferred. -/
theorem packet_injective {n : ℕ} (f : Rule) (h : Admissible f) : Function.Injective (packetStep (n := n) f) := by
  intro s t he
  apply embed_injective
  apply (tick n f).injective
  rw [packetStep_realizes_tick f h,packetStep_realizes_tick f h,he]

theorem packet_periodic {n : ℕ} (f : Rule) (h : Admissible f) (s : OnePacket n) :
    ∃ t > 0, (packetStep f)^[t] s = s :=
  Function.mem_periodicPts.mp ((packet_injective f h).mem_periodicPts s)

/-- Lifted displacement, not displacement modulo n (which vanishes on every closed ring cycle). -/
def displacement {n : ℕ} (f : Rule) (s : OnePacket n) (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range t, if (packetStep f ((packetStep f)^[j] s)).1.2 then -1 else 1

theorem saturated_four_return {n : ℕ} (b : Bool) (s : OnePacket n) :
    (packetStep (explicitRule 4 b))^[4] s = s := by
  rcases s with ⟨⟨x,d⟩,m⟩
  by_cases hf0 : finRotate n x = x
  · have hb0 : (finRotate n).symm x = x := (Equiv.symm_apply_eq (finRotate n)).mpr hf0.symm
    cases d <;> simp [Function.iterate_succ_apply',packet_formula,move,turns,hf0,hb0,
      -finRotate_apply,-finRotate_symm_apply]
    all_goals
      funext y
      by_cases hy : y = x <;> simp [hy]
  · have hb0 : (finRotate n).symm x ≠ x := by
      intro h
      exact hf0 ((Equiv.symm_apply_eq (finRotate n)).mp h).symm
    cases d <;> apply Prod.ext
    all_goals
      try { simp [Function.iterate_succ_apply',packet_formula,move,turns,hf0,hb0,
        -finRotate_apply,-finRotate_symm_apply] }
    all_goals
      funext y
      by_cases h : y = x <;>
        by_cases hf : y = finRotate n x <;>
          by_cases hb : y = (finRotate n).symm x <;>
            simp [h,hf,hb,hf0,hb0,Ne.symm hf0,Ne.symm hb0,
              Function.iterate_succ_apply',packet_formula,move,turns,
              -finRotate_apply,-finRotate_symm_apply]
    all_goals split_ifs <;> aesop

theorem saturated_four_displacement {n : ℕ} (b : Bool) (s : OnePacket n) :
    displacement (explicitRule 4 b) s 4 = 0 := by
  cases hd : s.1.2 <;>
    simp [displacement,Finset.sum_range_succ,packet_formula,turns,hd,
      Function.iterate_succ_apply',move,-finRotate_apply,-finRotate_symm_apply]

/-- Frozen markers retain their supplied layout exactly. -/
def staticStep {n : ℕ} (s : OnePacket n) : OnePacket n :=
  ((move s.1.1 (xor s.1.2 (s.2 s.1.1)),xor s.1.2 (s.2 s.1.1)),s.2)

theorem static_packet_step {n : ℕ} (b : Bool) :
    packetStep (n := n) (explicitRule 0 b) = staticStep := by
  funext s
  rw [packet_formula]
  apply Prod.ext
  · rfl
  · funext x
    by_cases hx : x = s.1.1 <;> simp [staticStep,hx]

/-- Recurrence with a specified native average, not restoration to the same perturbed orbit. -/
def RecursWithAverage {n : ℕ} (f : Rule) (s : OnePacket n) (q : ℚ) : Prop :=
  ∃ t > 0, (packetStep f)^[t] s = s ∧ average (nativeReversals f s t) t = q

theorem average_half (r t : ℕ) (ht : 0 < t) (h : 2*r = t) : average r t = 43/2 := by
  have hq : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have he : (2 : ℚ)*r = t := by exact_mod_cast h
  change (43 : ℚ)*r/t = 43/2
  rw [div_eq_iff hq]
  linarith

theorem recurrent_passive {n : ℕ} (b : Bool) (s : OnePacket n) :
    RecursWithAverage (explicitRule 1 b) s 0 := by
  obtain ⟨t,ht,hc⟩ := packet_periodic _ (explicit_admissible 1 b) s
  refine ⟨t,ht,hc,?_⟩
  simp [average,passive_reversals]

theorem recurrent_half_two {n : ℕ} (b : Bool) (s : OnePacket n) :
    RecursWithAverage (explicitRule 2 b) s (43/2) := by
  obtain ⟨t,ht,hc⟩ := packet_periodic _ (explicit_admissible 2 b) s
  exact ⟨t,ht,hc,average_half _ _ ht (closed_half_rate_two b s t hc)⟩

theorem recurrent_half_three {n : ℕ} (b : Bool) (s : OnePacket n) :
    RecursWithAverage (explicitRule 3 b) s (43/2) := by
  obtain ⟨t,ht,hc⟩ := packet_periodic _ (explicit_admissible 3 b) s
  exact ⟨t,ht,hc,average_half _ _ ht (closed_half_rate_three b s t hc)⟩

theorem recurrent_saturated {n : ℕ} (b : Bool) (s : OnePacket n) :
    RecursWithAverage (explicitRule 4 b) s 43 := by
  refine ⟨4,by norm_num,saturated_four_return b s,?_⟩
  rw [saturated_reversals]
  norm_num [average,PMSubstrate.E8Values.Delta,PMSubstrate.E8Values.Delta_eq]

def perturbMarker {n : ℕ} (s : OnePacket n) (x : Fin n) : OnePacket n :=
  (s.1,fun y => if y = x then !s.2 y else s.2 y)

/-- All-state rate theorems apply at every phase and after every one-marker perturbation. -/
theorem rate_robustness {n : ℕ} (f : Rule) (q : ℚ)
    (h : ∀ s : OnePacket n, RecursWithAverage f s q) (s : OnePacket n) (t : ℕ) (x : Fin n) :
    RecursWithAverage f (perturbMarker ((packetStep f)^[t] s) x) q := h _

/-- Corrected at-rest cycle test; the average is over Delta updates, not over one return. -/
def RestingAtRate {n : ℕ} (f : Rule) (s : OnePacket n) (q : ℚ) : Prop :=
  ∃ t > 0, (packetStep f)^[t] s = s ∧ displacement f s t = 0 ∧
    average (nativeReversals f s t) t = q

def MarkerRateRobust {n : ℕ} (f : Rule) (s : OnePacket n) (q : ℚ) : Prop :=
  ∀ t x, RecursWithAverage f (perturbMarker ((packetStep f)^[t] s) x) q

theorem saturated_resting {n : ℕ} (b : Bool) (s : OnePacket n) :
    RestingAtRate (explicitRule 4 b) s 43 := by
  refine ⟨4,by norm_num,saturated_four_return b s,saturated_four_displacement b s,?_⟩
  rw [saturated_reversals]
  norm_num [average,PMSubstrate.E8Values.Delta,PMSubstrate.E8Values.Delta_eq]

theorem saturated_marker_robust {n : ℕ} (b : Bool) (s : OnePacket n) :
    MarkerRateRobust (explicitRule 4 b) s 43 :=
  rate_robustness _ _ (recurrent_saturated b) s

/-- Marker-free static input remains marker-free and keeps its native direction. -/
theorem cleared_trace {n : ℕ} (x : Fin n) (t : ℕ) :
    staticStep^[t] ((x,false),fun _ => false) = (((finRotate n)^[t] x,false),fun _ => false) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
    rfl

theorem cleared_reversals {n : ℕ} (b : Bool) (x : Fin n) (t : ℕ) :
    nativeReversals (explicitRule 0 b) ((x,false),fun _ => false) t = 0 := by
  unfold nativeReversals
  rw [static_packet_step,reversals_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [cleared_trace,cleared_trace]
  rfl

/-- Unlike a raw cycle count, the common-window average has a period-independent 1D bound. -/
theorem native_average_bound {n : ℕ} (f : Rule) (s : OnePacket n) (t : ℕ) (ht : 0 < t) :
    average (nativeReversals f s t) t ≤ 43 := by
  have hr := reversals_le_ticks (packetStep f) (fun a => a.1.2) s t
  have hq : (0 : ℚ) < t := by exact_mod_cast ht
  have he : (nativeReversals f s t : ℚ) ≤ t := by exact_mod_cast hr
  change (43 : ℚ)*(nativeReversals f s t : ℚ)/t ≤ 43
  apply (div_le_iff₀ hq).mpr
  linarith

/-- AND and OR both give the static-marker collision when their scalar guard is retained. -/
theorem and_or_marker_embeddings : ∀ m : Bool,
    RingReceiver.exchange true (m,false) = m ∧ RingReceiver.exchange false (m,true) = m := by decide +kernel

theorem static_receiver_collision : ∀ either a b p,
    (explicitRule 0 false (p,RingReceiver.exchange either (a,b))).1 =
      LocalController.applyGuard (fun _ => RingReceiver.exchange either (a,b)) p := by decide +kernel

/-- In the fixed OR marker chart, AND always bypasses. Its identity collision
fails the frozen-marker clause at marker=1; this is a chart restriction, not a PM selection. -/
theorem and_in_or_chart : ∀ m p,
    LocalController.applyGuard (fun _ => RingReceiver.exchange false (m,false)) p = p := by
  decide +kernel

theorem fixed_or_chart_and_excluded : ¬ Admissible (Equiv.refl Site) := by decide +kernel

/-- Winding at n=43 is unnecessary to exclude mean one for the nonstatic kinds. -/
theorem nonstatic_no_unit_average {n : ℕ} (k : Fin 5) (hk : k ≠ 0) (b : Bool) (s : OnePacket n) :
    ¬ RecursWithAverage (explicitRule k b) s 1 := by
  rintro ⟨t,ht,hc,ha⟩
  fin_cases k
  · exact hk rfl
  · change average (nativeReversals (explicitRule 1 b) s t) t = 1 at ha
    rw [passive_reversals] at ha
    norm_num [average] at ha
  · change average (nativeReversals (explicitRule 2 b) s t) t = 1 at ha
    have he := average_half _ _ ht (closed_half_rate_two b s t hc)
    rw [ha] at he
    norm_num at he
  · change average (nativeReversals (explicitRule 3 b) s t) t = 1 at ha
    have he := average_half _ _ ht (closed_half_rate_three b s t hc)
    rw [ha] at he
    norm_num at he
  · change average (nativeReversals (explicitRule 4 b) s t) t = 1 at ha
    rw [saturated_reversals] at ha
    have hq : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
    norm_num [average,PMSubstrate.E8Values.Delta,PMSubstrate.E8Values.Delta_eq,hq] at ha

end PMKAutomaton.AutonomousRing
