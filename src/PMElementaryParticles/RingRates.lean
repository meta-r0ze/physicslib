import PMElementaryParticles.IsolatedReceiverTrace
import PMKAutomaton.ClockSites

set_option linter.unusedSimpArgs false

/-!
# One-site registration on the receiver ring

The packet starts on the live stream at `x0`. While it meets no exchanging site
it moves forward one site per tick (`quiet_walk`). At the firing site `s` it is
exchanged onto the record stream (`portStep_fire`) and registers once; the
record then moves backward one site per tick (`record_walk`) and returns to `s`
only after a full lap. So a single firing site registers exactly once in every
`n`-tick window starting at tick `0` (`one_site_exact`), for every ring size `n`.
On the clock ring `n = Δ = 43` this is `ring43_one` / `ring_Delta_one`.

The proof is structural; it replaces the earlier row-by-row kernel checks.
-/

noncomputable section

namespace PMElementaryParticles.RingRates

open PMElementaryParticles.IsolatedExcitation

/-! ## The live packet -/

section Walk

variable {n : ℕ}

/-- One port step is the stream shift followed by the on-site exchange. -/
theorem portStep_apply (either : Bool) (r : Fin n → IsolatedRequests)
    (P : PMKAutomaton.RingReceiver.PortField n) (x : Fin n) :
    PMKAutomaton.RingReceiver.portStep either r P x =
      PMKAutomaton.LocalController.applyGuard
        (fun _ => PMKAutomaton.RingReceiver.exchange either (r x))
        (PMKAutomaton.RingReceiver.arrivals P x) := rfl

theorem localized_live (y z : Fin n) :
    (localizedPortsN n y activePacket z).1 = decide (z = y) := by
  by_cases h : z = y <;> simp [localizedPortsN, h, active_activePacket]

theorem localized_record (y z : Fin n) :
    (localizedPortsN n y activePacket z).2 = false := by
  by_cases h : z = y <;> simp [localizedPortsN, h]

/-- A packet on the live stream at `y` arrives at `finRotate n y`. -/
theorem arrivals_localized (y x : Fin n) :
    PMKAutomaton.RingReceiver.arrivals (localizedPortsN n y activePacket) x =
      (decide (x = finRotate n y), false) := by
  change ((localizedPortsN n y activePacket ((finRotate n)⁻¹ x)).1,
      (localizedPortsN n y activePacket (finRotate n x)).2) = _
  rw [localized_live, localized_record]
  congr 1
  exact decide_eq_decide.mpr Equiv.Perm.inv_eq_iff_eq

/-- With no exchange at the arrival site, the packet moves one site. -/
theorem portStep_quiet (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n)
    (hq : PMKAutomaton.RingReceiver.exchange either (r (finRotate n y)) = false) :
    PMKAutomaton.RingReceiver.portStep either r (localizedPortsN n y activePacket) =
      localizedPortsN n (finRotate n y) activePacket := by
  funext x
  rw [portStep_apply, arrivals_localized]
  by_cases hx : x = finRotate n y
  · subst hx
    simp_all [PMKAutomaton.LocalController.applyGuard, localizedPortsN,
      active_activePacket]
  · simp_all [PMKAutomaton.LocalController.applyGuard, localizedPortsN]

/-- Until its first exchanging site, the packet walks the ring. -/
theorem quiet_walk (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (j : ℕ) (hq : ∀ i < j,
      PMKAutomaton.RingReceiver.exchange either (r ((finRotate n)^[i + 1] x0)) = false) :
    (PMKAutomaton.RingReceiver.portStep either r)^[j] (localizedPortsN n x0 activePacket) =
      localizedPortsN n ((finRotate n)^[j] x0) activePacket := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hj := hq j (Nat.lt_succ_self j)
    rw [Function.iterate_succ_apply' (⇑(finRotate n))] at hj
    rw [Function.iterate_succ_apply' (⇑(PMKAutomaton.RingReceiver.portStep either r)),
      ih (fun i hi => hq i (Nat.lt_succ_of_lt hi)),
      Function.iterate_succ_apply' (⇑(finRotate n))]
    exact portStep_quiet either r _ hj

theorem finRotate_iterate_val (k m : ℕ) (x : Fin (k + 1)) :
    ((finRotate (k + 1))^[m] x).val = (x.val + m) % (k + 1) := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ m ih =>
    rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, Nat.add_assoc]

/-- Every site is reached within one lap. -/
theorem reach (k : ℕ) (x0 s : Fin (k + 1)) :
    ∃ m < k + 1, (finRotate (k + 1))^[m + 1] x0 = s := by
  have hx := x0.isLt
  have hs := s.isLt
  by_cases h : x0.val < s.val
  · refine ⟨s.val - x0.val - 1, by omega, Fin.ext ?_⟩
    rw [finRotate_iterate_val,
      show x0.val + (s.val - x0.val - 1 + 1) = s.val by omega]
    exact Nat.mod_eq_of_lt hs
  · refine ⟨s.val + k - x0.val, by omega, Fin.ext ?_⟩
    rw [finRotate_iterate_val,
      show x0.val + (s.val + k - x0.val + 1) = s.val + (k + 1) by omega,
      Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hs

/-! ## The record packet -/

/-- A single record bit at `y`. -/
def recordPortsN (n : ℕ) (y : Fin n) : Fin n → IsolatedPorts :=
  fun x => if x = y then (false, true) else (false, false)

theorem record_live (y z : Fin n) : (recordPortsN n y z).1 = false := by
  unfold recordPortsN; split <;> rfl

theorem record_record (y z : Fin n) : (recordPortsN n y z).2 = decide (z = y) := by
  by_cases h : z = y <;> simp [recordPortsN, h]

/-- A record bit at `y` arrives at `(finRotate n).symm y`. -/
theorem arrivals_record (y x : Fin n) :
    PMKAutomaton.RingReceiver.arrivals (recordPortsN n y) x =
      (false, decide (x = (finRotate n).symm y)) := by
  change ((recordPortsN n y ((finRotate n)⁻¹ x)).1,
      (recordPortsN n y (finRotate n x)).2) = _
  rw [record_live, record_record]
  congr 1
  exact decide_eq_decide.mpr (by rw [Equiv.eq_symm_apply])

/-- At an exchanging site the live packet moves onto the record stream. -/
theorem portStep_fire (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n)
    (hf : PMKAutomaton.RingReceiver.exchange either (r (finRotate n y)) = true) :
    PMKAutomaton.RingReceiver.portStep either r (localizedPortsN n y activePacket) =
      recordPortsN n (finRotate n y) := by
  funext x
  rw [portStep_apply, arrivals_localized]
  by_cases hx : x = finRotate n y
  · subst hx
    simp_all [PMKAutomaton.LocalController.applyGuard, recordPortsN]
  · simp_all [PMKAutomaton.LocalController.applyGuard, recordPortsN]

/-- With no exchange at its arrival site, the record bit moves back one site. -/
theorem portStep_record_quiet (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n)
    (hq : PMKAutomaton.RingReceiver.exchange either (r ((finRotate n).symm y)) = false) :
    PMKAutomaton.RingReceiver.portStep either r (recordPortsN n y) =
      recordPortsN n ((finRotate n).symm y) := by
  funext x
  rw [portStep_apply, arrivals_record]
  by_cases hx : x = (finRotate n).symm y
  · subst hx
    simp_all [PMKAutomaton.LocalController.applyGuard, recordPortsN]
  · simp_all [PMKAutomaton.LocalController.applyGuard, recordPortsN]

/-- Until its next exchanging site, the record bit walks the ring backwards. -/
theorem record_walk (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n)
    (i : ℕ) (hq : ∀ l < i,
      PMKAutomaton.RingReceiver.exchange either
        (r ((⇑(finRotate n).symm)^[l + 1] y)) = false) :
    (PMKAutomaton.RingReceiver.portStep either r)^[i] (recordPortsN n y) =
      recordPortsN n ((⇑(finRotate n).symm)^[i] y) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi := hq i (Nat.lt_succ_self i)
    rw [Function.iterate_succ_apply' (⇑(finRotate n).symm)] at hi
    rw [Function.iterate_succ_apply' (⇑(PMKAutomaton.RingReceiver.portStep either r)),
      ih (fun l hl => hq l (Nat.lt_succ_of_lt hl)),
      Function.iterate_succ_apply' (⇑(finRotate n).symm)]
    exact portStep_record_quiet either r _ hi

/-! ## Registrations per tick -/

/-- Registrations in one tick from the port state `P`. -/
def tickCount (either : Bool) (r : Fin n → IsolatedRequests)
    (P : PMKAutomaton.RingReceiver.PortField n) : ℕ :=
  ∑ x, if PMKAutomaton.RingReceiver.exchange either (r x) = true ∧
      (PMKAutomaton.RingReceiver.arrivals P x).1 ≠
        (PMKAutomaton.RingReceiver.arrivals P x).2 then 1 else 0

theorem sum_flag_eq_tick (either : Bool) (r : Fin n → IsolatedRequests) (x0 : Fin n)
    (t : ℕ) :
    ∑ x, localizedFlagNatN n either r x0 t x =
      tickCount either r
        ((PMKAutomaton.RingReceiver.portStep either r)^[t]
          (localizedPortsN n x0 activePacket)) := rfl

theorem tick_localized (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n) :
    tickCount either r (localizedPortsN n y activePacket) =
      if PMKAutomaton.RingReceiver.exchange either (r (finRotate n y)) = true
      then 1 else 0 := by
  unfold tickCount
  rw [Finset.sum_eq_single (finRotate n y)]
  · rw [arrivals_localized]
    by_cases h : PMKAutomaton.RingReceiver.exchange either (r (finRotate n y)) = true <;>
      simp_all
  · intro b _ hb
    rw [arrivals_localized]
    simp_all
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tick_record (either : Bool) (r : Fin n → IsolatedRequests) (y : Fin n) :
    tickCount either r (recordPortsN n y) =
      if PMKAutomaton.RingReceiver.exchange either (r ((finRotate n).symm y)) = true
      then 1 else 0 := by
  unfold tickCount
  rw [Finset.sum_eq_single ((finRotate n).symm y)]
  · rw [arrivals_record]
    by_cases h : PMKAutomaton.RingReceiver.exchange either
        (r ((finRotate n).symm y)) = true <;>
      simp_all
  · intro b _ hb
    rw [arrivals_record]
    simp_all
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## No return before a full lap -/

theorem iterate_apply_symm_iterate {α : Type*} (e : Equiv.Perm α) (m : ℕ) (x : α) :
    (⇑e)^[m] ((⇑e.symm)^[m] x) = x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply (⇑e), Function.iterate_succ_apply' (⇑e.symm),
      Equiv.apply_symm_apply, ih]

theorem iterate_ne_self (k m : ℕ) (hm0 : 0 < m) (hm : m < k + 1) (s : Fin (k + 1)) :
    (finRotate (k + 1))^[m] s ≠ s := by
  intro h
  have hv := congrArg Fin.val h
  rw [finRotate_iterate_val] at hv
  have hs := s.isLt
  by_cases hlt : s.val + m < k + 1
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega

theorem symm_iterate_ne_self (k m : ℕ) (hm0 : 0 < m) (hm : m < k + 1) (s : Fin (k + 1)) :
    (⇑(finRotate (k + 1)).symm)^[m] s ≠ s := by
  intro h
  have h2 := iterate_apply_symm_iterate (finRotate (k + 1)) m s
  rw [h] at h2
  exact iterate_ne_self k m hm0 hm s h2

end Walk

/-! ## One firing site -/

/-- Requests with one firing site: `(true,true)` at `s`, idle elsewhere. -/
def oneFiringN (n : ℕ) (s : Fin n) : Fin n → IsolatedRequests :=
  fun x => if x = s then (true, true) else (false, false)

theorem exchange_oneFiring (either : Bool) {n : ℕ} (s x : Fin n) :
    PMKAutomaton.RingReceiver.exchange either (oneFiringN n s x) = decide (x = s) := by
  by_cases h : x = s <;> cases either <;>
    simp [oneFiringN, PMKAutomaton.RingReceiver.exchange, h]

/-- **One firing site registers exactly once per period**, for every ring size,
start site and firing site, under either guard. -/
theorem one_site_exact (either : Bool) {n : ℕ} (s x0 : Fin n) :
    localizedSumN n either (oneFiringN n s) x0 n = 1 := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := x0.isLt; omega⟩
  have hex := exchange_oneFiring either s
  obtain ⟨m, hm, hms⟩ := reach k x0 s
  have hex' : ∃ i, (finRotate (k + 1))^[i + 1] x0 = s := ⟨m, hms⟩
  obtain ⟨j, hj, hjmin⟩ : ∃ j, (finRotate (k + 1))^[j + 1] x0 = s ∧
      ∀ i < j, (finRotate (k + 1))^[i + 1] x0 ≠ s :=
    ⟨Nat.find hex', Nat.find_spec hex', fun i hi => Nat.find_min hex' hi⟩
  have hjn : j < k + 1 := by
    by_contra h
    exact hjmin m (by omega) hms
  have hq : ∀ i < j, PMKAutomaton.RingReceiver.exchange either
      (oneFiringN (k + 1) s ((finRotate (k + 1))^[i + 1] x0)) = false := by
    intro i hi
    rw [hex]
    exact decide_eq_false (hjmin i hi)
  have hs' : finRotate (k + 1) ((finRotate (k + 1))^[j] x0) = s := by
    rw [← Function.iterate_succ_apply' (⇑(finRotate (k + 1)))]
    exact hj
  have htick : ∀ t < k + 1,
      (∑ x, localizedFlagNatN (k + 1) either (oneFiringN (k + 1) s) x0 t x) =
        if t = j then 1 else 0 := by
    intro t ht
    rw [sum_flag_eq_tick]
    by_cases htj : t ≤ j
    · rw [quiet_walk either (oneFiringN (k + 1) s) x0 t (fun i hi => hq i (by omega)), tick_localized, hex,
        ← Function.iterate_succ_apply' (⇑(finRotate (k + 1)))]
      by_cases h' : t = j
      · subst h'
        rw [hj]
        simp
      · have hne : (finRotate (k + 1))^[t + 1] x0 ≠ s := hjmin t (by omega)
        rw [decide_eq_false hne]
        simp [h']
    · obtain ⟨i, rfl⟩ : ∃ i, t = i + (j + 1) := ⟨t - (j + 1), by omega⟩
      have hfire : PMKAutomaton.RingReceiver.exchange either
          (oneFiringN (k + 1) s (finRotate (k + 1) ((finRotate (k + 1))^[j] x0))) = true := by
        rw [hex, hs']
        exact decide_eq_true rfl
      rw [Function.iterate_add_apply,
        Function.iterate_succ_apply'
          (⇑(PMKAutomaton.RingReceiver.portStep either (oneFiringN (k + 1) s))),
        quiet_walk either (oneFiringN (k + 1) s) x0 j hq, portStep_fire either (oneFiringN (k + 1) s) _ hfire, hs',
        record_walk either (oneFiringN (k + 1) s) s i (fun l hl => by
          rw [hex]
          exact decide_eq_false (symm_iterate_ne_self k (l + 1) (by omega) (by omega) s)),
        tick_record, hex, ← Function.iterate_succ_apply' (⇑(finRotate (k + 1)).symm)]
      have hne : (⇑(finRotate (k + 1)).symm)^[i + 1] s ≠ s :=
        symm_iterate_ne_self k (i + 1) (by omega) (by omega) s
      rw [decide_eq_false hne]
      simp [show i + (j + 1) ≠ j by omega]
  unfold localizedSumN
  exact (Finset.sum_congr rfl (fun t ht => htick t (Finset.mem_range.1 ht))).trans
    (by simp [hjn])

/-- On the 43-ring one firing site registers exactly once per period. -/
theorem ring43_one (s x0 : Fin 43) :
    localizedSumN 43 true (oneFiringN 43 s) x0 43 = 1 :=
  one_site_exact true s x0

/-- The same result at the substrate period `Δ = 43`. -/
theorem ring_Delta_one (s x0 : Fin PMSubstrate.E8Values.Delta) :
    localizedSumN PMSubstrate.E8Values.Delta true
      (oneFiringN PMSubstrate.E8Values.Delta s) x0 43 = 1 := by
  simpa [PMSubstrate.E8Values.Delta_eq] using ring43_one s x0

end PMElementaryParticles.RingRates
