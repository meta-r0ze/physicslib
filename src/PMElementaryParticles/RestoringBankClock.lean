import PMElementaryParticles.RestoringBankedShift
import PMKAutomaton.BankReceiverPulse

/-!
# Clock windows for a serial banked restoring candidate

The two receiver ticks come from the encoded trace. The extraction and
reload are staged receiver half-pulses of two root quarter-times each.
A separate serial class word uses eight root quarter-times. The slot
calculation assumes these windows are admitted and the incoming banks
are already staged. It leaves the timing of the spatial work open.
-/

namespace PMElementaryParticles.RestoringWallShift

open PMAction

/-- Earliest class-word completion after the two receiver ticks, followed
by the staged extraction and four serial half-pulses. -/
def bankedClassFinish (q : ℕ) : ℕ :=
  2 + 2 * q + (2 * classShiftWord.length) * q

/-- Latest reload start that completes at the next two-period boundary. -/
def bankedReloadStart (q : ℕ) : ℕ := 2 * Delta - 2 * q

theorem banked_class_finish_eq (q : ℕ) : bankedClassFinish q = 2 + 10 * q := by
  unfold bankedClassFinish
  rw [class_shift_quarter_times]
  omega

/-- An extraction starting at tick two, followed by the class word,
can share the serial block with a reload ending at tick 86 precisely
when the common quarter-time occupies at most seven ticks. -/
theorem banked_windows_iff (q : ℕ) :
    bankedClassFinish q ≤ bankedReloadStart q ↔ q ≤ 7 := by
  rw [banked_class_finish_eq]
  change 2 + 10 * q ≤ 86 - 2 * q ↔ q ≤ 7
  omega

theorem banked_reload_ends (q : ℕ) (hq : q ≤ 7) :
    bankedReloadStart q + 2 * q = 2 * Delta := by
  change 86 - 2 * q + 2 * q = 86
  omega

/-- When this serial booking fits, its spare ticks lie after the class
word and before the reload. No time for staging has been included. -/
theorem banked_window_slack (q : ℕ) (hq : q ≤ 7) :
    bankedReloadStart q - bankedClassFinish q = 84 - 12 * q := by
  rw [banked_class_finish_eq]
  change 86 - 2 * q - (2 + 10 * q) = 84 - 12 * q
  omega

/-- The scalar geometric handoff weight cannot also be the root trial
weight of this serial banked schedule. The trial and handoff readouts
need their own native identification. -/
theorem banked_windows_fail_at_geometric_trial (p : ℝ) (hp' : p < 1 / 2)
    (q : ℕ) (hq : 0 < q)
    (hclock : RootTransferPhase.quarterTime p = (q : ℝ) / 2)
    (hweight : PMKAutomaton.BankReceiverPulse.bankTrialWeight p = PMSubstrate.causalCoupling) :
    bankedReloadStart q < bankedClassFinish q := by
  have htooLong := PMKAutomaton.BankReceiverPulse.geometric_trial_exceeds_block p hp' q hq hclock hweight
  apply lt_of_not_ge
  intro hfit
  have h := (banked_windows_iff q).1 hfit
  omega

/-! ## Retaining the signed carrier's axis alongside the staged doublet -/

open PMKAutomaton Matrix GappedGluedCrossing

/-- A doublet carries the sign. Its retained axis distinguishes four
such doublets in the existing signed-carrier code. -/
def signedAxisEquiv : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv

theorem signedAxisEquiv_apply (axis : Fin 4) (sign : Fin 2) :
    signedAxisEquiv (axis, sign) = signedAxis axis sign := by
  apply Fin.ext
  exact Nat.add_comm _ _

/-- A linear encoding of all eight signed carriers needs at least four
staged doublets. A single staged receiver doublet cannot carry that span. -/
theorem bank_doublet_capacity (n : ℕ)
    (e : (Fin 8 → ℂ) →ₗ[ℂ] ((Fin n × Fin 2) → ℂ)) (he : Function.Injective e) :
    4 ≤ n := by
  have h := LinearMap.finrank_le_finrank_of_injective he
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h
  omega

/-- Reindex each input stream by the existing signed-axis coordinates.
The axis is retained alongside the doublet, on both sites. -/
def stagedAxis (state : TwoSiteHandoff.State (Fin 8 → ℂ)) (axis : Fin 4) :
    TwoSiteHandoff.State (Fin 2 → ℂ) :=
  fun site => (fun sign => (state site).1 (signedAxisEquiv (axis, sign)),
    fun sign => (state site).2 (signedAxisEquiv (axis, sign)))

theorem staged_axis_injective : Function.Injective stagedAxis := by
  intro s t h
  funext site
  apply Prod.ext
  · funext j
    obtain ⟨⟨a, sign⟩, rfl⟩ := signedAxisEquiv.surjective j
    exact congrArg (fun f => (f a site).1 sign) h
  · funext j
    obtain ⟨⟨a, sign⟩, rfl⟩ := signedAxisEquiv.surjective j
    exact congrArg (fun f => (f a site).2 sign) h

/-- Given one staged native doublet per retained axis and a common
clock, the same timed pulse on each doublet exchanges the signed-carrier
inputs and keeps their axis labels. Physical supply of the four lanes
and their common pulse is the staging premise. -/
theorem staged_signed_exchange_in_ticks (s : TwoSiteHandoff.State (Fin 8 → ℂ))
    (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) (q : ℕ)
    (hclock : RootTransferPhase.quarterTime p = (q : ℝ) / 2) (axis : Fin 4) :
    Matrix.mulVec
      (NormedSpace.exp ((-((2 * q : ℕ) : ℂ) * Complex.I) •
        ClockedRootTrials.tickGenerator TwoSiteHandoff.receiverRoot p))
      (TwoSiteHandoff.field (stagedAxis s axis)) =
      TwoSiteHandoff.field (stagedAxis (OpenReferenceFlow.exchangeAt 0 s) axis) := by
  rw [BankReceiverPulse.staged_exchange_in_ticks (stagedAxis s axis) p hp hp' q hclock]
  congr 1
  funext site
  by_cases hx : site = 0 <;> simp [OpenReferenceFlow.exchangeAt, stagedAxis, hx]

/-- When the four axis pulses are booked separately for each bank
operation, they consume eight quarter-times for extraction and eight
for reload. This serial slot budget leaves at most three ticks per
quarter-time in the two-period block. -/
theorem serial_axis_block_iff (q : ℕ) :
    2 + (2 * Fintype.card (Fin 4)) * q + (2 * classShiftWord.length) * q +
      (2 * Fintype.card (Fin 4)) * q ≤ 2 * Delta ↔ q ≤ 3 := by
  rw [class_shift_quarter_times]
  simp only [Fintype.card_fin]
  change 2 + 8 * q + 8 * q + 8 * q ≤ 86 ↔ q ≤ 3
  omega

end PMElementaryParticles.RestoringWallShift
