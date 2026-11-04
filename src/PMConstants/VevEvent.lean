import PMConstants.VevReadout
import PMConstants.DepthEvents
import PMAction.LinkExpansion

/-!
# The VEV is read from an event, and events happen only on spatial hops

`VevReadout` reduced the noise divisor to one premise: the VEV's normalized readout puts no weight
on the reference's time axis. A normalized law with weight `w₀` there reads `(1 − w₀) Y/3`, so
`w₀ = 0` gives the divisor `3` and the uniform four-axis law gives `4`. This module derives
`w₀ = 0` from the event principle already used for depth (`DepthEvents.no_event_no_advance`:
nothing is registered without an event).

* `flag_zero_iff`: a comparison of the reference `φ` with its transport `U φ` has flag probability
  `stateFlag U φ = ‖φ − Uφ‖²/4` (Paper II `CommonResponse`), which is zero exactly when `U` fixes `φ`.
* Along the time axis the transport of the maintained reference is the maintenance update itself.
  Exact repair returns the reference (`RepairBudget`), so that comparison never fires
  (`time_never_fires`).
* `conditioned_on_event`: for any prior law `π` over the four axes and any per-axis event
  probabilities `f` with `f₀ = 0`, the law of the axis *given that a readout event occurred*,
  `qᵢ = πᵢ fᵢ / Σ πⱼ fⱼ`, is normalized with `q₀ = 0`.
* `vev_reads_spatial_share`: hence the event-conditioned readout reads exactly `Y/3`, whatever the
  prior law. The uniform four-axis reading `Y/4` would need the time comparison to fire, which
  exact repair forbids.

Premise: the VEV is read from a comparison that registers (an event), the same event principle as
`DepthEvents`. Together with `VevReadout`, both correction factors of the VEV now rest on exact
repair, one repair (`PersistenceClosures.one_repair`) and this event principle.
-/

noncomputable section
namespace PMConstants.VevEvent
open PMAction CommonResponse

/-- **A comparison fires only if the transport moves the reference.** -/
theorem flag_zero_iff {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (φ : ι → ℂ) :
    stateFlag U φ = 0 ↔ U.mulVec φ = φ := by
  unfold stateFlag
  rw [LinkExpansion.nsq_eq]
  constructor
  · intro h
    have hs : ∑ k, Complex.normSq ((φ - U.mulVec φ) k) = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).mp hs
    funext k
    have := Complex.normSq_eq_zero.mp (hall k (Finset.mem_univ k))
    simp only [Pi.sub_apply, sub_eq_zero] at this
    exact this.symm
  · intro h
    simp [h]

/-- **The time-axis comparison of an exactly repaired reference never fires.** -/
theorem time_never_fires {ι : Type*} [Fintype ι] (Umaint : Matrix ι ι ℂ) (φ : ι → ℂ)
    (hfix : Umaint.mulVec φ = φ) : stateFlag Umaint φ = 0 :=
  (flag_zero_iff Umaint φ).mpr hfix

/-- **Conditioning on an event removes the time axis.** -/
theorem conditioned_on_event (π f : Fin 4 → ℝ) (hπ : ∀ i, 0 ≤ π i) (hf : ∀ i, 0 ≤ f i)
    (hf0 : f 0 = 0) (hZ : 0 < ∑ j, π j * f j) :
    let q := fun i => π i * f i / ∑ j, π j * f j
    q 0 = 0 ∧ (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 := by
  intro q
  refine ⟨by simp [q, hf0], fun i => div_nonneg (mul_nonneg (hπ i) (hf i)) hZ.le, ?_⟩
  simp only [q, ← Finset.sum_div]
  exact div_self hZ.ne'

/-- **The VEV reads one spatial axis's share, `Y/3`.** -/
theorem vev_reads_spatial_share (share : Fin 4 → ℝ) (Yn : ℝ) (hexact : share 0 = 0)
    (h12 : share 1 = share 2) (h13 : share 1 = share 3) (hsum : ∑ i, share i = Yn)
    (π f : Fin 4 → ℝ) (hπ : ∀ i, 0 ≤ π i) (hf : ∀ i, 0 ≤ f i) (hf0 : f 0 = 0)
    (hZ : 0 < ∑ j, π j * f j) :
    ∑ i, (π i * f i / ∑ j, π j * f j) * share i = Yn / 3 := by
  obtain ⟨h0, -, h1⟩ := conditioned_on_event π f hπ hf hf0 hZ
  exact VevReadout.normalized_share share Yn hexact h12 h13 hsum _ h0 h1

/-- With the time comparison firing at zero rate, the four-axis reading `Y/4` is unreachable:
the conditioned law always reads `Y/3`, and `Y/3 ≠ Y/4` for `Y ≠ 0`. -/
theorem four_unreachable (Yn : ℝ) (hY : Yn ≠ 0) : Yn / 3 ≠ Yn / 4 := by
  intro h; apply hY; linarith

end PMConstants.VevEvent
