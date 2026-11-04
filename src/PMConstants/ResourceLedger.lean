import PMConstants.ColourChannels
import PMConstants.WMassTest

/-!
# Shared versus per-channel resources: one rule for the weak and colour ledgers

Paper V (`4_protocols.tex`, Table "The ν = 16 chiral channels") gives each channel two binary
attributes: whether it routes through the colour bulk (`N_res = σ − χ = 3`, channels 1–12) and
whether it couples to the active left-handed temporal boundary (channels 1–6, 13–14). The two
resources differ in kind: the temporal boundary is one clock shared by every active channel,
while each coloured channel has its own internal routing.

Rule (minimal persistent refresh). The work a sector's links must do per phase is the sum over the
*distinct* resources its channels require. Refreshing the same resource once per user duplicates
work (Economy); dropping a distinct required resource loses a distinction (Conservation,
`FinalPremises.description_minimal`).

* `ledger_shared`: if every channel maps to one resource `r`, the ledger is `w r` however many
  channels use it. For SU(2) the resource is the clock row, `w = Δ = 43`: `GaugeStiffness`'s
  premise `W = Δ` follows.
* `ledger_per_channel`: if channels map injectively to resources of weight `η`, the ledger is
  `(number of channels) · η`. For colour, `12η` (`ColourChannels`).
* `su2_ledger`, `colour_ledger_rule`: the two instances with Paper V's channel table.

The sterile channel 16 is Paper V's locked reference. Whether its capacity counts in the
footprint is decided by the W mass: `sterile_counted` shows that dropping it (`15η` payload)
moves `m_W` below `80.3268` GeV, more than 3.1σ under the direct world average, while the
counted footprint (`WMassTest`) is within 1.3σ. The sterile channel's capacity persists in the
footprint as the reference it holds.
-/

noncomputable section
namespace PMConstants.ResourceLedger
open PMConstants

/-- Minimal per-phase refresh work: one refresh per distinct required resource. -/
def ledger {C R : Type*} [DecidableEq R] (S : Finset C) (res : C → R) (w : R → ℝ) : ℝ :=
  ∑ r ∈ S.image res, w r

theorem ledger_shared {C R : Type*} [DecidableEq R] (S : Finset C) (hS : S.Nonempty)
    (r : R) (w : R → ℝ) : ledger S (fun _ => r) w = w r := by
  unfold ledger
  rw [Finset.image_const hS, Finset.sum_singleton]

theorem ledger_per_channel {C R : Type*} [DecidableEq R] (S : Finset C) (res : C → R)
    (hinj : Set.InjOn res S) (w : R → ℝ) (η : ℝ) (hw : ∀ c ∈ S, w (res c) = η) :
    ledger S res w = S.card * η := by
  unfold ledger
  rw [Finset.sum_image hinj, Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]

/-! ## Paper V's channel table -/

/-- Channels 1–16 as `Fin 16` (index `i` is channel `i+1`). -/
def colourBulk (i : Fin 16) : Bool := i.val < 12
def activeBoundary (i : Fin 16) : Bool := i.val < 6 ∨ i.val = 12 ∨ i.val = 13

def colouredSet : Finset (Fin 16) := Finset.univ.filter fun i => colourBulk i
def activeSet : Finset (Fin 16) := Finset.univ.filter fun i => activeBoundary i

theorem coloured_card : colouredSet.card = 12 := by decide
theorem active_card : activeSet.card = 8 := by decide

/-- Resources: the shared clock, or a channel's own colour routing. -/
inductive Res | clock | route (i : Fin 16)
  deriving DecidableEq

def weight : Res → ℝ
  | .clock => 43
  | .route _ => overhead

theorem su2_ledger : ledger activeSet (fun _ => Res.clock) weight = 43 :=
  ledger_shared _ (by decide) _ _

theorem colour_ledger_rule :
    ledger colouredSet Res.route weight = ColourChannels.colourLedger := by
  rw [ledger_per_channel colouredSet Res.route (fun a _ b _ h => by cases h; rfl) weight overhead
    (fun _ _ => rfl), coloured_card]
  norm_num [ColourChannels.colourLedger]

/-! ## The sterile channel's capacity counts -/

def footprint15 : ℝ := 172 + 15 * overhead + 5

theorem sterile_counted {mZ : ℝ} (h : 91.1855 < mZ ∧ mZ < 91.1897) :
    mZ * Real.sqrt (1 - 43/footprint15) < 80.3268 ∧
      (mZ * Real.sqrt (1 - 43/footprint15) - 80.3692) / 0.0133 < -3.1 := by
  have hr : Real.sqrt (1 - 43/footprint15) < 0.8808755 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num [footprint15, overhead]
  have hp : 0 ≤ Real.sqrt (1 - 43/footprint15) := Real.sqrt_nonneg _
  have h1 : mZ * Real.sqrt (1 - 43/footprint15) < 80.3268 := by nlinarith [h.1, h.2]
  refine ⟨h1, ?_⟩
  rw [div_lt_iff₀ (by norm_num)]; linarith

end PMConstants.ResourceLedger
