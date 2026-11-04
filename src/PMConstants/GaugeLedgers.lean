import PMConstants.ResourceLedger
import PMConstants.GaugeStiffness

/-!
# One rule, one table: all three gauge ledgers

Resources per phase, from Paper III's partition `(43, 129, P_t, 5)`: the clock row (`43`), the
three spatial rows (`129`), the wires (`σ = 5`), and one payload per channel (`η` each).
Requirements, from Paper V's channel attributes:

* SU(2) couples to the active temporal boundary: it requires the clock only.
* Hypercharge is boundary flux carried across the spatial grid (Paper V, "Map and Capacity"):
  it requires the spatial rows, the wires, and the payload of every channel whose flux is kept,
  including the sterile reference against which flux is measured.
* Colour routes payload through the colour bulk: it requires the payload of the 12 coloured
  channels.

With the minimal-refresh rule (one refresh per distinct required resource):

* `su2_value`, `hyper_value`, `colour_value`: the ledgers are `43`, `129 + 5 + 16η` and `12η`.
* `mixing_from_rule`: `43/(43 + Y) = Δ/N_sys`, the paper's weak mixing (`clockRatio`).
* `footprint_from_rule`: `43 + Y = N_sys`; the electric coupling's footprint is the sum of the
  two electroweak ledgers, as `GaugeStiffness.electric` requires.
* `strong_from_rule`: `α N_sys/(12η)`, the colour readout of `ColourChannels`.

The alternative that excludes the sterile reference from hypercharge's requirements gives
`ResourceLedger.footprint15` and is disfavoured by the W mass at more than 3.1σ
(`ResourceLedger.sterile_counted`). Premises: the minimal-refresh rule and the requirement
table above, read from Papers III and V.
-/

noncomputable section
namespace PMConstants.GaugeLedgers
open PMConstants

inductive Res | clock | space | wires | payload (i : Fin 16)
  deriving DecidableEq

def weight : Res → ℝ
  | .clock => 43
  | .space => 129
  | .wires => 5
  | .payload _ => overhead

/-- Ledger of a requirement set: one refresh per distinct resource. -/
def ledger (R : Finset Res) : ℝ := ∑ r ∈ R, weight r

def reqSU2 : Finset Res := {Res.clock}
def reqY : Finset Res := {Res.space, Res.wires} ∪ Finset.univ.image Res.payload
def reqColour : Finset Res := ResourceLedger.colouredSet.image Res.payload

lemma payload_inj : Function.Injective Res.payload := fun a b h => by cases h; rfl

theorem su2_value : ledger reqSU2 = 43 := by simp [ledger, reqSU2, weight]

theorem hyper_value : ledger reqY = 129 + 5 + 16 * overhead := by
  unfold ledger reqY
  rw [Finset.sum_union (by
    rw [Finset.disjoint_left]; intro r hr hr'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr'
    rcases hr with h | h <;> cases h)]
  rw [Finset.sum_image (fun a _ b _ h => payload_inj h)]
  simp [weight]

theorem colour_value : ledger reqColour = ColourChannels.colourLedger := by
  unfold ledger reqColour
  rw [Finset.sum_image (fun a _ b _ h => payload_inj h)]
  simp only [weight, Finset.sum_const, nsmul_eq_mul, ResourceLedger.coloured_card]
  norm_num [ColourChannels.colourLedger]

theorem footprint_from_rule : ledger reqSU2 + ledger reqY = footprint := by
  rw [su2_value, hyper_value]; unfold footprint; ring

theorem mixing_from_rule : ledger reqSU2 / (ledger reqSU2 + ledger reqY) = clockRatio := by
  rw [footprint_from_rule, su2_value]; rfl

theorem strong_from_rule :
    CertifiedConstants.α * (ledger reqSU2 + ledger reqY) / ledger reqColour =
      CertifiedConstants.α * footprint / ColourChannels.colourLedger := by
  rw [footprint_from_rule, colour_value]

end PMConstants.GaugeLedgers
