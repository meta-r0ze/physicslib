import PMAction.Machine.CarrierEvents
import PMConstants.RequirementTable

/-!
# The channel representation from Paper I's carriers

Paper III took the representation content of a generation (`Q, u, d, L, e, ν` with multiplicities
`6, 3, 3, 2, 1, 1`) as a premise. Paper II identified the actual carriers: each nontrivial D₄ glue
class has eight minimal vectors (`PMAction.CarrierEvents.carrier_card`). In the vector class these
are `±2eᵢ`, four axes with two signs each: the `(4, 2)` of Pati–Salam's `SU(4) × SU(2)`, with
lepton number as the fourth "colour".

* `one_axis`: every vector-class carrier lies on exactly one axis.
* `lepton_axis_split`: singling out one axis (here axis `0`) leaves `6` carriers on the other three
  and `2` on it. Signs split each set evenly (`sign_split`).
* Reading the three other axes as colour and the sign as the doublet index:
  - left sector: `6` colour carriers (`Q`) and `2` on the lepton axis (`L`);
  - right sector: positive/negative colour carriers are `u`/`d` (`3` each), and the lepton axis gives
    `ν`/`e` (`1` each).
  This is exactly `RequirementTable.multiplicities` (`multiplicities_from_carriers`).
* `bl_traceless`: a lepton-number charge equal on the three colour axes and traceless over the four
  (an `SU(4)` generator) has lepton value `−3` times the colour value; normalized by the forced
  lepton charge `−1`, colour is `1/3`.
* `charges_from_carriers`: with `Y = B − L` on the left and `Y = B − L + 2T₃` on the right
  (`T₃ = ±1/2` from the sign), the carriers reproduce Paper III's forced charges
  (`Hypercharge.standard`): `1/3, 4/3, −2/3, −1, −2, 0`.

Premises: both domain-wall sectors use a class carried to the vector class by triality (any
nontrivial class is, keeping the roots: `PMSubstrate.ChannelSymmetry.class_to_vector`; and all
three classes are admitted, `PMAction.ClassAdmission`), the sign is the doublet index, and one
axis is the lepton axis. The last is the reserved cell's: the frame reserves one cell for its
tone (`ReferenceFrames`, η), the cell holds one carrier state (`ReferenceEconomy.cell_inj_of_content`),
and a carrier lies on exactly one axis (`one_axis`), so the reference singles out one axis
(`ReferenceAxis`). Which axis that is breaks `SU(4)` to colour
times lepton number; a natural reading is the temporal axis, whose clock SU(2) refreshes.
-/

namespace PMConstants.CarrierRepresentation
open PMAction.CarrierEvents

abbrev V := Carrier 0

def coord (v : V) (i : Fin 4) : ℤ := vector v i

theorem one_axis : ∀ v : V, (Finset.univ.filter fun i => coord v i ≠ 0).card = 1 := by
  decide +kernel

def onLepton (v : V) : Bool := coord v 0 ≠ 0
def positive (v : V) : Bool := 0 < ∑ i, coord v i

theorem lepton_axis_split :
    (Finset.univ.filter fun v : V => onLepton v = false).card = 6 ∧
      (Finset.univ.filter fun v : V => onLepton v = true).card = 2 := by
  constructor <;> decide +kernel

theorem sign_split :
    (Finset.univ.filter fun v : V => onLepton v = false ∧ positive v = true).card = 3 ∧
      (Finset.univ.filter fun v : V => onLepton v = false ∧ positive v = false).card = 3 ∧
      (Finset.univ.filter fun v : V => onLepton v = true ∧ positive v = true).card = 1 ∧
      (Finset.univ.filter fun v : V => onLepton v = true ∧ positive v = false).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

open RequirementTable in
def leftType (v : V) : Ty := if onLepton v then .L else .Q

open RequirementTable in
def rightType (v : V) : Ty :=
  if onLepton v then (if positive v then .n else .e) else (if positive v then .u else .d)

open RequirementTable in
theorem multiplicities_from_carriers :
    (Finset.univ.filter fun v : V => leftType v = .Q).card = 6 ∧
    (Finset.univ.filter fun v : V => rightType v = .u).card = 3 ∧
    (Finset.univ.filter fun v : V => rightType v = .d).card = 3 ∧
    (Finset.univ.filter fun v : V => leftType v = .L).card = 2 ∧
    (Finset.univ.filter fun v : V => rightType v = .e).card = 1 ∧
    (Finset.univ.filter fun v : V => rightType v = .n).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem bl_traceless (a b : ℚ) (htr : 3 * a + b = 0) (hl : b = -1) : a = 1/3 ∧ b = -3 * a := by
  constructor <;> linarith

/-- Lepton number minus baryon number per axis, and the right-sector isospin. -/
def bl (v : V) : ℚ := if onLepton v then -1 else 1/3
def t3 (v : V) : ℚ := if positive v then 1/2 else -1/2

open RequirementTable Hypercharge in
theorem charges_from_carriers (v : V) :
    bl v = hyper standard (leftType v) ∧ bl v + 2 * t3 v = hyper standard (rightType v) := by
  unfold bl t3 leftType rightType
  cases onLepton v <;> cases positive v <;> simp [hyper, standard] <;> norm_num

end PMConstants.CarrierRepresentation
