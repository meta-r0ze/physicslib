import PMKAutomaton.Machine.CarrierEvents
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
  (`Hypercharge.standard`): `1/3, 4/3, −2/3, −1, −2, 0`. The right wall's extra `2T₃` is the
  insertion of a link of unit charge, not a separate reading (`carrier_table`,
  `carrierCharges_yukawa`).

Premises: both domain-wall sectors use a class carried to the vector class by triality (any
nontrivial class is, keeping the roots: `PMSubstrate.ChannelSymmetry.class_to_vector`; and all
three classes are admitted, `PMAction.ClassAdmission`), the sign is the doublet index (the only
move keeping a carrier's axis, `CarrierActions.same_axis_iff`, so the refresh that moves the
reference within its axis acts on the sign pair), and one axis is the lepton axis. The last is the reserved cell's: the frame reserves one cell for its
tone (`ReferenceFrames`, η), the cell holds one carrier state (`ReferenceEconomy.cell_inj_of_content`),
and a carrier lies on exactly one axis (`one_axis`), so the reference singles out one axis
(`ReferenceAxis`). Which axis that is breaks `SU(4)` to colour
times lepton number; a natural reading is the temporal axis, whose clock SU(2) refreshes.

So this module's premises are three, and they are the only inputs to the charge table: the
triality carry of both sectors to the vector class, the sign as the doublet index, and the
reserved axis. The lepton charge `−1` is the normalization of `bl_traceless`, and the unit link is
`SectorLinks`. `Hypercharge`'s flux and Yukawa conditions are consequences, not further premises
(`carrierCharges_flux`, `carrierCharges_yukawa`).
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

/-- Baryon number minus lepton number per axis, and the right-sector isospin. -/
def bl (v : V) : ℚ := blAxis (onLepton v)
def t3 (v : V) : ℚ := t3Sign (positive v)

open RequirementTable Hypercharge in
theorem charges_from_carriers (v : V) :
    bl v = packetHypercharge carrierStandard (leftType v) ∧ bl v + 2 * t3 v = packetHypercharge carrierStandard (rightType v) := by
  unfold bl t3 leftType rightType
  cases onLepton v <;> cases positive v <;> simp [packetHypercharge, carrierStandard, carrierCharges, blAxis, t3Sign] <;> norm_num

/-! ## The charge table from the carriers

`Hypercharge` selects its table with a flux condition, a Yukawa-balance condition, a neutral
sterile channel and a unit scalar charge. On the carriers the first two are not extra conditions:
flux conservation is tracelessness over the four axes (`carrierCharges_flux`), and the Yukawa
balance is the statement that the link carries one unit of charge (`carrierCharges_yukawa`). So
the table follows from the carrier geometry, the forced lepton charge and the unit link
(`carrierCharges_eq_standard`).
-/

/-- **The table in terms of `bl` and `t3`.** The left wall carries the axis value; the right wall
adds `2 h t3`, the insertion of a link of charge `h`. -/
theorem carrier_table (a b h : ℚ) (v : V) :
    RequirementTable.packetHypercharge (carrierCharges a b h) (leftType v) = (if onLepton v then b else a) ∧
      RequirementTable.packetHypercharge (carrierCharges a b h) (rightType v) =
        (if onLepton v then b else a) + 2 * h * t3 v := by
  unfold carrierCharges leftType rightType t3
  cases onLepton v <;> cases positive v <;>
    simp [RequirementTable.packetHypercharge, t3Sign] <;> ring

/-- **Flux conservation is axis tracelessness.** The two further flux conditions hold for every
`a`, `b`, `h`. -/
theorem carrierCharges_flux (a b h : ℚ) (htr : 3 * a + b = 0) :
    Hypercharge.Flux (carrierCharges a b h) := by
  dsimp [Hypercharge.Flux, carrierCharges]
  exact ⟨by linarith, by ring, by ring⟩

/-- **The Yukawa balance is the unit link.** The right wall differs from the left by the link's
own charge, so the balance holds by construction, for any `h`. -/
theorem carrierCharges_yukawa (a b h : ℚ) : Hypercharge.Yukawa (carrierCharges a b h) h :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The carrier table is the standard table.** Tracelessness over the four axes with the forced
lepton charge (`bl_traceless`) and one unit of link charge give exactly `Hypercharge.standard`.
No Yukawa-invariance premise is used. -/
theorem carrierCharges_eq_standard (a b : ℚ) (htr : 3 * a + b = 0) (hl : b = -1) :
    carrierCharges a b 1 = Hypercharge.standard := by
  obtain ⟨ha, -⟩ := bl_traceless a b htr hl
  subst hl
  subst ha
  norm_num [carrierCharges, Hypercharge.standard]

/-- The carriers' own values are that table: `bl` on the left wall, `bl + 2 t3` on the right. -/
theorem charges_eq_carrier_table (v : V) :
    bl v = RequirementTable.packetHypercharge (carrierCharges (1/3) (-1) 1) (leftType v) ∧
      bl v + 2 * t3 v = RequirementTable.packetHypercharge (carrierCharges (1/3) (-1) 1) (rightType v) := by
  exact charges_from_carriers v

end PMConstants.CarrierRepresentation
