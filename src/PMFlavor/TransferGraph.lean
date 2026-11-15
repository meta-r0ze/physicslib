import PMFlavor.ExchangeChirality
import PersistenceMechanics.InformationTransfer

/-!
# The generation transfers on E8 and their types

Each pair of generations transfers through the one glue class both contain
(`PMAction.GenerationLabel.transition_class`, `ExchangeChirality.hop_class`). Generation `g` omits
class `g` and carries `g + 1` and `g − 1` (`PMAction.GenerationWalls.side`), so the transfer through
class `c` joins generations `c + 1` and `c − 1` (`ends`). The reference's class is the vector class
`0` (`PMConstants.CarrierRepresentation`), and generation `0`, which omits it, is the
reference-free generation.

**What is derived.**
* `inCycle_iff`: a class has an exchange displacement off the reference axis exactly when it is the
  reference's class (`ExchangeAxis.vector_free`, `spinor_ne`). So exactly one transfer (through `0`,
  generations `1` and `2`) stays inside the maintenance cycle; the other two change the channel type
  and cross the reference node, by two legs each (`LinkKronComparison.two_leg_from_incidence`).
* `node_walls_opposite`, `swap_flips_wall`: the two node-crossing classes sit on opposite walls of the
  reference-free generation (`ExchangeChirality.free_generation_split`), and the class swap fixing
  the reference exchanges them while flipping the wall.
* `three_types`: the data a one-wall current can see, (in-cycle?, wall), separate all three
  transfers. `two_types_blind`: without the wall (a probe symmetric under wall exchange, for which
  swap × exchange is a symmetry, `ExchangeChirality.swap_with_exchange`) the two node crossings are
  one type. The charged current couples to one wall (`PMAction.WallChiralCurrent`), so the substrate
  has exactly three transfer types as the charged current sees them, and two otherwise.

**Mode assignment (candidate).** `mode`: the in-cycle transfer is boundary conduction; a node
crossing whose class sits on the reference's wall is capacity promotion; the one on the other wall
is a coordinate jump. Derived part: `mode_continuous_iff` with `inCycle_iff`, the continuous mode is
exactly the transfer that stays in the cycle. Premise (not derived): a hop of a class on the
reference's wall starts inside the node's refresh (adjacent), while a hop on the other wall must
enter and leave the node (non-adjacent). `refWall` is the reference's wall, `false`, the wall of the
reference background in `PMAction.ReferenceDetuning` and `PMAction.ReferenceWallMass`.

**Which generations each joins.** `mode_ends`: the conduction joins generations `1` and `2`, the
promotion `0` and `1`, the jump `0` and `2`; generation `0` is the label-`v` generation, the one whose
two transfers both cross the node (`PMAction.MassInsertion.label_v_mixings_cross`). The readout as
matrix elements (e8p prints the conduction as `s₁₂`, the promotion as `|V_cb|`, the jump as `|V_ub|`)
names generation `1` the second and `2` the first, the wall-naming convention
(`GenerationWalls.balanced_classification`); which protocols read which transfers is
PMElementaryParticles.
-/

namespace PMFlavor.TransferGraph
open PMAction.GenerationWalls PMAction.CarrierEvents PersistenceMechanics.InformationTransfer

/-- The transfer through class `c` joins generations `c + 1` and `c − 1`. -/
def ends (c : Fin 3) : Fin 3 × Fin 3 := (c + 1, c - 1)

/-- **Both ends contain the class, and the ends differ.** Generation `g` omits class `g`. -/
theorem ends_share : ∀ c : Fin 3, (ends c).1 ≠ (ends c).2 ∧ c ≠ (ends c).1 ∧ c ≠ (ends c).2 := by
  decide

/-- **Every pair of generations has its transfer.** -/
theorem every_pair : ∀ g g' : Fin 3, g ≠ g' → ∃ c : Fin 3, ends c = (g, g') ∨ ends c = (g', g) := by
  decide

/-- A transfer stays in the cycle when its class has an exchange displacement off the reference
axis `0`. -/
def InCycle (c : Fin 3) : Prop := ∃ d : Carrier c, vector d 0 = 0

/-- **Exactly the reference's class transfers inside the cycle.** -/
theorem inCycle_iff (c : Fin 3) : InCycle c ↔ c = 0 := by
  constructor
  · rintro ⟨d, hd⟩
    by_contra h
    exact ExchangeAxis.spinor_ne c h d hd
  · rintro rfl
    have hpos : 0 < (Finset.univ.filter fun d : Carrier 0 => vector d 0 = 0).card := by
      rw [ExchangeAxis.vector_free]; norm_num
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
    exact ⟨d, (Finset.mem_filter.mp hd).2⟩

/-- The wall of a class in the reference-free generation `0`. -/
def wall (c : Fin 3) : Bool := side 0 c

/-- **The two node-crossing classes sit on opposite walls.** -/
theorem node_walls_opposite : wall 1 ≠ wall 2 := by decide

/-- **The class swap fixing the reference exchanges the node crossings and flips the wall.** -/
theorem swap_flips_wall : ExchangeChirality.swap 0 0 = 0 ∧ ExchangeChirality.swap 0 1 = 2 ∧
    ∀ c : Fin 3, c ≠ 0 → wall (ExchangeChirality.swap 0 c) = !wall c := by
  decide

/-- What a current coupled to one wall sees of a transfer: in-cycle or not, and its wall. -/
def typeData (c : Fin 3) : Bool × Bool := (decide (c = 0), wall c)

/-- **Three transfer types** as a one-wall current sees them. -/
theorem three_types : Function.Injective typeData := by decide

/-- What a probe symmetric under wall exchange sees: in-cycle or not. -/
def typeBlind (c : Fin 3) : Bool := decide (c = 0)

/-- **Two transfer types** for a wall-symmetric probe. -/
theorem two_types_blind : typeBlind 1 = typeBlind 2 ∧ typeBlind 0 ≠ typeBlind 1 := by decide

/-- The reference's wall (the wall of the reference background). -/
def refWall : Bool := false

/-- **Mode of each transfer (candidate assignment).** -/
def mode (c : Fin 3) : TransferMode :=
  if c = 0 then .boundaryConduction
  else if wall c = refWall then .capacityPromotion else .coordinateJump

/-- **The continuous mode is exactly the in-cycle transfer.** -/
theorem mode_continuous_iff : ∀ c : Fin 3, (mode c).continuous = true ↔ c = 0 := by decide

/-- **Each transfer has its own mode.** -/
theorem modes_distinct : Function.Injective mode := by decide

/-- The assignment: through `0` conduction, through `2` promotion, through `1` jump. -/
theorem mode_values :
    mode 0 = .boundaryConduction ∧ mode 2 = .capacityPromotion ∧ mode 1 = .coordinateJump := by
  decide

/-- The promotion joins generations `0` and `1`, the jump `0` and `2`, the conduction `1` and `2`. -/
theorem mode_ends : ends 2 = (0, 1) ∧ ends 1 = (2, 0) ∧ ends 0 = (1, 2) := by decide

end PMFlavor.TransferGraph
