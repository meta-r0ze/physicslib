import PMConstants.PacketGaugeActions
import PMAction.CyclicSeesaw
import PMAction.NativeFlavourWall
import PMAction.GenerationWalls

/-! Colour relabelling on the existing 48 generation-wall labels.
The bare exchange keeps the carrier. A weighted exchange also preserves colour
exactly when its coefficient is constant on colour orbits. This tests the
crossing separately from the on-site chirality flip. -/
namespace PMConstants.ColourWallCrossing
open PMAction PMAction.GenerationWalls PMConstants.CarrierActions

/-- Apply the packet's coordinate transposition in each native glue class. -/
def relabel (a b : Fin 3) (p : WallNative) : WallNative :=
  (p.1, ⟨p.2.1, CarrierEvents.permute p.2.1 (Equiv.swap (colourAxis a) (colourAxis b)) p.2.2⟩)

/-- The vector-class restriction agrees with the physical packet in both sectors. -/
theorem packet_agreement (a b : Fin 3) (p : Packet) :
    (relabel a b (false, ⟨0, carried p⟩)).2 =
      ⟨0, carried (colour a b p)⟩ := by cases p <;> rfl

/-- The existing on-site β and the physical axis action disagree on an
actual vector carrier. An independent colour index changes this realization. -/
theorem beta_fails_packet_colour : ∃ v : CarrierEvents.Carrier 0,
    CarrierWeyl.lookup 0 0 (axisExchange 0 1 v) ≠
      axisExchange 0 1 (CarrierWeyl.lookup 0 0 v) := by decide +kernel

/-- Extra registers cannot repair the mismatch through a faithful encoding
that still intertwines both original operations, even for this one colour swap. -/
theorem no_faithful_joint_encoding {X : Type*} (encode : CarrierEvents.Carrier 0 → X)
    (faithful : Function.Injective encode) (B C : X → X)
    (hb : ∀ v, encode (CarrierWeyl.lookup 0 0 v) = B (encode v))
    (hc : ∀ v, encode (axisExchange 0 1 v) = C (encode v)) :
    ¬ Function.Commute B C := by
  intro comm
  obtain ⟨v, hv⟩ := beta_fails_packet_colour
  apply hv
  apply faithful
  rw [hb, hc, hc, hb]
  exact comm (encode v)

theorem exchange_equivariant (a b : Fin 3) (p : WallNative) :
    exchange (relabel a b p) = relabel a b (exchange p) := rfl

/-- On basis labels the weighted exchange outputs one target and one coefficient. -/
def weighted (w : WallNative → ℂ) (p : WallNative) := (exchange p, w p)

theorem weighted_equivariant_iff (w : WallNative → ℂ) :
    (∀ a b p, weighted w (relabel a b p) =
      (relabel a b (weighted w p).1, (weighted w p).2)) ↔
    ∀ a b p, w (relabel a b p) = w p := by
  simp [weighted, exchange_equivariant]

/-- Each directed wall/class leg may have its own complex coefficient. -/
theorem class_leg_equivariant (y : Bool → Fin 3 → ℂ) (a b : Fin 3) (p : WallNative) :
    weighted (fun q => y q.1 q.2.1) (relabel a b p) =
      (relabel a b (exchange p), y p.1 p.2.1) := rfl

/-- A colour-sensitive phase can violate equivariance with exactly the same
exchange targets and modulus one. The witness lives on the actual carriers. -/
theorem support_and_unit_modulus_insufficient :
    ∃ w : WallNative → ℂ, (∀ p, ‖w p‖ = 1) ∧
      ¬ ∀ a b p, w (relabel a b p) = w p := by
  let mark (p : WallNative) := CarrierEvents.vector p.2.2 (colourAxis 0) ≠ 0
  have witness : ∃ v : CarrierEvents.Carrier 0,
      ¬ (mark (relabel 0 1 (false, ⟨0, v⟩)) ↔ mark (false, ⟨0, v⟩)) := by
    dsimp [mark]
    decide +kernel
  refine ⟨fun p => if mark p then 1 else -1, ?_, ?_⟩
  · intro p
    by_cases hm : mark p <;> simp [hm]
  · intro h
    obtain ⟨v, hv⟩ := witness
    have he := h 0 1 (false, ⟨0, v⟩)
    by_cases h₁ : mark (relabel 0 1 (false, ⟨0, v⟩)) <;>
      by_cases h₂ : mark (false, ⟨0, v⟩)
    all_goals simp [h₁, h₂] at hv he <;> norm_num at he

noncomputable section
open Matrix PacketGaugeActions
open scoped Kronecker

/-- One coloured triplet/doublet block per wall. Both sectors of the actual
packet carry precisely this action. -/
def triplet (V : Matrix (Fin 3) (Fin 3) ℂ) := V ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem packet_blocks (V : Matrix (Fin 3) (Fin 3) ℂ) (i j : Q) :
    PacketGaugeActions.colour V (.inl i) (.inl j) = triplet V i j ∧
    PacketGaugeActions.colour V (.inr (.inl i)) (.inr (.inl j)) = triplet V i j := ⟨rfl, rfl⟩

abbrev Payload := Fin 3 × Q
def action (V : Matrix (Fin 3) (Fin 3) ℂ) : Matrix Payload Payload ℂ :=
  (1 : Matrix (Fin 3) _ ℂ) ⊗ₖ triplet V

def crossing (y : Fin 3 → ℂ) : Matrix Payload Payload ℂ :=
  CyclicSeesaw.cyc y ⊗ₖ (1 : Matrix Q _ ℂ)

theorem directed_links (V : Matrix (Fin 3) (Fin 3) ℂ) (y : Fin 3 → ℂ) :
    action V * crossing y = crossing y * action V ∧
    action V * (crossing y)ᴴ = (crossing y)ᴴ * action V := by
  simp [action, crossing, conjTranspose_kronecker, ← mul_kronecker_mul]

theorem wall_colour (V : Matrix (Fin 3) (Fin 3) ℂ) (y : Fin 3 → ℂ)
    (k : Fin 3 → ℝ) (δ₁ δ₂ : ℝ) :
    let C := WallExchange.payloadAction (action V)
    let H := WallExchange.H2 k δ₁ δ₂ (crossing y)
    C * H = H * C :=
  (WallExchange.payload_symmetry_iff _ _ _ _ _).mpr (directed_links V y)

theorem native_colour (c : Fin 3) (V : Matrix (Fin 3) (Fin 3) ℂ) (y : Fin 3 → ℂ)
    (p : ℝ) (k : Fin 3 → ℝ) (δ₁ δ₂ : ℝ) :
    let B := (1 : Matrix (CarrierEvents.Carrier c) _ ℂ) ⊗ₖ action V
    let C := fromBlocks B 0 0 B
    let H := NativeFlavourWall.nativeHamiltonian2 c p k δ₁ δ₂ (crossing y)
    C * H = H * C :=
  NativeFlavourWall.native_payload_symmetry c _ _ _ _ _ _
    (directed_links V y).1 (directed_links V y).2

end
end PMConstants.ColourWallCrossing
