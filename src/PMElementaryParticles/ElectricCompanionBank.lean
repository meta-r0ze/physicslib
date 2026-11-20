import PMElementaryParticles.CompanionHeavyFlip
import PMElementaryParticles.ElectricChiralKick
import PMTransport.Interface

/-!
# Triality preparation of the companion's electric bank

On antipodal-odd carrier amplitudes the actual glue-class transport acts
as the coordinate triality matrix. In either target companion class, a
single forward transport from a supplied occupied coordinate seed in the
predecessor class gives the balanced bank. The existing six-root word
implements this transport on the diagonal glued sector. The class guard
works across the whole bank. Provision of the odd seed and local admission
and duration of the word remain inputs.
-/

noncomputable section
namespace PMElementaryParticles.ElectricCompanionBank

open Matrix PMAction CarrierEvents
open PMConstants.PacketGaugeActions

open PMTransport.CarrierTriality
export PMTransport.CarrierTriality
  (carrierTriality trialityMatrix triality_unitary triality_observed diagonalRoot glued_triality_step)

def seed : Fin 4 → ℂ := Pi.single 0 1

theorem triality_balances_seed : trialityMatrix *ᵥ seed = ElectricFourPortRecord.bank 1 1 := by
  ext i
  fin_cases i <;> norm_num [trialityMatrix, GluedRegister.M, seed, ElectricFourPortRecord.bank]

theorem triality_returns_seed :
    trialityMatrix *ᵥ (trialityMatrix *ᵥ ElectricFourPortRecord.bank 1 1) = seed := by
  rw [← triality_balances_seed, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, triality_cube, Matrix.one_mulVec]

/-- The companion classes on the two heavy-wall insertions are supplied by
forward triality from classes 1 and 0 respectively. -/
def seedClass (wall : Bool) : Fin 3 := if wall then 0 else 1

theorem seed_target (wall : Bool) :
    seedClass wall + 1 = ControlledGluedRegister.wallClass 0 (!wall) := by
  cases wall <;> decide +kernel

/-- On either wall the incoming companion can carry a balanced electric bank.
Its preparation is one forward triality permutation of the occupied odd
seed in the predecessor class. -/
theorem prepares_companion_bank (wall : Bool) :
    (CarrierParity.embedding (seedClass wall + 1) *ᵥ ElectricFourPortRecord.bank 1 1) ∘
      carrierTriality (seedClass wall) = CarrierParity.embedding (seedClass wall) *ᵥ seed := by
  rw [← triality_balances_seed]
  exact triality_observed _ _

/-- Close the class-changing preparation to a reversible exchange on the
direct sum of its source and destination classes. -/
def classExchange (c : Fin 3) : Equiv.Perm (Carrier c ⊕ Carrier (c + 1)) :=
  (Equiv.sumCongr (carrierTriality c) (carrierTriality c).symm).trans (Equiv.sumComm _ _)

private theorem seed_population (c : Fin 3) :
    CommonResponse.nsq (CarrierParity.embedding c *ᵥ seed) = 1 := by
  unfold CommonResponse.nsq
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, CarrierParity.isometry, one_mulVec]
  simp [seed, dotProduct, Pi.single_apply]

/-- A comparison retaining the original class flags half the time on this
triality setup. With one registration per such flag, this is a common setup
cost for either wall, conditional on the odd seed already being supplied. -/
theorem setup_class_flag (wall : Bool) :
    let c := seedClass wall
    CommonResponse.stateFlag ((classExchange c).permMatrix ℂ)
      (Sum.elim (CarrierParity.embedding c *ᵥ seed) (fun _ => 0)) = 1 / 2 := by
  dsimp only
  rw [CommonResponse.state_flag_formula _ (CarrierResponse.perm_unitary _) _]
  · rw [Matrix.permMatrix_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, classExchange]
  · simpa only [CommonResponse.nsq, dotProduct, Fintype.sum_sum_type, Pi.star_apply,
      Sum.elim_inl, Sum.elim_inr, star_zero, zero_mul, Finset.sum_const_zero, add_zero] using
      seed_population (seedClass wall)

/-- The companion part of the guarded heavy flip uses two forward
triality steps from the static wall, and one from the active wall. -/
def companionTransport (wall : Bool) :
    Carrier (ControlledGluedRegister.wallClass 0 (!wall)) ≃
      Carrier (ControlledGluedRegister.wallClass 0 wall) := by
  cases wall
  · exact (carrierTriality 2).trans (carrierTriality 0)
  · exact carrierTriality 1

private theorem companion_vector (wall : Bool)
    (v : Carrier (ControlledGluedRegister.wallClass 0 (!wall))) :
    vector (companionTransport wall v) =
      if wall then GluedRegister.triality (vector v)
      else GluedRegister.triality (GluedRegister.triality (vector v)) := by
  cases wall
  · change vector (carrierTriality 0 (carrierTriality 2 v)) =
      GluedRegister.triality (GluedRegister.triality (vector v))
    exact (carrierTriality_vector 0 (carrierTriality 2 v)).trans
      (congrArg GluedRegister.triality (carrierTriality_vector 2 v))
  · exact carrierTriality_vector 1 v

set_option maxRecDepth 4096 in
private theorem reverse_diagonal_root : ∀ a : Fin 8,
    let w := GluedRegister.carrier 2 a
    (HeavyCrossingCost.word true).foldl
      (fun p r => GluedRegister.reflectPair (HeavyCrossingCost.rootPair r) p) (w, w) =
      (GluedRegister.triality (GluedRegister.triality w),
        GluedRegister.triality (GluedRegister.triality w)) := by
  decide +kernel

/-- The companion uses the opposite six-root word from the live root.
The diagonal code realizes its endpoint update in either direction. -/
theorem companion_transport_roots (wall : Bool)
    (v : Carrier (ControlledGluedRegister.wallClass 0 (!wall))) :
    (HeavyCrossingCost.word (!wall)).foldl
      (fun p r => GluedRegister.reflectPair (HeavyCrossingCost.rootPair r) p)
      (diagonalRoot v) = diagonalRoot (companionTransport wall v) := by
  cases wall
  · change Carrier 2 at v
    obtain ⟨a, ha⟩ := carrier_is_glued 2 v
    have hv : vector (companionTransport false v) =
        GluedRegister.triality (GluedRegister.triality (vector v)) := companion_vector false v
    calc
      _ = let w := GluedRegister.triality (GluedRegister.triality (vector v))
          (w, w) := by
        change (HeavyCrossingCost.word true).foldl
          (fun p r => GluedRegister.reflectPair (HeavyCrossingCost.rootPair r) p)
          (vector v, vector v) = _
        rw [ha]
        exact reverse_diagonal_root a
      _ = _ := congrArg (fun w => (w, w)) hv.symm
  · exact glued_triality_step 1 v

private theorem carrier_is_frame : ∀ (x : Fin 3) (v : Carrier x),
    ∃ k : Fin 8, vector v = ControlledGluedRegister.frame x k := by
  decide +kernel

/-- The class address remains valid on every carrier supporting the ready
bank, and the actual guarded flip transports that same carrier. -/
theorem guarded_companion_transport (c : Channels) (a : Fin 8)
    (v : Carrier (ControlledGluedRegister.wallClass 0 (!ProtocolInventory.active c))) :
    let r := HeavyFlipControl.labelRecord c
    let w : CompanionHeavyFlip.State := (ControlledGluedRegister.encode 0 c a, vector v)
    CompanionHeavyFlip.ready (ProtocolInventory.active c) w = true ∧
      CompanionHeavyFlip.run r r w =
        (ControlledGluedRegister.encode 0 (ControlledGluedRegister.opposite c) a,
          vector (companionTransport (ProtocolInventory.active c) v)) := by
  obtain ⟨k, hk⟩ := carrier_is_frame _ v
  dsimp only
  rw [companion_vector, hk]
  constructor
  · exact (CompanionHeavyFlip.ready_pack _ _ _ _ _).mpr ⟨rfl, rfl⟩
  · change CompanionHeavyFlip.run _ _ (CompanionHeavyFlip.pack 0 c a k) = _
    rw [CompanionHeavyFlip.run_pack]
    simp only [HeavyFlipControl.controlledFlip, Equiv.coe_fn_mk, HeavyFlipControl.direct_iff,
      and_self, ite_true, CompanionHeavyFlip.pack, ControlledGluedRegister.opposite_active]
    cases ProtocolInventory.active c <;>
      simp only [Bool.not_false, Bool.not_true, ite_true,
        ControlledGluedRegister.frame_succ, ControlledGluedRegister.wallClass] <;> rfl

/-- Coordinate action of the companion's physical class change in the
admitted endpoint model. -/
def advanceCoordinates (wall : Bool) (ψ : Fin 4 → ℂ) : Fin 4 → ℂ :=
  if wall then trialityMatrix *ᵥ ψ else trialityMatrix *ᵥ (trialityMatrix *ᵥ ψ)

theorem companion_transport_observed (wall : Bool) (ψ : Fin 4 → ℂ) :
    (CarrierParity.embedding (ControlledGluedRegister.wallClass 0 wall) *ᵥ
      advanceCoordinates wall ψ) ∘ companionTransport wall =
        CarrierParity.embedding (ControlledGluedRegister.wallClass 0 (!wall)) *ᵥ ψ := by
  cases wall
  · funext v
    exact (congrFun (triality_observed 0 (trialityMatrix *ᵥ ψ)) (carrierTriality 2 v)).trans
      (congrFun (triality_observed 2 ψ) v)
  · exact triality_observed 1 ψ

/-- Moving a written port with the existing companion update does not
in general prepare the balanced reader again. -/
theorem written_port_ready_iff (wall : Bool) (port : Fin 4) :
    advanceCoordinates wall (Pi.single port 1) = ElectricFourPortRecord.bank 1 1 ↔
      wall = true ∧ port = 0 := by
  constructor
  · intro h
    cases wall <;> fin_cases port
    all_goals
      first
      | exact ⟨rfl, rfl⟩
      | have h0 := congrFun h (0 : Fin 4)
        have h1 := congrFun h (1 : Fin 4)
        have h2 := congrFun h (2 : Fin 4)
        have h3 := congrFun h (3 : Fin 4)
        norm_num [advanceCoordinates, trialityMatrix, GluedRegister.M, mulVec, dotProduct,
          Fin.sum_univ_four, ElectricFourPortRecord.bank, Pi.single_apply] at *
  · rintro ⟨rfl, rfl⟩
    exact triality_balances_seed

end PMElementaryParticles.ElectricCompanionBank
