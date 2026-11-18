import PMElementaryParticles.CompanionHeavyFlip
import PMElementaryParticles.ElectricChiralKick

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

private def transportedBox {c : Fin 3} (v : Carrier c) : Box :=
  fun i => ⟨((GluedRegister.triality (vector v) i + 2).toNat) % 5, Nat.mod_lt _ (by decide)⟩

private theorem transported_valid : ∀ (c : Fin 3) (v : Carrier c),
    valid (c + 1) (transportedBox v) := by
  decide +kernel

private def nextCarrier (c : Fin 3) (v : Carrier c) : Carrier (c + 1) :=
  ⟨transportedBox v, transported_valid c v⟩

private theorem next_vector : ∀ (c : Fin 3) (v : Carrier c) (i : Fin 4),
    vector (nextCarrier c v) i = GluedRegister.triality (vector v) i := by
  decide +kernel

private theorem next_bijective : ∀ (c : Fin 3), Function.Bijective (nextCarrier c) := by
  decide +kernel

def carrierTriality (c : Fin 3) : Carrier c ≃ Carrier (c + 1) :=
  Equiv.ofBijective (nextCarrier c) (next_bijective c)

/-- Triality on the odd coordinate amplitudes, in the current's coordinate frame. -/
def trialityMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => (GluedRegister.M i j : ℂ) / 2

theorem triality_unitary : trialityMatrix ∈ unitary _ := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [trialityMatrix, GluedRegister.M, star_eq_conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

private theorem twice_triality : trialityMatrix * (trialityMatrix * trialityMatrix) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [trialityMatrix, GluedRegister.M, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

private theorem doubled_vector : ∀ (c : Fin 3) (v : Carrier c) (i : Fin 4),
    2 * vector (nextCarrier c v) i = ∑ j, GluedRegister.M i j * vector v j := by
  decide +kernel

private theorem moved_embedding (c : Fin 3) :
    (CarrierParity.embedding (c + 1)).submatrix (carrierTriality c) id =
      CarrierParity.embedding c * trialityMatrixᴴ := by
  ext v i
  change CarrierParity.scale * (vector (nextCarrier c v) i : ℂ) = _
  have h := congrArg (fun z : ℤ => (z : ℂ)) (doubled_vector c v i)
  push_cast at h
  rw [Matrix.mul_apply]
  change _ = ∑ j : Fin 4, (CarrierParity.scale * (vector v j : ℂ)) *
    star ((GluedRegister.M i j : ℂ) / 2)
  have hs (z : ℤ) : star ((z : ℂ) / 2) = (z : ℂ) / 2 := by
    rw [Complex.star_def]
    simp [map_ofNat]
  simp_rw [hs]
  simp_rw [show ∀ j : Fin 4,
      CarrierParity.scale * (vector v j : ℂ) * ((GluedRegister.M i j : ℂ) / 2) =
      (CarrierParity.scale / 2) * ((GluedRegister.M i j : ℂ) * (vector v j : ℂ)) by
    intro j
    ring]
  rw [← Finset.mul_sum, ← h]
  ring

/-- Relabeling actual carrier amplitudes by triality moves their odd coordinates
by the same matrix. This preserves the full four-port state. -/
theorem triality_observed (c : Fin 3) (ψ : Fin 4 → ℂ) :
    (CarrierParity.embedding (c + 1) *ᵥ (trialityMatrix *ᵥ ψ)) ∘ carrierTriality c =
      CarrierParity.embedding c *ᵥ ψ := by
  have h : trialityMatrixᴴ * trialityMatrix = 1 := triality_unitary.1
  change (CarrierParity.embedding (c + 1)).submatrix (carrierTriality c) id *ᵥ
    (trialityMatrix *ᵥ ψ) = _
  rw [moved_embedding, Matrix.mulVec_mulVec, Matrix.mul_assoc, h, Matrix.mul_one]

def seed : Fin 4 → ℂ := Pi.single 0 1

theorem triality_balances_seed : trialityMatrix *ᵥ seed = ElectricFourPortRecord.bank 1 1 := by
  ext i
  fin_cases i <;> norm_num [trialityMatrix, GluedRegister.M, seed, ElectricFourPortRecord.bank]

theorem triality_returns_seed :
    trialityMatrix *ᵥ (trialityMatrix *ᵥ ElectricFourPortRecord.bank 1 1) = seed := by
  rw [← triality_balances_seed, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, twice_triality, Matrix.one_mulVec]

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

/-- A single logical carrier occupying the diagonal of the glued root bank.
Its two equal coordinates specify one root label. -/
def diagonalRoot {c : Fin 3} (v : Carrier c) : GluedRegister.Wt × GluedRegister.Wt :=
  (vector v, vector v)

private theorem carrier_is_glued : ∀ (x : Fin 3) (v : Carrier x),
    ∃ a : Fin 8, vector v = GluedRegister.carrier x a := by
  decide +kernel

/-- On the diagonal, the actual six-root crossing sends both halves to
the same new carrier. This implements the triality permutation on the
diagonal sector, including its linear action on an occupied odd seed. -/
theorem glued_triality_step (c : Fin 3) (v : Carrier c) :
    GluedRegister.runCrossing (diagonalRoot v) = diagonalRoot (carrierTriality c v) := by
  obtain ⟨a, ha⟩ := carrier_is_glued c v
  change GluedRegister.runCrossing (vector v, vector v) =
    (vector (nextCarrier c v), vector (nextCarrier c v))
  have hv : vector (nextCarrier c v) = GluedRegister.triality (vector v) := by
    funext i
    exact next_vector c v i
  rw [hv, ha, GluedRegister.crossing_word_glued]
  rfl

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
  · change vector (nextCarrier 0 (nextCarrier 2 v)) = _
    funext i
    rw [next_vector 0]
    congr 2
    funext j
    exact next_vector 2 v j
  · funext i
    exact next_vector 1 v i

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
