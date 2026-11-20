import PMElementaryParticles.ElectricPrimitiveToll
import PMTransport.Interface

/-!
# Both electric kicks from one chiral register current

The same existing register current suffices for both controls. Its chiral
projector marks the high bit in either coordinate summand. A root swap
conjugates it to the low-bit projector. The bank is a separate carrier
register, and the charge is the packet's unbroken electric generator.
This specifies an occupation-conserving interaction in the register
model. Physical allocation, admission and clock calibration remain
requirements.
-/

noncomputable section
namespace PMElementaryParticles.ElectricChiralKick

open Matrix PMAction ConcreteFermion PMConstants.PacketGaugeActions
open ElectricHeavyRecord ElectricFourPortRecord
open scoped Kronecker Matrix.Norms.Operator

private instance : DecidableEq Channels := inferInstanceAs
  (DecidableEq (PMConstants.PacketGaugeActions.Q ⊕
    (PMConstants.PacketGaugeActions.Q ⊕ (Fin 2 ⊕ Fin 2))))
private instance : Fintype Channels := inferInstanceAs
  (Fintype (PMConstants.PacketGaugeActions.Q ⊕
    (PMConstants.PacketGaugeActions.Q ⊕ (Fin 2 ⊕ Fin 2))))

/-- The bank coordinate within either summand of the two-wall carrier. -/
def port : Sites → Fin 4 := Sum.elim id id

def onHigh (j : Fin 4) : Bool := decide (2 ≤ j.val)
def onLow (j : Fin 4) : Bool := decide (j.val % 2 = 1)

def packetQ : Matrix Channels Channels ℂ := diagonal fun c => (q c : ℂ)

open PMConstants.GeneratorNormalization PMConstants.PacketTraceForm in
theorem packetQ_eq : packetQ = t3 + hyperGen := electric_generator.symm

theorem packetQ_hermitian : packetQ.IsHermitian := by
  rw [packetQ, Matrix.isHermitian_diagonal_iff]
  intro i
  change star (q i : ℂ) = (q i : ℂ)
  simp

/-- The existing full chiral projector has the same high-bit mask on
both coordinate summands. This concerns a record bank; on a live
zero mode the projector instead reads its wall. -/
theorem projector_high :
    WallChiralCurrent.projector =
      diagonal (fun i : Sites => if onHigh (port i) then (1 : ℂ) else 0) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [WallChiralCurrent.projector, WallChiralCurrent.chirality, onHigh, port,
      ConcreteFermion.gamma, Matrix.one_apply, Matrix.diagonal_apply]

def electricCurrent (c : Fin 3) :=
  RegisterInteraction.current c packetQ

def highPulse (c : Fin 3) (t : ℝ) :=
  NormedSpace.exp ((((t : ℝ) : ℂ) * Complex.I) • electricCurrent c)

def kickOn (select : Fin 4 → Bool) (t : ℝ) : Matrix (Sites × Channels) (Sites × Channels) ℂ :=
  diagonal (fun i => if select (port i.1) then phase t i.2 else 1)

/-- The packet charge under the existing chiral current gives exactly
the high-bit kick on the occupied modes. -/
theorem high_observed (c : Fin 3) (t : ℝ) :
    NativeObservation.Obs (RegisterVacuum.embedding c) (highPulse c t) (kickOn onHigh t) := by
  have h := NativeObservation.exp (RegisterInteraction.current_observed c packetQ packetQ_hermitian)
    ((t : ℂ) * Complex.I)
  have hgen : WallChiralCurrent.projector ⊗ₖ packetQ =
      diagonal fun i : Sites × Channels => if onHigh (port i.1) then (q i.2 : ℂ) else 0 := by
    rw [projector_high, packetQ, diagonal_kronecker_diagonal]
    congr 1
    ext ⟨i, a⟩
    by_cases hm : onHigh (port i) <;> simp [hm]
  rw [hgen, ← Matrix.diagonal_smul, Matrix.exp_diagonal] at h
  have heq :
      Matrix.diagonal (NormedSpace.exp (((t : ℂ) * Complex.I) •
        (fun i : Sites × Channels => if onHigh (port i.1) then (q i.2 : ℂ) else 0))) =
        kickOn onHigh t := by
    unfold kickOn
    congr 1
    ext ⟨i, a⟩
    rw [Pi.coe_exp]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hm : onHigh (port i)
    · simp only [hm, ite_true, phase, Complex.ofReal_mul, ← Complex.exp_eq_exp_ℂ]
      congr 1
      ring
    · simp [hm]
  rw [← heq]
  exact h

/-- The same root swap is applied to both banks of the carrier. -/
def coordinateSwap (c : Fin 3) : Equiv.Perm (RegisterVacuum.Labels c) :=
  Equiv.Perm.sumCongr (PairedRootFlip.rootEvent c 2 2) (PairedRootFlip.rootEvent c 2 2)

def swapSite : Equiv.Perm Sites :=
  Equiv.Perm.sumCongr (Equiv.swap (1 : Fin 4) 2) (Equiv.swap 1 2)

def swapUpdate (c : Fin 3) :=
  (IndependentRegisters.update (coordinateSwap c) (Equiv.refl Channels)).permMatrix ℂ

private theorem swap_bank_coordinate :
    fromBlocks swapBits 0 0 swapBits = swapSite.permMatrix ℂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    norm_num [swapBits, swapSite, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.swap_apply_def]

theorem swap_observed (c : Fin 3) :
    NativeObservation.Obs (RegisterVacuum.embedding c) (swapUpdate c)
      (swapSite.permMatrix ℂ ⊗ₖ (1 : Matrix Channels Channels ℂ)) := by
  apply NativeObservation.compose (IndependentRegisters.tensor_observed (coordinateSwap c)
    (Equiv.refl Channels))
  apply NativeObservation.tensor _ (by simpa using
    (NativeObservation.one : NativeObservation.Obs (1 : Matrix Channels Channels ℂ) 1 1))
  rw [← swap_bank_coordinate, ← ElectricCoordinateDecoder.swap_coordinate]
  have h := PairedRootFlip.root_observed c 2 2
  have hs : (coordinateSwap c).permMatrix ℂ =
      fromBlocks ((PairedRootFlip.rootEvent c 2 2).permMatrix ℂ) 0 0
        ((PairedRootFlip.rootEvent c 2 2).permMatrix ℂ) := by
    ext i j
    cases i <;> cases j <;>
      simp [coordinateSwap, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [hs]
  exact NativeObservation.blocks h NativeObservation.zero NativeObservation.zero h

/-- Conjugate the one current by the root swap to mark the low bit. -/
def lowPulse (c : Fin 3) (t : ℝ) :=
  swapUpdate c * highPulse c t * swapUpdate c

private theorem port_mask_swap (i : Sites) :
    onHigh (port (swapSite i)) = onLow (port i) := by
  rcases i with i | i <;> fin_cases i <;> decide +kernel

private theorem swap_twice : Function.Involutive swapSite := by
  rintro (i | i) <;> simp [swapSite]

theorem low_observed (c : Fin 3) (t : ℝ) :
    NativeObservation.Obs (RegisterVacuum.embedding c) (lowPulse c t) (kickOn onLow t) := by
  have h := NativeObservation.mul (NativeObservation.mul (swap_observed c) (high_observed c t))
    (swap_observed c)
  let e : Equiv.Perm (Sites × Channels) := Equiv.prodCongr swapSite (Equiv.refl Channels)
  have hs : swapSite.permMatrix ℂ ⊗ₖ (1 : Matrix Channels Channels ℂ) =
      e.permMatrix ℂ := by
    simpa [e] using (IndependentRegisters.tensor_permutation swapSite (Equiv.refl Channels)).symm
  rw [hs] at h
  have he : Function.Involutive e := by
    rintro ⟨i, a⟩
    exact Prod.ext (swap_twice i) rfl
  have hdiag : e.permMatrix ℂ * kickOn onHigh t * e.permMatrix ℂ = kickOn onLow t := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [kickOn, Matrix.mul_diagonal, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [Finset.sum_eq_single (e i)]
    · by_cases hij : i = j
      · subst j
        rcases i with ⟨u, a⟩
        simp [e, swap_twice u, port_mask_swap]
      · simp [he i, hij]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  rw [hdiag] at h
  exact h

theorem high_unitary (c : Fin 3) (t : ℝ) : highPulse c t ∈ unitary _ := by
  have h := RegisterInteraction.current_unitary c packetQ (-t)
  simpa [highPulse, electricCurrent, Complex.ofReal_neg, mul_comm] using h

theorem high_preserves_occupation (c : Fin 3) (t : ℝ) :
    let N := diagonal (fun r : RegisterVacuum.Config (b := Channels) c =>
      (IndependentRegisters.occupied r : ℂ))
    highPulse c t * N = N * highPulse c t :=
  RegisterInteraction.evolution_occupation (RegisterVacuum.nativeProjector c) packetQ _

theorem low_unitary (c : Fin 3) (t : ℝ) : lowPulse c t ∈ unitary _ :=
  mul_mem (mul_mem (CarrierResponse.perm_unitary _) (high_unitary c t))
    (CarrierResponse.perm_unitary _)

/-- The executed pair of pulses uses one current and one intervening
swap if the input is the already-balanced bank. -/
theorem pair_observed (c : Fin 3) (t u : ℝ) :
    NativeObservation.Obs (RegisterVacuum.embedding c)
      (highPulse c u * (swapUpdate c * highPulse c t))
      (kickOn onHigh u * ((swapSite.permMatrix ℂ ⊗ₖ (1 : Matrix Channels Channels ℂ)) *
        kickOn onHigh t)) :=
  NativeObservation.mul (high_observed c u) (NativeObservation.mul (swap_observed c)
    (high_observed c t))

/-- Each bank summand carries the same four-port kick at a fixed
payload, with no transition to the other summand or payload. -/
theorem kick_on_summand (high wall : Bool) (t : ℝ) (a : Channels) (i j : Fin 4) :
    let place : Fin 4 → Sites := if wall then Sum.inr else Sum.inl
    kickOn (if high then onHigh else onLow) t (place i, a) (place j, a) =
      kick high (phase t a) i j := by
  cases high <;> cases wall <;> fin_cases i <;> fin_cases j <;>
    simp [kickOn, onHigh, onLow, port, kick]

/-- The first coordinate is a rest seed on the first carrier wall. -/
theorem clean_first_seed_at_rest :
    ConcreteFermion.hamiltonian 0 0 *ᵥ
        Sum.elim (Pi.single (0 : Fin 4) (1 : ℂ)) (fun _ => 0) = 0 := by
  rw [ConcreteFermion.kernel_coordinates]
  simp

/-- A balanced four-port bank on one summand uses gapped coordinates.
The live rest wire on that wall cannot serve as this prepared bank. -/
theorem balanced_bank_leaves_rest (wall : Bool) :
    ConcreteFermion.hamiltonian 0 0 *ᵥ
      (if wall then Sum.elim (fun _ => 0) (bank 1 1)
        else Sum.elim (bank 1 1) (fun _ => 0)) ≠ 0 := by
  intro h
  have hz := (ConcreteFermion.kernel_coordinates _).mp h
  cases wall
  · have hc := hz.1
    norm_num [bank] at hc
  · have hc := hz.2.2.1
    norm_num [bank] at hc

/-! ### Executing and charging the swapped current on a balanced bank -/

private theorem swap_bank (x y : ℂ) : swapBits *ᵥ bank x y = bank y x := by
  ext i
  fin_cases i <;>
        norm_num [swapBits, bank, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]

private theorem high_seed (z : ℂ) : kick true z *ᵥ bank 1 1 = bank 1 z := by
  ext i
  rw [kick, Matrix.mulVec_diagonal]
  fin_cases i <;> simp [bank, div_eq_mul_inv]

private theorem low_seed (z : ℂ) : kick false z *ᵥ bank 1 1 = bank z 1 := by
  ext i
  rw [kick, Matrix.mulVec_diagonal]
  fin_cases i <;> simp [bank, div_eq_mul_inv]

/-- A balanced seed absorbs the incoming swap exactly. The one remaining
swap realizes the low kick, so the short decoder receives its usual input. -/
theorem two_kicks_from_one_current (x y : ℂ) :
    kick true y *ᵥ (swapBits *ᵥ (kick true x *ᵥ bank 1 1)) =
      kick true y *ᵥ (kick false x *ᵥ bank 1 1) := by
  rw [high_seed, swap_bank, low_seed]

theorem bank_swap_flag (x y : ℂ) :
    CommonResponse.stateFlag swapBits (bank x y) = Complex.normSq (x - y) / 8 := by
  rw [CommonResponse.stateFlag, swap_bank]
  have h : bank x y - bank y x = ![0, (x - y) / 2, -(x - y) / 2, 0] := by
    ext i
    fin_cases i <;> simp [bank] <;> ring
  rw [h, LinkExpansion.nsq_eq, Fin.sum_univ_four]
  norm_num [Complex.normSq_div]
  have hn : Complex.normSq (y - x) = Complex.normSq (x - y) := by
    rw [show y - x = -(x - y) by ring, Complex.normSq_neg]
  rw [hn]
  ring

private theorem first_flag (z : ℂ) :
    CommonResponse.stateFlag (kick true z) (bank 1 1) =
      CommonResponse.stateFlag (kick false z) (bank 1 1) := by
  rw [CommonResponse.stateFlag, CommonResponse.stateFlag, high_seed, low_seed]
  have h₁ : bank 1 1 - bank 1 z = ![0, 0, (1 - z) / 2, (1 - z) / 2] := by
    ext i; fin_cases i <;> simp [bank] <;> ring
  have h₂ : bank 1 1 - bank z 1 = ![0, (1 - z) / 2, 0, (1 - z) / 2] := by
    ext i; fin_cases i <;> simp [bank] <;> ring
  rw [h₁, h₂]
  simp [LinkExpansion.nsq_eq, Fin.sum_univ_four]

/-- The extra physical swap between the two current pulses has an exact
state flag. This prices the shared-current realization, in addition to
the earlier direct-mask exposure ledger. -/
def swapToll (label : Channels) : ℝ :=
  DiagonalReadout.flag (3 * Real.pi / 2 * q label) / 2

theorem swapped_exposure_toll (label : Channels) :
    let x := phase (3 * Real.pi / 2) label
    let y := phase (3 * Real.pi) label
    CommonResponse.stateFlag (kick true x) (bank 1 1) +
      CommonResponse.stateFlag swapBits (kick true x *ᵥ bank 1 1) +
      CommonResponse.stateFlag (kick true y) (swapBits *ᵥ (kick true x *ᵥ bank 1 1)) =
        exposureToll label + swapToll label := by
  dsimp only
  rw [first_flag, high_seed, swap_bank, bank_swap_flag]
  have he := exposure_eq_flags label
  rw [low_seed] at he
  rw [← he, swapToll, phase, DiagonalReadout.normSq_one_sub_exp]
  ring

/-- The forward record event using the single chiral-current interaction,
its intervening swap, and the short decoder at bit-reversed ports. -/
def totalToll (label : Channels) : ℝ :=
  ElectricPrimitiveToll.forwardToll label + swapToll label

/-- The electric generator supplies identical phase histories to both
packet wall slots. Their equal-superposition flag ledger has that same price. -/
theorem total_toll_wall_pair (label : Channels) :
    totalToll (ControlledGluedRegister.opposite label) = totalToll label := by
  simp only [totalToll, ElectricPrimitiveToll.forwardToll, exposureToll, swapToll,
    phase_opposite, (ElectricHeavyRecord.same_wall_pair label).1]

open ProtocolToll in
theorem total_tolls (a : Fin 3) :
    totalToll electronStatic = 13 / 4 ∧ totalToll (downStatic a) = 11 / 4 ∧
      totalToll (upStatic a) = 5 / 2 ∧ totalToll neutrinoStatic = 1 := by
  obtain ⟨he, hd, hu, hn⟩ := HeavyFlipControl.static_record_codes a
  obtain ⟨te, td, tu, tn⟩ := ElectricPrimitiveToll.forward_tolls a
  change HeavyFlipControl.labelRecord electronStatic = (true, true) at he
  change HeavyFlipControl.labelRecord (downStatic a) = (false, true) at hd
  change HeavyFlipControl.labelRecord (upStatic a) = (false, false) at hu
  change HeavyFlipControl.labelRecord neutrinoStatic = (true, false) at hn
  have hs (label : Channels) : swapToll label =
      (1 - (phase (3 * Real.pi / 2) label).re) / 4 := by
    rw [phase, Complex.exp_ofReal_mul_I_re, swapToll, DiagonalReadout.flag]
    ring
  simp only [totalToll, hs, te, td, tu, tn, phase_codes, address, he, hd, hu, hn,
    Bool.false_eq_true, ite_true, ite_false]
  change (3 : ℝ) + (1 - Complex.I.re) / 4 = 13 / 4 ∧
    5 / 2 + (1 - (-Complex.I).re) / 4 = 11 / 4 ∧
    2 + (1 - (-1 : ℂ).re) / 4 = 5 / 2 ∧
    1 + (1 - (1 : ℂ).re) / 4 = 1
  norm_num

open ProtocolToll in
/-- The extra swap changes the two gaps to one half and one quarter. -/
theorem total_ladder (a : Fin 3) :
    TollAmplitude.wireAmplitude (totalToll electronStatic) <
        TollAmplitude.wireAmplitude (totalToll (downStatic a)) ∧
      TollAmplitude.wireAmplitude (totalToll (downStatic a)) <
        TollAmplitude.wireAmplitude (totalToll (upStatic a)) := by
  obtain ⟨he, hd, hu, -⟩ := total_tolls a
  rw [TollAmplitude.wireAmplitude_lt_iff, TollAmplitude.wireAmplitude_lt_iff, he, hd, hu]
  norm_num

end PMElementaryParticles.ElectricChiralKick
