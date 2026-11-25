import PMElementaryParticles.ElectricChiralKick
import PMElementaryParticles.OccupiedBankedRestoring

/-!
# Registration account for the occupied direct writer and its renewal

The short word writes the charged-lepton's guard port. A reversible
renewal transports the companion bank back, then runs the decoder and
electric kicks in reverse. Prices here use one comparison per decoder pulse or completed
electric kick, with a supplied capacity per flag. The companion transport,
direct flip, and return of the payload to its next input have their own
admission and bookings.
-/

noncomputable section

namespace PMElementaryParticles.DirectWriterRenewal

open Matrix PMAction ElectricCoordinateDecoder ElectricFourPortRecord ElectricPrimitiveToll
open OccupiedBankedRestoring
open PMConstants.PacketGaugeActions

private def wordEnd {n : Type*} [Fintype n]
    (word : List (Matrix n n ℂ)) (input : n → ℂ) : n → ℂ :=
  word.foldl (fun v U => U *ᵥ v) input

private theorem word_end_product {n : Type*} [Fintype n] [DecidableEq n]
    (word : List (Matrix n n ℂ)) (v : n → ℂ) :
    wordEnd word v = word.reverse.prod *ᵥ v := by
  induction word generalizing v with
  | nil => simp [wordEnd]
  | cons U tail ih =>
    simpa only [wordEnd, List.foldl_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, Matrix.mulVec_mulVec] using ih (U *ᵥ v)

private theorem flags_append {n : Type*} [Fintype n] [DecidableEq n]
    (word tail : List (Matrix n n ℂ)) (v : n → ℂ) :
    flagLedger (word ++ tail) v = flagLedger word v + flagLedger tail (wordEnd word v) := by
  induction word generalizing v with
  | nil => simp [flagLedger, wordEnd]
  | cons U rest ih =>
    simp only [List.cons_append, flagLedger, ih, wordEnd, List.foldl_cons, add_assoc]

private theorem inverse_flag {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U ∈ unitary _) (v : n → ℂ) :
    CommonResponse.stateFlag Uᴴ (U *ᵥ v) = CommonResponse.stateFlag U v := by
  have hleft : Uᴴ * U = 1 := hU.1
  rw [CommonResponse.stateFlag, CommonResponse.stateFlag, mulVec_mulVec, hleft, one_mulVec]
  apply congrArg (· / 4)
  simp only [LinkExpansion.nsq_eq, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (U *ᵥ v) j - v j = -(v j - (U *ᵥ v) j) by ring, Complex.normSq_neg]

/-- The reverse-adjoint word restores the input and has the same state
flag sum when charged on that exact return path. -/
theorem reverse_flags {n : Type*} [Fintype n] [DecidableEq n]
    (word : List (Matrix n n ℂ)) (h : ∀ U ∈ word, U ∈ unitary _) (v : n → ℂ) :
    let undo := word.reverse.map Matrix.conjTranspose
    wordEnd undo (wordEnd word v) = v ∧
      flagLedger undo (wordEnd word v) = flagLedger word v := by
  induction word generalizing v with
  | nil => simp [flagLedger, wordEnd]
  | cons U tail ih =>
    have hU := h U (by simp)
    obtain ⟨hret, hflag⟩ := ih (fun A hA => h A (List.mem_cons_of_mem _ hA)) (U *ᵥ v)
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    change wordEnd (tail.reverse.map Matrix.conjTranspose ++ [Uᴴ]) (wordEnd tail (U *ᵥ v)) = v ∧
      flagLedger (tail.reverse.map Matrix.conjTranspose ++ [Uᴴ]) (wordEnd tail (U *ᵥ v)) =
        CommonResponse.stateFlag U v + flagLedger tail (U *ᵥ v)
    constructor
    · simp only [wordEnd, List.foldl_append] at hret ⊢
      rw [hret]
      have hleft : Uᴴ * U = 1 := hU.1
      simp [mulVec_mulVec, hleft]
    · rw [flags_append, hflag, hret]
      simp [flagLedger, inverse_flag U hU v, add_comm]

private def kicked (c : Channels) : Fin 4 → ℂ :=
  kick true (phase (3 * Real.pi) c) *ᵥ
    (kick false (phase (3 * Real.pi / 2) c) *ᵥ bank 1 1)

private theorem kicked_bank (c : Channels) :
    kicked c = bank (phase (3 * Real.pi / 2) c) (phase (3 * Real.pi / 2) c ^ 2) := by
  have hd := phase_double (3 * Real.pi / 2) c
  rw [show 2 * (3 * Real.pi / 2) = 3 * Real.pi by ring] at hd
  rw [kicked, kick_bank, hd]

private theorem static_electron : staticLepton = ProtocolToll.electronStatic := by decide +kernel

/-- The booked inverse decoder starts on the actual port 2 after the
companion has returned it. Its flag sum equals that of the forward decoder. -/
theorem charged_undo_decoder_flags (k : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    flagLedger (undoWord.reverse.map (runInstruction k p))
      (CarrierParity.embedding k *ᵥ Pi.single (2 : Fin 4) 1) = 9 / 4 := by
  let word := shortWord.reverse.map (runInstruction k p)
  let v := CarrierParity.embedding k *ᵥ kicked staticLepton
  have hu : ∀ U ∈ word, U ∈ unitary _ := by
    intro U hU
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hU
    exact RootTransferPhase.phase_unitary _ (PairedRootFlip.root_twice k i.1 i.2.1) _ _
  have hport : wordEnd word v = CarrierParity.embedding k *ᵥ Pi.single (2 : Fin 4) 1 := by
    rw [word_end_product]
    simp only [word, ← List.map_reverse, List.reverse_reverse, short_word_exact k p hp hp', v, kicked]
    have hread := short_reads k p hp hp' staticLepton
    change shortDecoder k p *ᵥ (CarrierParity.embedding k *ᵥ
      (kick true (phase (3 * Real.pi) staticLepton) *ᵥ
        (kick false (phase (3 * Real.pi / 2) staticLepton) *ᵥ bank 1 1))) = _ at hread
    exact hread
  have hret := (reverse_flags word hu v).2
  rw [hport, ← undo_execution k p hp hp'] at hret
  rw [hret]
  change flagLedger (shortWord.reverse.map (runInstruction k p))
    (CarrierParity.embedding k *ᵥ kicked staticLepton) = _
  rw [kicked_bank, decoder_carrier_flags k p hp hp']
  norm_num [address, staticLepton, HeavyFlipControl.labelRecord, ProtocolInventory.colourBulk,
    ControlledGluedRegister.labelIndex]

private theorem phase_star (t : ℝ) (c : Channels) :
    (starRingEnd ℂ) (phase t c) = phase (-t) c := by
  simp [phase, ← Complex.exp_conj, Complex.conj_I]

private theorem kick_unitary (high : Bool) (t : ℝ) (c : Channels) :
    kick high (phase t c) ∈ unitary _ := by
  have hmul : (starRingEnd ℂ) (phase t c) * phase t c = 1 :=
    by
      rw [phase_star, phase, phase, ← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      push_cast
      ring
  have hmul' : phase t c * (starRingEnd ℂ) (phase t c) = 1 := by rw [mul_comm, hmul]
  constructor <;> cases high <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [star_eq_conjTranspose, kick, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | exact hmul | exact hmul'

private theorem kick_adjoint (high : Bool) (t : ℝ) (c : Channels) :
    (kick high (phase t c))ᴴ = kick high (phase (-t) (ControlledGluedRegister.opposite c)) := by
  rw [phase_opposite]
  cases high <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kick, phase_star]

/-- The two inverse electric exposures start on the actual kicked bank
recovered by the inverse decoder. Opposite-wall phases implement those
adjoints, and their comparison sum is the forward exposure sum. -/
theorem charged_inverse_kick_flags :
    flagLedger
      [kick true (phase (-(3 * Real.pi)) (ControlledGluedRegister.opposite staticLepton)),
       kick false (phase (-(3 * Real.pi / 2)) (ControlledGluedRegister.opposite staticLepton))]
      (kicked staticLepton) = 3 / 4 := by
  let kicks := [kick false (phase (3 * Real.pi / 2) staticLepton),
    kick true (phase (3 * Real.pi) staticLepton)]
  have hu : ∀ U ∈ kicks, U ∈ unitary _ := by
    intro U hU
    simp only [kicks, List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with rfl | rfl <;> exact kick_unitary _ _ _
  have hrev := (reverse_flags kicks hu (bank 1 1)).2
  change flagLedger [(kick true (phase (3 * Real.pi) staticLepton))ᴴ,
      (kick false (phase (3 * Real.pi / 2) staticLepton))ᴴ] (kicked staticLepton) = _ at hrev
  rw [kick_adjoint, kick_adjoint] at hrev
  rw [hrev]
  change CommonResponse.stateFlag _ (bank 1 1) +
    (CommonResponse.stateFlag _ (kick false (phase (3 * Real.pi / 2) staticLepton) *ᵥ bank 1 1) + 0) = _
  rw [add_zero, exposure_eq_flags, static_electron]
  exact (exposure_tolls 0).1

/-- The shared-current realization reverses its intervening swap as
well as the two high-bit kicks. Its returned exposure has one flag. -/
theorem charged_inverse_shared_exposure_flags :
    flagLedger
      [kick true (phase (-(3 * Real.pi)) (ControlledGluedRegister.opposite staticLepton)),
       swapBits,
       kick true (phase (-(3 * Real.pi / 2)) (ControlledGluedRegister.opposite staticLepton))]
      (kicked staticLepton) = 1 := by
  let kicks := [kick true (phase (3 * Real.pi / 2) staticLepton), swapBits,
    kick true (phase (3 * Real.pi) staticLepton)]
  have swap_adjoint : swapBitsᴴ = swapBits := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [swapBits]
  have hswap : swapBits ∈ unitary _ := by
    have hh : swapBits * swapBits = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [swapBits, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
    have hl : swapBitsᴴ * swapBits = 1 := by rw [swap_adjoint, hh]
    have hr : swapBits * swapBitsᴴ = 1 := by rw [swap_adjoint, hh]
    exact ⟨hl, hr⟩
  have hu : ∀ U ∈ kicks, U ∈ unitary _ := by
    intro U hU
    simp only [kicks, List.mem_cons, List.not_mem_nil, or_false] at hU
    rcases hU with rfl | rfl | rfl
    · exact kick_unitary _ _ _
    · exact hswap
    · exact kick_unitary _ _ _
  have hpath : wordEnd kicks (bank 1 1) = kicked staticLepton :=
    ElectricChiralKick.two_kicks_from_one_current _ _
  have hrev := (reverse_flags kicks hu (bank 1 1)).2
  rw [hpath] at hrev
  change flagLedger [(kick true (phase (3 * Real.pi) staticLepton))ᴴ, swapBitsᴴ,
    (kick true (phase (3 * Real.pi / 2) staticLepton))ᴴ] (kicked staticLepton) = _ at hrev
  rw [kick_adjoint, swap_adjoint, kick_adjoint] at hrev
  rw [hrev]
  simp only [kicks, flagLedger, add_zero, ← add_assoc]
  rw [ElectricChiralKick.swapped_exposure_toll, static_electron, (exposure_tolls 0).1]
  have htotal := (ElectricChiralKick.total_tolls 0).1
  rw [ElectricChiralKick.totalToll, (ElectricPrimitiveToll.forward_tolls 0).1] at htotal
  linarith

/-- The shared-current writer and uncompute each use thirteen quarters
of a flag, including one intervening swap in each direction. -/
theorem shared_writer_flag_sum (k : Fin 3) (p : ℝ) (hp : 0 < p) (hp' : p < 1 / 2) :
    ElectricChiralKick.totalToll staticLepton +
      flagLedger (undoWord.reverse.map (runInstruction k p))
        (CarrierParity.embedding k *ᵥ Pi.single (2 : Fin 4) 1) +
      flagLedger
        [kick true (phase (-(3 * Real.pi)) (ControlledGluedRegister.opposite staticLepton)),
         swapBits,
         kick true (phase (-(3 * Real.pi / 2)) (ControlledGluedRegister.opposite staticLepton))]
        (kicked staticLepton) = 13 / 2 := by
  rw [charged_undo_decoder_flags k p hp hp', charged_inverse_shared_exposure_flags,
    static_electron, (ElectricChiralKick.total_tolls 0).1]
  norm_num

/-- Price the optional clean-seed preparation and one writer/uncompute
pair with their capacity values. The companion's transport and the
guarded flip have separate visit accounts. -/
def writerClaim (fresh : Bool) (prepareCapacity forwardCapacity renewalCapacity : ℝ) : ℝ :=
  CommonResponse.bookedCapacity Finset.univ
    (![prepareCapacity, forwardCapacity, renewalCapacity] : Fin 3 → ℝ)
    (![if fresh then 1 else 0, forwardToll staticLepton, 9 / 4 + 3 / 4] : Fin 3 → ℝ)

theorem writer_claim (fresh : Bool) (prepareCapacity forwardCapacity renewalCapacity : ℝ) :
    writerClaim fresh prepareCapacity forwardCapacity renewalCapacity =
      (if fresh then prepareCapacity else 0) + 3 * forwardCapacity + 3 * renewalCapacity := by
  have hforward : forwardToll staticLepton = 3 :=
    by rw [static_electron]; exact (ElectricPrimitiveToll.forward_tolls 0).1
  cases fresh <;>
    simp [writerClaim, CommonResponse.booked_capacity_eq, Fin.sum_univ_three, hforward] <;> ring

/-- With one capacity per flag, the balanced-bank writer and uncompute
claim six units. Preparing a fresh clean seed adds one unit. -/
theorem writer_claim_uniform (fresh : Bool) (capacity : ℝ) :
    writerClaim fresh capacity capacity capacity = (if fresh then 7 else 6) * capacity := by
  rw [writer_claim]
  cases fresh <;> simp <;> ring

/-- Decoder-only duration for the booked write and inverse, including
the optional fresh-seed preparation. -/
theorem writer_decoder_quarters (fresh : Bool) :
    (if fresh then (undoWord.map quarters).sum else 0) +
      (shortWord.map quarters).sum + (undoWord.map quarters).sum =
      if fresh then 79 else 52 := by
  cases fresh <;> simp [short_duration, undo_duration]

/-- Even the reusable-bank itinerary takes more than one frame at
positive whole ticks per root quarter, before the other visits. -/
theorem writer_decoder_exceeds_period (fresh : Bool) (q : ℕ) (hq : 0 < q) :
    Delta < ((if fresh then (undoWord.map quarters).sum else 0) +
      (shortWord.map quarters).sum + (undoWord.map quarters).sum) * q := by
  rw [writer_decoder_quarters]
  change 43 < (if fresh then 79 else 52) * q
  cases fresh <;> simp <;> omega

end PMElementaryParticles.DirectWriterRenewal
