import PersistenceMechanics.InformationTransfer
import PMFlavor.BreakingPhase
import PMFlavor.MixingMatrix
import PMFlavor.CKM
import PMFlavor.PMNS

/-! **Experimental/candidate module.**

# Flavor as information transfer

CKM is boundary conduction, PMNS is capacity promotion, and the broken link is a
coordinate jump.  The mixing overlap is the transfer amplitude ledger.
-/

noncomputable section
namespace PMFlavor.TransferFlavor

open PersistenceMechanics.InformationTransfer
open PMFlavor.BreakingWall

/-- CKM transfer channel: adjacent, interface-limited. -/
def ckmTransfer (phase cost capacityRequired margin : ℝ) : TransferChannel :=
  { mode := .boundaryConduction
    phase := phase
    cost := cost
    capacityRequired := capacityRequired
    margin := margin }

/-- PMNS transfer channel: capacity promotion. -/
def pmnsTransfer (phase cost capacityRequired margin : ℝ) : TransferChannel :=
  { mode := .capacityPromotion
    phase := phase
    cost := cost
    capacityRequired := capacityRequired
    margin := margin }

/-- Broken-link transfer: non-adjacent coordinate jump. -/
def brokenLinkTransfer (w : BreakingPhase) : TransferChannel :=
  { mode := .coordinateJump
    phase := w.delta
    cost := w.epsilon
    capacityRequired := 1
    margin := 1 }

theorem ckmTransfer_mode (phase cost cap margin : ℝ) :
    (ckmTransfer phase cost cap margin).mode = .boundaryConduction := rfl

theorem pmnsTransfer_mode (phase cost cap margin : ℝ) :
    (pmnsTransfer phase cost cap margin).mode = .capacityPromotion := rfl

theorem brokenLinkTransfer_mode (w : BreakingPhase) :
    (brokenLinkTransfer w).mode = .coordinateJump := rfl

theorem pmnsTransfer_expands (phase cost cap margin : ℝ) :
    (pmnsTransfer phase cost cap margin).mode.expandsCapacity = true := rfl

theorem brokenLinkTransfer_not_adjacent (w : BreakingPhase) :
    (brokenLinkTransfer w).mode.adjacent = false := rfl

/-- Mixing overlap amplitude in the protected-state sector. -/
def mixingOverlapAmplitude (ε : ℝ) : ℂ :=
  PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti
    (![1, (PMFlavor.MixingMatrix.rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ)

theorem mixingOverlapAmplitude_eq (ε : ℝ) :
    mixingOverlapAmplitude ε =
      PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti
        (![1, (PMFlavor.MixingMatrix.rootM ε : ℂ) - 3, 1] : Fin 3 → ℂ) := rfl

/-- CKM transfer capacity: the active channel count `ν`. -/
def ckmCapacity : ℝ := (PMSubstrate.E8Values.nu : ℝ)

/-- PMNS transfer capacity: the active basin `ν + σ`. -/
def pmnsCapacity : ℝ :=
  ((PMSubstrate.E8Values.nu + PMSubstrate.E8Values.sigma : Nat) : ℝ)

theorem ckmCapacity_eq : ckmCapacity = 16 := by
  unfold ckmCapacity
  norm_num [PMSubstrate.E8Values.nu, PMSubstrate.baseline]

theorem pmnsCapacity_eq : pmnsCapacity = 21 := by
  unfold pmnsCapacity
  norm_num [PMSubstrate.E8Values.nu, PMSubstrate.E8Values.sigma, PMSubstrate.baseline]

/-- The PMNS/CKM capacity ratio. -/
def capacityRatio : ℝ := pmnsCapacity / ckmCapacity

theorem capacityRatio_eq : capacityRatio = 21 / 16 := by
  unfold capacityRatio
  rw [pmnsCapacity_eq, ckmCapacity_eq]

/-- Quark and neutrino transfer modes are distinct. -/
theorem ckm_pmns_modes_distinct :
    (ckmTransfer 0 0 1 1).mode ≠ (pmnsTransfer 0 0 1 1).mode := by
  decide

/-- The protected-state overlap is the explicit `rootM − 4` amplitude. -/
theorem mixingOverlapAmplitude_eq_rootM (ε : ℝ) :
    mixingOverlapAmplitude ε = ((PMFlavor.MixingMatrix.rootM ε : ℂ) - 4) := by
  unfold mixingOverlapAmplitude
  rw [PMFlavor.MixingMatrix.ip_anti_M]

/-- Normalize a complex overlap into a unit-modulus transfer entry. -/
noncomputable def normalizedOverlap (z : ℂ) : ℂ :=
  z / (Real.sqrt (Complex.normSq z) : ℂ)

theorem normalizedOverlap_normSq (z : ℂ) (h : z ≠ 0) :
    Complex.normSq (normalizedOverlap z) = 1 := by
  unfold normalizedOverlap
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  have hz : Complex.normSq z ≠ 0 := by
    intro hz
    exact h (Complex.normSq_eq_zero.mp hz)
  rw [Real.mul_self_sqrt (Complex.normSq_nonneg z)]
  field_simp [hz]

/-- Transfer impedance from the E8 capacity ratio. -/
def transferImpedance : ℝ := ckmCapacity / pmnsCapacity

theorem transferImpedance_eq : transferImpedance = 16 / 21 := by
  unfold transferImpedance
  rw [ckmCapacity_eq, pmnsCapacity_eq]

theorem ckmCapacity_lt_pmns : ckmCapacity < pmnsCapacity := by
  rw [ckmCapacity_eq, pmnsCapacity_eq]; norm_num

/-- Flavor sector label. -/
inductive FlavorSector
  | ckm | pmns
  deriving DecidableEq, Repr

/-- Raw sector entry. -/
noncomputable def sectorEntry (s : FlavorSector) (i j : Fin 3) : ℂ :=
  match s with
  | .ckm => PMFlavor.CKM.ckm PMFlavor.CKM.c12 PMFlavor.CKM.s12
      PMFlavor.CKM.c23 PMFlavor.CKM.s23 PMFlavor.CKM.c13 PMFlavor.CKM.s13
      (Complex.exp ((PMFlavor.CKM.δ : ℂ) * Complex.I)) i j
  | .pmns => PMFlavor.PMNS.matrix i j

/-- Normalized transfer entry for a labeled sector. -/
noncomputable def normalizedSectorEntry (s : FlavorSector) (i j : Fin 3) : ℂ :=
  normalizedOverlap (sectorEntry s i j)

theorem normalizedSectorEntry_eq (s : FlavorSector) (i j : Fin 3) :
    normalizedSectorEntry s i j = normalizedOverlap (sectorEntry s i j) := rfl

/-- Wall-dispersion impedance from a two-branch spectrum. -/
def wallImpedance (e : Fin 3 → ℝ) : ℝ := Real.sqrt (e 2 / e 0)

/-- If the wall dispersion gives the E8 capacity ratio, the transfer impedance is
the wall impedance. -/
theorem transferImpedance_eq_wall (e : Fin 3 → ℝ)
    (h : wallImpedance e = 16 / 21) :
    transferImpedance = wallImpedance e := by
  rw [transferImpedance_eq, h]

/-- CKM share of the combined transfer capacity. -/
def ckmCapacityFraction : ℝ := ckmCapacity / (ckmCapacity + pmnsCapacity)

/-- PMNS share of the combined transfer capacity. -/
def pmnsCapacityFraction : ℝ := pmnsCapacity / (ckmCapacity + pmnsCapacity)

theorem ckmCapacityFraction_eq : ckmCapacityFraction = 16 / 37 := by
  unfold ckmCapacityFraction
  rw [ckmCapacity_eq, pmnsCapacity_eq]
  norm_num

theorem pmnsCapacityFraction_eq : pmnsCapacityFraction = 21 / 37 := by
  unfold pmnsCapacityFraction
  rw [ckmCapacity_eq, pmnsCapacity_eq]
  norm_num

theorem ckm_fraction_lt_half : ckmCapacityFraction < 1 / 2 := by
  rw [ckmCapacityFraction_eq]; norm_num

theorem pmns_fraction_gt_half : 1 / 2 < pmnsCapacityFraction := by
  rw [pmnsCapacityFraction_eq]; norm_num

/-- Full mixing entries depend on `δ`; the protected-state overlap does not. -/
theorem fullMixing_delta_dependence :
    PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootP 0 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (PMFlavor.MixingMatrix.rootP 0 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠
      PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootP 2 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (PMFlavor.MixingMatrix.rootP 0 : ℂ) - 3, 1] : Fin 3 → ℂ) := by
  rw [PMFlavor.MixingMatrix.ip_P_P, PMFlavor.MixingMatrix.ip_P_P,
    PMFlavor.MixingMatrix.rootP_zero, PMFlavor.MixingMatrix.rootP_two]
  norm_num

/-- Unit-toll wall anchor: one unit of phase mismatch and one unit of cost. -/
def unitWall : BreakingPhase := ⟨1, 1⟩

theorem unitWall_physical : PhysicalWall unitWall := by
  unfold PhysicalWall unitWall
  norm_num

theorem unitWall_off_exceptional : PhysicalWallInput unitWall :=
  physicalWall_off_exceptional unitWall_physical

/-- At the unit-toll anchor every full mixing entry is nonzero. -/
theorem unitWall_all_nonzero :
    (PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti PMFlavor.MixingMatrix.antiB ≠ 0 ∧
      PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti
        (![1, (PMFlavor.MixingMatrix.rootP 1 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      PMFlavor.MixingMatrix.ip PMFlavor.GenerationBreaking.anti
        (![1, (PMFlavor.MixingMatrix.rootM 1 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0) ∧
    (PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootP 1 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        PMFlavor.MixingMatrix.antiB ≠ 0 ∧
      PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootM 1 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        PMFlavor.MixingMatrix.antiB ≠ 0) ∧
    (PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootP 1 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (PMFlavor.MixingMatrix.rootP 1 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootP 1 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (PMFlavor.MixingMatrix.rootM 1 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootM 1 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (PMFlavor.MixingMatrix.rootP 1 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0 ∧
      PMFlavor.MixingMatrix.ip
        (![(PMFlavor.MixingMatrix.rootM 1 : ℂ) - 3, 1, 1] : Fin 3 → ℂ)
        (![1, (PMFlavor.MixingMatrix.rootM 1 : ℂ) - 3, 1] : Fin 3 → ℂ) ≠ 0) :=
  PMFlavor.MixingMatrix.all_nonzero_mixing_interval 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end PMFlavor.TransferFlavor
