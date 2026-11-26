import PMElementaryParticles.VacancyProjection
import PMElementaryParticles.ResonanceLift
import PMAction.CoherentComparisonRepair
import PMAction.OtherWallFlipEvent
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Charge and generation selectors for a static-wall insertion

On the static bank the existing packet hypercharge transport at `3π/4`
has eigenvalues `1, i, -1, -i` for vacancy, electron, up and down.
Two phase-matched coherent comparisons isolate any one of these sectors
with unit retained amplitude. The vector glue class selects one static
generation leg. The resulting selector can localize a supplied coherent
flip; admission of the joint control and the common detuning and pulse
areas are dynamical inputs.
-/

noncomputable section
namespace PMElementaryParticles.ChargedInsertion
open Matrix PMConstants.PacketGaugeActions PMConstants.ChannelOccupancy
open ProtocolInventory ControlledGluedRegister PMAction.CoherentComparisonRepair
open scoped Matrix.Norms.Operator

/-- Possible static-wall slots, encoded by their quarter-turn eigenphase. -/
def phaseIndex : Option BaseProtocol → Fin 4
  | none | some .neutrino => 0
  | some .electron => 1
  | some .up => 2
  | some .down => 3

private theorem phaseIndex_inj (c : Channels) (s : Option BaseProtocol)
    (hc : active c = false) (hs : s ≠ some .neutrino) :
    phaseIndex (baseProtocol c) = phaseIndex s ↔ baseProtocol c = s := by
  revert c s
  decide +kernel

private theorem transport_diagonal :
    hypercharge (3 * Real.pi / 4) = diagonal
      (fun c => Complex.exp (((Real.pi : ℂ) * (hyperchargeThirds c : ℂ) / 4) * Complex.I)) := by
  rw [VacancyProjection.hypercharge_eq_diagonal]
  congr 1
  funext c
  congr 1
  push_cast
  ring

private theorem static_phase (c : Channels) (hc : active c = false) :
    Complex.exp (((Real.pi : ℂ) * (hyperchargeThirds c : ℂ) / 4) * Complex.I) =
      Complex.I ^ (phaseIndex (baseProtocol c)).val := by
  have hi : Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) = Complex.I :=
    Complex.exp_pi_div_two_mul_I
  rcases c with ⟨a, s⟩ | ⟨a, s⟩ | s | s
  · simp [active] at hc
  · fin_cases s
    · norm_num [hyperchargeThirds_apply, baseProtocol, phaseIndex, Complex.exp_pi_mul_I, Complex.I_sq]
    · norm_num [hyperchargeThirds_apply, baseProtocol, phaseIndex]
      rw [show -((Real.pi : ℂ) * 2) / 4 * Complex.I = -((Real.pi : ℂ) / 2 * Complex.I) by ring,
        Complex.exp_neg, hi]
      simp [Complex.inv_I]
  · simp [active] at hc
  · fin_cases s
    · norm_num [hyperchargeThirds_apply, baseProtocol, phaseIndex]
    · norm_num [hyperchargeThirds_apply, baseProtocol, phaseIndex]
      rw [show -((Real.pi : ℂ) * 6) / 4 * Complex.I =
        (Real.pi : ℂ) / 2 * Complex.I - (2 * Real.pi : ℂ) * Complex.I by ring,
        Complex.exp_sub, hi, Complex.exp_two_pi_mul_I, div_one]

/-- Packet transport with the target phase removed on the transported branch. -/
def matchedTransport (s : Option BaseProtocol) : M :=
  star (Complex.I ^ (phaseIndex s).val) • hypercharge (3 * Real.pi / 4)

/-- The two plus ports compare with the matched transport and its square. -/
def select (s : Option BaseProtocol) : M :=
  let U := matchedTransport s
  plus (U * U) * plus U

/-- A selected static channel never flags in either matched comparison.
This counts outcomes of the two comparisons and leaves their implementation cost open. -/
theorem matched_flags_zero (s : Option BaseProtocol) (c : Channels)
    (hc : active c = false) (hs : baseProtocol c = s) :
    let U := matchedTransport s
    PMAction.InterferenceReadout.flagProbability U c = 0 ∧
      PMAction.InterferenceReadout.flagProbability (U * U) c = 0 := by
  let U := matchedTransport s
  have hunit : star (Complex.I ^ (phaseIndex s).val) * Complex.I ^ (phaseIndex s).val = 1 := by
    rw [star_pow, ← mul_pow]
    simp [Complex.conj_I]
  have hcol (b : Channels) : U b c = (1 : M) b c := by
    change matchedTransport s b c = _
    rw [matchedTransport, transport_diagonal, Matrix.smul_apply, smul_eq_mul]
    by_cases h : b = c
    · subst b
      rw [diagonal_apply_eq, static_phase c hc, hs, hunit, Matrix.one_apply_eq]
    · simp [h]
  have noFlag (A : M) (h : ∀ b, A b c = (1 : M) b c) :
      PMAction.InterferenceReadout.flagProbability A c = 0 := by
    simp [PMAction.InterferenceReadout.flagProbability,
      PMAction.InterferenceReadout.flagAmplitude, h]
  change PMAction.InterferenceReadout.flagProbability U c = 0 ∧
    PMAction.InterferenceReadout.flagProbability (U * U) c = 0
  refine ⟨noFlag U hcol, noFlag (U * U) (fun b => ?_)⟩
  calc
    (U * U) b c = (U * 1) b c := by simp only [Matrix.mul_apply, hcol]
    _ = (1 : M) b c := by rw [mul_one, hcol]

/-- Keep the static bank so the selector is never applied to the active hypercharge table. -/
def staticBank : M := diagonal (fun c => if active c = false then 1 else 0)

private theorem plus_diagonal (v : Channels → ℂ) :
    plus (diagonal v) = diagonal (fun c => (1 / 2 : ℂ) * (1 + v c)) := by
  ext i j
  by_cases hij : i = j <;> simp [plus, one_apply, diagonal, hij, smul_eq_mul]

private theorem quarter_select (i j : Fin 4) :
    let z := star (Complex.I ^ j.val) * Complex.I ^ i.val
    (1 / 2 : ℂ) * (1 + z * z) * ((1 / 2 : ℂ) * (1 + z)) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_succ, Complex.I_sq, Complex.conj_I]

/-- The comparisons retain a matching static channel with amplitude one and
give zero on every other static channel, also for coherent superpositions. -/
theorem select_static (s : Option BaseProtocol) (hs : s ≠ some .neutrino) :
    select s * staticBank =
      diagonal (fun c => if active c = false ∧ baseProtocol c = s then 1 else 0) := by
  unfold select matchedTransport staticBank
  simp only [transport_diagonal, ← diagonal_smul, diagonal_mul_diagonal, plus_diagonal]
  congr 1
  funext c
  by_cases hc : active c = false
  · simpa only [Pi.smul_apply, smul_eq_mul, hc, ite_true, true_and, static_phase c hc,
      mul_one, phaseIndex_inj c s hc hs] using
      quarter_select (phaseIndex (baseProtocol c)) (phaseIndex s)
  · simp [hc]

/-- The vector class occurs on a unique static generation leg. Selecting it
uses the existing class comparison and its generation context. -/
theorem vector_static_leg (g : Fin 3) (c : Channels) (amp : Fin 8)
    (hc : active c = false) :
    onWall 2 false (encode g c amp) = true ↔ g = 2 := by
  have ha : (encode g c amp).1 = frame (wallClass g false) amp := by
    simp [encode, place, hc]
  simp only [onWall, decide_eq_true_eq, ha]
  constructor
  · rintro ⟨i, hi⟩
    have h := frame_class_unique _ _ _ _ hi
    change g + 1 = (2 : Fin 3) + 1 at h
    exact add_right_cancel h
  · rintro rfl
    exact ⟨amp, rfl⟩

/-- On the static bank the joint selector is the product of the
hypercharge comparison and the vector glue-class test. -/
theorem joint_selector (s : BaseProtocol) (hs : s ≠ .neutrino) (g : Fin 3)
    (c : Channels) (amp : Fin 8) (hc : active c = false) :
    (if onWall 2 false (encode g c amp) then (select (some s) * staticBank) c c else 0) =
      if g = 2 ∧ baseProtocol c = some s then 1 else 0 := by
  have h := select_static (some s) (by simpa using hs)
  rw [h, diagonal_apply_eq]
  simp only [vector_static_leg g c amp hc, hc, true_and]
  by_cases hg : g = 2 <;> simp [hg]

/-- The static-sector flip with the selected vector leg driven at an extra
amplitude. The common term is shared by construction of this candidate. -/
def flip (s : BaseProtocol) (c : Channels) (δ ε : ℂ) (κ : Fin 3 → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ResonanceLift.shifted δ κ 2 (ε * (select (some s) * staticBank) c c)

/-- Every selected static protocol has the same linear determinant response
to the supplied offset. All other channels retain the bare determinant zero. -/
theorem det_flip_at_resonance (s : BaseProtocol) (hs : s ≠ .neutrino)
    (c : Channels) (δ ε : ℂ) (κ : Fin 3 → ℂ)
    (hres : δ ^ 3 = -(κ 0 * κ 1 * κ 2)) :
    (flip s c δ ε κ).det =
      if active c = false ∧ baseProtocol c = some s then δ ^ 2 * ε else 0 := by
  rw [flip, ResonanceLift.det_shifted_at_resonance _ _ _ _ hres,
    select_static (some s) (by simpa using hs), diagonal_apply_eq]
  split_ifs <;> simp

/-- If the unmodified calibration wire is kept stationary under the
same real detuning, that detuning is pinned by its cycle product. -/
theorem calibrated_detuning (Y R : Matrix (Fin 3) (Fin 3) ℂ)
    (hY : IsUnit Y.det) (hR : IsUnit R.det) (δ cycle : ℝ) (κ : Fin 3 → ℂ)
    (hcycle : 0 < cycle) (hκ : κ 0 * κ 1 * κ 2 = (cycle : ℂ))
    (hcal : ∃ w, w ≠ 0 ∧
      PMAction.ExactZeroMode.H Y (PMAction.ReferenceWallRotation.X (δ : ℂ) κ)ᴴ R *ᵥ w = 0) :
    δ = -cycle ^ ((1 : ℝ) / 3) := by
  have hd := (ResonanceLift.full_zero_iff Y R _ hY hR).mp hcal
  rw [PMAction.ReferenceWallRotation.det_X, hκ, add_eq_zero_iff_eq_neg] at hd
  exact PMAction.OtherWallFlipEvent.lazy_root cycle δ hcycle (by exact_mod_cast hd)

/-- At the shared bare resonance the candidate lifts exactly its selected
static protocol, with no zero-energy approximation in the two-wall model. -/
theorem full_zero_iff_unselected (Y R : Matrix (Fin 3) (Fin 3) ℂ)
    (hY : IsUnit Y.det) (hR : IsUnit R.det) (s : BaseProtocol) (hs : s ≠ .neutrino)
    (c : Channels) (δ ε : ℂ) (κ : Fin 3 → ℂ) (hδ : δ ≠ 0) (hε : ε ≠ 0)
    (hres : δ ^ 3 = -(κ 0 * κ 1 * κ 2)) :
    (∃ w, w ≠ 0 ∧ PMAction.ExactZeroMode.H Y (flip s c δ ε κ)ᴴ R *ᵥ w = 0) ↔
      ¬(active c = false ∧ baseProtocol c = some s) := by
  rw [flip, ResonanceLift.shifted_full_zero_iff Y R hY hR δ κ hδ hres,
    select_static (some s) (by simpa using hs), diagonal_apply_eq]
  by_cases h : active c = false ∧ baseProtocol c = some s <;> simp [h, hε]

end PMElementaryParticles.ChargedInsertion
