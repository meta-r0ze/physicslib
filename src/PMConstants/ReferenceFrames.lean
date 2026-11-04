import PMConstants.Allocation
import PMConstants.General.ReferenceCapacity
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# An internal reference and its resource cost

An in-band frame has a distinct marker alphabet (`none`) and payload symbols
(`some a`). Observing the whole frame locates a unique marker without an external
origin. One marker suffices; if a marker is mandatory, maximizing payload uses
exactly one slot. These premises describe a particular framing architecture.

A separate finite control track can instead store an origin alongside all payload
slots. Thus an internal reference does not universally imply a one-slot loss.
This module does not establish a physical cost for the separate track.
-/

namespace PMConstants.ReferenceFrames
open Finset

variable {N : ℕ} {A : Type*}

/-- Encode an origin and data at every other position in a single track. -/
def encode (o : Fin N) (data : {i : Fin N // i ≠ o} → A) : Fin N → Option A :=
  fun i => if h : i = o then none else some (data ⟨i, h⟩)

theorem marker_iff (o : Fin N) (data : {i : Fin N // i ≠ o} → A) (i : Fin N) :
    encode o data i = none ↔ i = o := by
  by_cases h : i = o <;> simp [encode, h]

/-- The frame itself determines its origin. This is state-dependent marking,
not the selection of a preferred label by a fully symmetric empty state. -/
theorem unique_marker (o : Fin N) (data : {i : Fin N // i ≠ o} → A) :
    ∃! i, encode o data i = none := by
  refine ⟨o, (marker_iff o data o).mpr rfl, ?_⟩
  intro i hi
  exact (marker_iff o data i).mp hi

theorem origin_recoverable (o p : Fin N)
    (data : {i : Fin N // i ≠ o} → A) (other : {i : Fin N // i ≠ p} → A)
    (heq : encode o data = encode p other) : o = p := by
  apply (marker_iff p other o).mp
  rw [← heq]
  exact (marker_iff o data o).mpr rfl

theorem payload_recoverable (o : Fin N) : Function.Injective (encode (A := A) o) := by
  intro data other h
  funext i
  have heq := congrFun h i
  simpa [encode, i.property] using heq

/-- Moving the whole frame just moves its marker; no label is privileged. -/
theorem relabel_marker (σ : Equiv.Perm (Fin N)) (o : Fin N)
    (data : {i : Fin N // i ≠ o} → A) (i : Fin N) :
    encode o data (σ.symm i) = none ↔ i = σ o := by
  rw [marker_iff]
  constructor
  · intro h; simpa using congrArg σ h
  · intro h; rw [h]; simp

/-- A tick rotates the entire frame, preserving both marker and data. -/
def advanceFrame (frame : Fin N → Option A) : Fin N → Option A :=
  fun i => frame ((finRotate N).symm i)

theorem frame_update_injective : Function.Injective (advanceFrame (N := N) (A := A)) := by
  intro f g h
  funext i
  have hi := congrFun h (finRotate N i)
  simpa only [advanceFrame, Equiv.symm_apply_apply] using hi

/-- The extra marker symbol in `Option A` is a real alphabet assumption.
Independent origin and 171 binary payload bits cannot fit in 172 binary cells. -/
theorem binary_marker_capacity_obstruction :
    ¬ ∃ f : (Fin 172 × (Fin 171 → Bool)) → (Fin 172 → Bool), Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  norm_num [Fintype.card_prod, Fintype.card_fun] at h

/-- Counting all independent origin/payload combinations gives a sharper
bound in a binary 172-cell memory. This is an encoding bound, not a claim
that manifold addresses in the paper are binary memory cells. -/
theorem binary_payload_bound (K : ℕ)
    (f : (Fin 172 × (Fin K → Bool)) → (Fin 172 → Bool))
    (hf : Function.Injective f) : K ≤ 164 := by
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool] at hcard
  by_contra hK
  have hp : (2 : ℕ)^165 ≤ 2^K := pow_le_pow_right₀ (by decide) (by omega)
  norm_num at hcard hp
  omega

theorem payload_slots (o : Fin N) :
    (univ.filter (fun i : Fin N => i ≠ o)).card = N-1 := by
  have heq : univ.filter (fun i : Fin N => i ≠ o) = univ.erase o := by
    ext i; simp [ne_comm]
  rw [heq]
  simp

/-- A finite set of mandatory reserved positions removes exactly its size. -/
theorem payload_count (R : Finset (Fin N)) : (univ \ R).card = N-R.card := by
  rw [card_sdiff_of_subset (subset_univ R)]
  simp

/-- If at least one in-band marker is compulsory, one marker maximizes payload. -/
theorem inband_bound (R : Finset (Fin N)) (hR : R.Nonempty) :
    (univ \ R).card ≤ N-1 := by
  rw [payload_count]
  have := hR.card_pos
  omega

theorem inband_optimal_iff (R : Finset (Fin N)) (hR : R.Nonempty) :
    (univ \ R).card = N-1 ↔ R.card = 1 := by
  have hle : R.card ≤ N := by simpa using card_le_card (subset_univ R)
  have hpos := hR.card_pos
  rw [payload_count]
  omega

theorem optimal_172_overhead (R : Finset (Fin 172)) (hR : R.Nonempty)
    (hopt : ∀ S : Finset (Fin 172), S.Nonempty →
      (univ \ S).card ≤ (univ \ R).card) :
    ((univ \ R).card : ℝ)/172 = overhead := by
  have hmax := hopt {0} (by simp)
  have hbound := inband_bound R hR
  have hsing : (univ \ ({0} : Finset (Fin 172))).card = 171 := by
    rw [payload_count]; simp
  rw [hsing] at hmax
  have heq : (univ \ R).card = 171 := by omega
  rw [heq]
  norm_num [overhead]

/-- A second route to the same static payload fraction, independent of the
marker implementation. This assumes a closed homogeneous-width register model
and independently recoverable reference/payload. It does not assert that the
static optimal code is local, cheap or compatible with the physical clock. -/
theorem static_capacity_optimal_overhead (a K : ℕ) (ha : 172 ≤ a)
    (h : General.ReferenceCapacity.OptimalPayload 172 K a 172) :
    (K : ℝ)/172 = overhead := by
  have hK := (General.ReferenceCapacity.optimal_payload_iff 172 K a 172
    (by decide) (by decide) ha).mp h
  rw [hK]
  norm_num [overhead]

/-- A separate internal controller stores the origin without erasing data. -/
abbrev SeparateTrack (N : ℕ) (A : Type*) := Fin N × (Fin N → A)

def advanceSeparate (x : SeparateTrack N A) : SeparateTrack N A :=
  (finRotate N x.1, x.2)

theorem separate_reversible : Function.Bijective (advanceSeparate (N := N) (A := A)) := by
  constructor
  · intro x y h
    change (finRotate N x.1, x.2) = (finRotate N y.1, y.2) at h
    apply Prod.ext
    · exact (finRotate N).injective (congrArg Prod.fst h)
    · have hs := congrArg (fun z : Fin N × (Fin N → A) => z.2) h
      exact hs
  · intro y
    refine ⟨((finRotate N).symm y.1, y.2), ?_⟩
    apply Prod.ext
    · exact (finRotate N).apply_symm_apply y.1
    · rfl

theorem separate_preserves_payload (x : SeparateTrack N A) :
    (advanceSeparate x).2 = x.2 := rfl

theorem separate_finite [Fintype A] :
    Fintype.card (SeparateTrack N A) = N * Fintype.card A ^ N := by
  simp [SeparateTrack]

end PMConstants.ReferenceFrames
