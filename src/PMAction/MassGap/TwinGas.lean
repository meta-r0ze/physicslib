import PMAction.MassGap.PolymerConvergence

/-!
# Sign twins: activity sign changes as allowed-set toggles

The correlation theorems (`PolymerInfluence.cross_ratio_of_close`) compare partition functions of
different **allowed sets** with the same activities. A parity observable instead flips the
**sign** of some activities. Giving every polymer two copies, one with each sign, turns a sign
choice into a choice of allowed set.

* `inc2`, `w2`: the twin gas on `P × Bool`; twins of the same polymer are incompatible when the
  polymer is incompatible with itself (every nonempty contour is).
* `sel s`: the allowed set that keeps, for each polymer, the twin with sign `s γ`.
* `Z_sel`: `Z_twin(sel s) = Z(univ)` with activities `± w γ`. The twin gas reproduces the signed
  gas exactly.
* `sel_eq_symmDiff`: `sel s = sel true ∆ twins {γ | s γ = false}`, and twin sets compose by
  symmetric difference (`twins_symmDiff`). A sign change on a set `F` of polymers is the toggle
  `∆ twins F`.
-/

namespace PMAction.MassGap.TwinGas
open Finset PolymerConvergence

variable {P : Type*} [Fintype P] [DecidableEq P] (inc : P → P → Prop) [DecidableRel inc]
  (w : P → ℝ)

/-- Twin incompatibility. -/
def inc2 (a b : P × Bool) : Prop := inc a.1 b.1

instance : DecidableRel (inc2 inc) := fun a b => inferInstanceAs (Decidable (inc a.1 b.1))

/-- Twin activity: `w` for the `true` twin, `−w` for the `false` twin. -/
def w2 (a : P × Bool) : ℝ := if a.2 then w a.1 else -w a.1

/-- Keep, for every polymer, the twin with sign `s γ`. -/
def sel (s : P → Bool) : Finset (P × Bool) := univ.image fun γ => (γ, s γ)

/-- Both twins of a set of polymers. -/
def twins (F : Finset P) : Finset (P × Bool) := F ×ˢ univ

lemma mem_sel {s : P → Bool} {a : P × Bool} : a ∈ sel s ↔ a.2 = s a.1 := by
  constructor
  · intro h; obtain ⟨γ, -, rfl⟩ := mem_image.mp h; rfl
  · intro h; exact mem_image.mpr ⟨a.1, mem_univ _, Prod.ext rfl h.symm⟩

/-- **The twin gas reproduces the signed gas.** -/
theorem Z_sel (s : P → Bool) :
    Z (inc2 inc) (w2 w) (sel s) = Z inc (fun γ => if s γ then w γ else -w γ) univ := by
  classical
  unfold Z
  let φ : P → P × Bool := fun γ => (γ, s γ)
  have hφ : Function.Injective φ := fun a b h => (Prod.ext_iff.mp h).1
  symm
  apply Finset.sum_nbij' (fun J => J.image φ) (fun I => I.image Prod.fst)
  · intro J hJ
    simp only [mem_filter, mem_powerset] at hJ ⊢
    refine ⟨fun a ha => ?_, ?_⟩
    · obtain ⟨γ, -, rfl⟩ := mem_image.mp ha; exact mem_image.mpr ⟨γ, mem_univ _, rfl⟩
    · intro a ha b hb hab
      obtain ⟨γ, hγ, rfl⟩ := mem_image.mp ha
      obtain ⟨δ, hδ, rfl⟩ := mem_image.mp hb
      exact hJ.2 γ hγ δ hδ (fun h => hab (by rw [h]))
  · intro I hI
    simp only [mem_filter, mem_powerset] at hI ⊢
    refine ⟨subset_univ _, ?_⟩
    intro γ hγ δ hδ hγδ
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hγ
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hδ
    exact hI.2 a ha b hb (fun h => hγδ (by rw [h]))
  · intro J _
    ext γ; simp [φ]
  · intro I hI
    simp only [mem_filter, mem_powerset] at hI
    ext a
    simp only [mem_image]
    constructor
    · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
      have h := mem_sel.mp (hI.1 hc)
      have e : φ c.1 = c := Prod.ext rfl h.symm
      rw [e]; exact hc
    · intro ha
      have h := mem_sel.mp (hI.1 ha)
      exact ⟨a.1, ⟨a, ha, rfl⟩, Prod.ext rfl h.symm⟩
  · intro J _
    rw [prod_image fun a _ b _ h => hφ h]
    rfl

/-- **Sign changes are toggles.** -/
theorem sel_eq_symmDiff (s : P → Bool) :
    sel s = symmDiff (sel fun _ => true) (twins (univ.filter fun γ => s γ = false)) := by
  ext ⟨γ, b⟩
  simp only [Finset.mem_symmDiff, mem_sel, twins, mem_product, mem_filter, mem_univ, true_and,
    and_true]
  cases b <;> cases s γ <;> simp

omit [Fintype P] in
/-- Twin sets compose by symmetric difference. -/
theorem twins_symmDiff (F G : Finset P) : symmDiff (twins F) (twins G) = twins (symmDiff F G) := by
  ext ⟨γ, b⟩
  simp [twins, Finset.mem_symmDiff]

end PMAction.MassGap.TwinGas
