import PMConstants.Partition
import PMSubstrate.ClosureSymmetry

/-!
# What allocation equations select, and what finiteness does not select

These explicit balance equations select the displayed rational constants.
Their physical necessity is not inferred from budget closure alone.
-/

namespace PMConstants.Allocation

structure Values where
  η : ℝ
  strong : ℝ
  weak : ℝ
  scalar : ℝ

/-- One reserved address, saturated channel load, clock/footprint allocation,
and intrinsic-load scalar regulation. These are physical modeling premises. -/
structure Compatible (α : ℝ) (v : Values) : Prop where
  origin : 172 * v.η = 171
  saturation : v.strong = (16 * v.η + 1/4) * α
  temporal : (172 + 16 * v.η + 5) * v.weak = 43
  regulation : 23 * v.scalar + 1/43 = 3

theorem allocation_forced (α : ℝ) (v : Values) (h : Compatible α v) :
    v.η = overhead ∧ v.strong = strongCoupling α ∧
      v.weak = clockRatio ∧ v.scalar = selfCoupling := by
  have ho : v.η = overhead := by dsimp [overhead]; linarith [h.origin]
  refine ⟨ho, ?_, ?_, ?_⟩
  · simpa [strongCoupling, ho] using h.saturation
  · have ht := h.temporal
    rw [ho] at ht
    norm_num [overhead] at ht
    norm_num [clockRatio, footprint, overhead]
    linarith
  · norm_num [selfCoupling]
    linarith [h.regulation]

theorem allocation_exists (α : ℝ) :
    Compatible α ⟨overhead, strongCoupling α, clockRatio, selfCoupling⟩ := by
  constructor
  · norm_num [overhead]
  · rfl
  · norm_num [overhead, clockRatio, footprint]
  · norm_num [selfCoupling]

/-- A finite address book can have every address available. Finiteness alone
does not require a reserved delimiter. -/
theorem full_finite_payload :
    (Finset.univ : Finset (Fin 172)).card = 172 := by simp

/-- A chosen reserved origin gives the overhead used in the paper. -/
theorem one_origin_overhead (o : Fin 172) :
    ((Finset.univ.erase o).card : ℝ) / Fintype.card (Fin 172) = overhead := by
  simp [overhead]

/-- Full relabeling symmetry cannot itself choose exactly one reserved origin.
An origin must be marked relationally or supplied as additional structure. -/
theorem no_invariant_single_origin (S : Finset (Fin 172)) (hcard : S.card = 1) :
    ¬ ∀ σ : Equiv.Perm (Fin 172), S.map σ.toEmbedding = S := by
  intro hinv
  rcases PMSubstrate.ClosureSymmetry.invariant_set S hinv with h | h
  · simp [h] at hcard
  · simp [h] at hcard

end PMConstants.Allocation
