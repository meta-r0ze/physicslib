import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! Reversible coarse descriptions and metadata capacity. These are finite
distinguishability theorems; no mass or thermodynamic conversion is assumed.
-/
namespace PMConstants.General.Encoding

variable {States Labels Metadata : Type*}

def encode (coarse : States → Labels) (metadata : States → Metadata) (x : States) :=
  (coarse x, metadata x)

/-- Metadata must separate precisely the distinctions the coarse description
merges. This is the general reversible-encoding contract. -/
theorem reversible_iff (coarse : States → Labels) (metadata : States → Metadata) :
    Function.Injective (encode coarse metadata) ↔
      ∀ x y, coarse x = coarse y → metadata x = metadata y → x = y := by
  constructor
  · intro h x y hc hm; exact h (Prod.ext hc hm)
  · intro h x y he
    exact h x y (congrArg Prod.fst he) (congrArg Prod.snd he)

/-- Reversibility is equivalent to an actual partial decoder on label/metadata
pairs. Impossible codes can return `none`; every encoded state is recovered. -/
theorem reversible_iff_decoder (coarse : States → Labels) (metadata : States → Metadata) :
    Function.Injective (encode coarse metadata) ↔
      ∃ decode : Labels × Metadata → Option States,
        ∀ x, decode (encode coarse metadata x) = some x := by
  classical
  constructor
  · intro h
    refine ⟨fun code => if hc : ∃ x, encode coarse metadata x = code
      then some hc.choose else none, ?_⟩
    intro x
    dsimp only
    split_ifs with hc
    · exact congrArg some (h hc.choose_spec)
    · exact (hc ⟨x, rfl⟩).elim
  · rintro ⟨decode, hd⟩ x y he
    have h := congrArg decode he
    rw [hd, hd] at h
    exact Option.some.inj h

/-- The metadata alphabet must be at least as large as each coarse fiber. -/
theorem fiber_capacity [Fintype States] [Fintype Metadata]
    (coarse : States → Labels) (metadata : States → Metadata)
    (h : Function.Injective (encode coarse metadata)) (q : Labels) :
    Nat.card {x : States // coarse x = q} ≤ Fintype.card Metadata := by
  classical
  let f : {x : States // coarse x = q} → Metadata := fun x => metadata x
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact (reversible_iff coarse metadata).mp h x y (x.property.trans y.property.symm) he
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf

theorem total_capacity [Fintype States] [Fintype Labels] [Fintype Metadata]
    (coarse : States → Labels) (metadata : States → Metadata)
    (h : Function.Injective (encode coarse metadata)) :
    Fintype.card States ≤ Fintype.card Labels * Fintype.card Metadata := by
  simpa using Fintype.card_le_of_injective (encode coarse metadata) h

/-- If a coarse label has k independent possible remainders, storing fewer
than k metadata states cannot preserve all those states. -/
theorem remainder_capacity (k : ℕ) [Fintype Metadata] (q : Labels)
    (metadata : Labels × Fin k → Metadata)
    (h : Function.Injective (encode Prod.fst metadata)) : k ≤ Fintype.card Metadata := by
  have hinj : Function.Injective (fun i : Fin k => metadata (q, i)) := by
    intro i j he
    have hpair := (reversible_iff Prod.fst metadata).mp h (q, i) (q, j) rfl he
    exact congrArg Prod.snd hpair
  simpa using Fintype.card_le_of_injective _ hinj

/-- Renaming metadata preserves the information. A physical interpretation
of that metadata requires additional structure beyond reversibility. -/
theorem metadata_relabel {M' : Type*} (coarse : States → Labels)
    (metadata : States → Metadata) (e : Metadata ≃ M')
    (h : Function.Injective (encode coarse metadata)) :
    Function.Injective (encode coarse (e ∘ metadata)) := by
  apply (reversible_iff _ _).mpr
  intro x y hc hm
  exact (reversible_iff _ _).mp h x y hc (e.injective hm)

end PMConstants.General.Encoding
