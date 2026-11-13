import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Finite substrate capacity and homogeneous-cell state counting.
No continuum metric, radiation process or black-hole entropy normalization is assumed. -/
noncomputable section
namespace PMCosmology.InformationCapacity

/-- A full finite register cannot retain its old labels and injectively encode a fresh label. -/
theorem no_fresh_label_at_saturation (C : ℕ) :
    ¬ ∃ encode : Fin (C+1) → Fin C, Function.Injective encode := by
  rintro ⟨encode, hinj⟩
  have := Fintype.card_le_of_injective encode hinj
  simp only [Fintype.card_fin] at this
  omega

/-- Reversible storage of a new independent input needs additional outcomes or capacity. -/
theorem new_input_needs_extra_capacity {C N : ℕ} (hC : 0 < C) (hN : 1 < N) :
    ¬ ∃ encode : Fin C × Fin N → Fin C, Function.Injective encode := by
  rintro ⟨encode, hinj⟩
  have h := Fintype.card_le_of_injective encode hinj
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  nlinarith

abbrev CellStates (cells statesPerCell : ℕ) := Fin cells → Fin statesPerCell

theorem states_count (cells statesPerCell : ℕ) :
    Fintype.card (CellStates cells statesPerCell) = statesPerCell^cells := by simp [CellStates]

/-- Recovering the initial state and every input requires room for every possible history. -/
theorem retained_history_capacity {Initial Final : Type*} [Fintype Initial] [Fintype Final]
    {ticks choices : ℕ} (encode : Initial × CellStates ticks choices → Final)
    (decode : Final → Initial × CellStates ticks choices) (recover : Function.LeftInverse decode encode) :
    Fintype.card Initial * choices ^ ticks ≤ Fintype.card Final := by
  simpa only [Fintype.card_prod, states_count] using
    Fintype.card_le_of_injective encode recover.injective

/-- Retaining every initial binary cell and one independent bit per tick needs this many cells. -/
theorem retained_binary_history_cells {initial ticks final : ℕ}
    (encode : CellStates initial 2 × CellStates ticks 2 → CellStates final 2)
    (decode : CellStates final 2 → CellStates initial 2 × CellStates ticks 2)
    (recover : Function.LeftInverse decode encode) : initial + ticks ≤ final := by
  have bound := retained_history_capacity encode decode recover
  rw [states_count, states_count, ← pow_add] at bound
  exact (pow_right_strictMono₀ (by decide : 1 < (2 : ℕ))).le_iff_le.mp bound

/-- Information in nats: the logarithm of the number of equal-weight configurations. -/
def information (cells statesPerCell : ℕ) : ℝ :=
  Real.log (Fintype.card (CellStates cells statesPerCell))

theorem information_adds (cells statesPerCell : ℕ) :
    information cells statesPerCell = cells*Real.log statesPerCell := by
  rw [information, states_count]
  push_cast
  rw [Real.log_pow]

theorem binary_cell_information (cells : ℕ) : information cells 2 = cells*Real.log 2 :=
  information_adds cells 2

/-- An area law follows from independent identical cells and additive cell area.
Its coefficient is log(q)/a, which still needs a physical choice of q and a. -/
theorem area_proportional_information (cells q : ℕ) (a : ℝ) (ha : a ≠ 0) :
    information cells q = ((cells : ℝ)*a)*(Real.log q/a) := by
  rw [information_adds]
  field_simp

/-- One binary cell of area 4 l² gives log(2)/(4 l²) nats per area.
It does not by counting alone give 1/(4 l²). -/
theorem binary_area_normalization (cells : ℕ) (l : ℝ) (hl : l ≠ 0) :
    information cells 2 = ((cells : ℝ)*(4*l^2))*(Real.log 2/(4*l^2)) := by
  exact area_proportional_information cells 2 (4*l^2) (by positivity)

end PMCosmology.InformationCapacity
