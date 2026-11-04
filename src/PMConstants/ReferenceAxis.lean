import PMConstants.PersistenceClosures
import PMConstants.CarrierRepresentation

/-!
# The reference singles out the lepton axis

`CarrierRepresentation` reads the vector-class carriers `±2eᵢ` as the `(4, 2)` of `SU(4) × SU(2)`
and takes as a premise that one of the four axes is the lepton axis, which breaks `SU(4)` to colour.
The reserved reference supplies the axis.

* The reserved cell holds one carrier state (`ReferenceEconomy.cell_inj_of_content`), and every
  vector-class carrier lies on exactly one axis (`CarrierRepresentation.one_axis`). So the
  reference singles out exactly one axis.
* `axis_stabilizer`: a Hermitian `SU(4)` generator fixes the reference axis `e₀` exactly when it is
  the extension by zero of a Hermitian generator on the other three axes, with the same trace. So
  the generators the reference leaves unbroken are `SU(3)` acting on the three remaining axes:
  colour is the stabilizer of the reference's axis, and `4 - 1 = 3` colours follow.
* `bl_broken`: the `B - L` generator `diag(-1, 1/3, 1/3, 1/3)` is moved by the reference, as
  hypercharge is (`ReferenceStabilizer`); only `Q` survives among the neutral directions.
* `skipped_maintenance_fails`: with a drift `d > 0` per update and no repair, the displacement
  exceeds any tolerance after finitely many updates. The reference's maintenance is required work,
  not optional: skipping it does not persist.

The persistence reading: a maintained reference vector is refreshed against every symmetry that
moves it and needs nothing for those that fix it. Its axis is the lepton axis by definition, the
three others are colour, and the premise "one axis is the lepton axis" becomes "the reserved cell
holds one carrier state".
-/

noncomputable section
namespace PMConstants.ReferenceAxis
open Matrix

/-- Extension by zero of a generator on axes `1, 2, 3`. -/
def ext (C : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => Fin.cases 0 (fun i' => Fin.cases 0 (fun j' => C i' j') j) i

/-- `B` fixes the reference axis: its column at axis `0` vanishes. -/
def FixesAxis (B : Matrix (Fin 4) (Fin 4) ℂ) : Prop := ∀ i, B i 0 = 0

/-- **Colour is the stabilizer of the reference axis.** -/
theorem axis_stabilizer (B : Matrix (Fin 4) (Fin 4) ℂ) (hB : Bᴴ = B) :
    FixesAxis B ↔ ∃ C : Matrix (Fin 3) (Fin 3) ℂ, Cᴴ = C ∧ B = ext C ∧ B.trace = C.trace := by
  constructor
  · intro h
    have hrow : ∀ j, B 0 j = 0 := by
      intro j
      have := congrFun (congrFun hB 0) j
      rw [conjTranspose_apply] at this
      rw [← this, h j, star_zero]
    refine ⟨Matrix.of fun i j => B i.succ j.succ, ?_, ?_, ?_⟩
    · ext i j
      have := congrFun (congrFun hB i.succ) j.succ
      rw [conjTranspose_apply] at this ⊢
      simpa using this
    · ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [ext, hrow]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp only [ext, Fin.cases_succ, Fin.cases_zero]; exact h _
        · simp [ext]
    · simp [Matrix.trace, Fin.sum_univ_succ, hrow, Matrix.diag]
  · rintro ⟨C, -, rfl, -⟩ i
    refine Fin.cases ?_ (fun i' => ?_) i <;> simp [ext]

theorem ext_hermitian (C : Matrix (Fin 3) (Fin 3) ℂ) (hC : Cᴴ = C) : (ext C)ᴴ = ext C := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [ext, conjTranspose_apply]
  have := congrFun (congrFun hC i') j'
  simpa [conjTranspose_apply] using this

theorem ext_trace (C : Matrix (Fin 3) (Fin 3) ℂ) : (ext C).trace = C.trace := by
  simp [Matrix.trace, Fin.sum_univ_succ, ext]

/-- `B - L` on the four axes. -/
def bl : Matrix (Fin 4) (Fin 4) ℂ := diagonal ![-1, 1/3, 1/3, 1/3]

theorem bl_traceless : bl.trace = 0 := by
  simp [bl, Matrix.trace, Fin.sum_univ_succ]; norm_num

theorem bl_broken : ¬ FixesAxis bl := by
  intro h
  have := h 0
  simp [bl] at this

/-- **Skipped maintenance does not persist.** -/
theorem skipped_maintenance_fails (d tol : ℝ) (hd : 0 < d) : ∃ n : ℕ, tol < n * d := by
  obtain ⟨n, hn⟩ := exists_nat_gt (tol / d)
  exact ⟨n, by rwa [div_lt_iff₀ hd] at hn⟩

end PMConstants.ReferenceAxis
