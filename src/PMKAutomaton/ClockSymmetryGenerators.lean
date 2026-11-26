import PMKAutomaton.ClockSymmetryFrames

/-!
# Exhaustive generators of the aligned clock-root stabilizers

Six D3 reflections and one two-root glued word generate the full positive
clock-root stabilizer. Central lattice negation extends it to the line stabilizer.
The finite word table is in ClockSymmetryFrames.
-/
noncomputable section
namespace PMKAutomaton.ClockSymmetry
open Matrix PMSubstrate.Lattices PMKAutomaton.ClockRing PMKAutomaton.ClockAlignment

def generatorRootVectors : Fin 6 → V :=
  ![![0,0,0,0,0,0,0,-1],
    ![0,0,0,0,0,0,-1,0],
    ![2,3,4,6,5,4,2,1],
    ![0,0,0,-1,0,0,0,0],
    ![0,0,0,0,-1,0,0,0],
    ![0,-1,0,-1,-1,0,0,0]]

theorem generator_root_norms : ∀ i, pairing (generatorRootVectors i) (generatorRootVectors i) = 2 := by decide +kernel

def generatorRoots (i : Fin 6) : Root := ⟨generatorRootVectors i, generator_root_norms i⟩

theorem glued_swap_root_data :
    pairing rootPlus.val rootMinus.val = 0 ∧
    glueKey rootPlus.val = (0,1) ∧ glueKey rootMinus.val = (0,1) := by decide +kernel

def liftRoot (r : Root) : Weyl := ⟨rootReflection r, Subgroup.subset_closure ⟨r, rfl⟩⟩

def generatorWeyl (i : Fin 7) : Weyl :=
  if h : i.val < 6 then liftRoot (generatorRoots ⟨i.val,h⟩) else swapWeyl

theorem generator_checks : ∀ i : Fin 7,
    (∀ j, (generatorWeyl i).val (sectorProjection (basis j)) =
      sectorProjection ((generatorWeyl i).val (basis j))) ∧
    (generatorWeyl i).val PMSubstrate.ClockPlane.cu = PMSubstrate.ClockPlane.cu := by decide +kernel

def positiveGenerator (i : Fin 7) : Gplus :=
  ⟨generatorWeyl i, commutes_of_basis _ (generator_checks i).1, Or.inl (generator_checks i).2⟩

theorem positive_clock (w : Gplus) : w.val.val PMSubstrate.ClockPlane.cu = PMSubstrate.ClockPlane.cu := by
  rcases w.property.2 with h | ⟨h,_⟩
  · exact h
  · cases h

theorem generator_frame_check : ∀ (g : Fin 7) (b : Bool) (i : Fin 3),
    (generatorWeyl g).val (axis (spatialIndex b i)) =
      frameAxis b (if b then (generatorFrames g).2 else (generatorFrames g).1) i := by decide +kernel

def wordElement : List (Fin 7) → Gplus
  | [] => 1
  | i :: is => positiveGenerator i * wordElement is

private theorem map_signed (w : V ≃ₗ[ℤ] V) (n : Bool) (z : V) :
    w (signed n z) = signed n (w z) := by cases n <;> simp [signed]

private theorem signed_xor (n m : Bool) (z : V) :
    signed n (signed m z) = signed (Bool.xor n m) z := by cases n <;> cases m <;> simp [signed]

theorem frame_composition (w v : Weyl) (f g : FramePair)
    (hw : ∀ b i, w.val (axis (spatialIndex b i)) = frameAxis b (if b then f.2 else f.1) i)
    (hv : ∀ b i, v.val (axis (spatialIndex b i)) = frameAxis b (if b then g.2 else g.1) i) :
    ∀ b i, (w*v).val (axis (spatialIndex b i)) =
      frameAxis b (if b then (pairComp f g).2 else (pairComp f g).1) i := by
  intro b i
  change w.val (v.val (axis (spatialIndex b i))) = _
  rw [hv]
  unfold frameAxis
  rw [map_signed, hw]
  cases b <;> simp [pairComp, frameComp, frameAxis, signed_xor]

theorem word_spatial_action (word : List (Fin 7)) : ∀ b i,
    (wordElement word).val.val (axis (spatialIndex b i)) =
      frameAxis b (if b then (wordFrames word).2 else (wordFrames word).1) i := by
  induction word with
  | nil => intro b i; cases b <;> rfl
  | cons g rest ih => exact frame_composition _ _ _ _ (generator_frame_check g) ih

theorem word_axes_action (word : List (Fin 7)) : ∀ i,
    (wordElement word).val.val (axis i) =
      frameAxes false (wordFrames word).1 (wordFrames word).2 i :=
  axes_normal_form (wordElement word) false (positive_clock _) _ _ (word_spatial_action word)

/-- Exhaustiveness: every element of the INTRINSIC positive stabilizer is a word
in the displayed seven generators. -/
theorem positive_generators_exhaustive (w : Gplus) : ∃ word, wordElement word = w := by
  obtain ⟨fS,fI,hS,hI,hf⟩ := spatial_frames w false (positive_clock w)
  obtain ⟨i,hi⟩ := allFrames_complete fS.1 fS.2 hS
  obtain ⟨j,hj⟩ := allFrames_complete fI.1 fI.2 hI
  replace hi : allFrames i = fS := hi.trans Prod.mk.eta
  replace hj : allFrames j = fI := hj.trans Prod.mk.eta
  have ha := axes_normal_form w false (positive_clock w) fS fI hf
  have hm := normal_form_integral w false fS fI ha
  rw [← hi, ← hj] at hm
  have hp := integral_sign_parity false i j hm
  have hw := wordTable_correct i j hp
  refine ⟨wordTable i j, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have hlin := linear_ext_axes
    (f := (wordElement (wordTable i j)).val.val.toLinearMap)
    (g := w.val.val.toLinearMap) (fun a => by
      change (wordElement (wordTable i j)).val.val (axis a) = w.val.val (axis a)
      rw [word_axes_action, ha, hw]
      rw [hi,hj])
  exact congrArg (fun f : V →ₗ[ℤ] V => f z) hlin

def reversingRootVectors : Fin 8 → V :=
  ![![1,0,0,0,0,0,0,0],
    ![1,1,2,2,1,0,0,0],
    ![1,1,2,2,2,2,1,0],
    ![1,2,2,4,3,2,1,0],
    ![1,1,2,3,2,2,1,1],
    ![1,2,2,3,3,2,1,1],
    ![1,1,2,3,3,2,2,1],
    ![1,2,2,3,2,2,2,1]]

theorem reversing_root_norms : ∀ i, pairing (reversingRootVectors i) (reversingRootVectors i) = 2 := by decide +kernel

def reversingRoots (i : Fin 8) : Root := ⟨reversingRootVectors i, reversing_root_norms i⟩

def reversingWeyl : Weyl := (List.ofFn (fun i => liftRoot (reversingRoots i))).prod

theorem reversing_basis_check : ∀ i, reversingWeyl.val (basis i) = -basis i := by decide +kernel

theorem reversing_neg (z : V) : reversingWeyl.val z = -z := by
  have h := linear_ext_basis (f := reversingWeyl.val.toLinearMap) (g := -LinearMap.id)
    reversing_basis_check
  exact congrArg (fun f : V →ₗ[ℤ] V => f z) h

def reversingElement : Gpm := ⟨reversingWeyl,
  (fun z => by rw [reversing_neg, reversing_neg]; simp [sectorProjection, Matrix.mulVec_neg]),
  Or.inr ⟨rfl, reversing_neg _⟩⟩

def includePositive : Gplus →* Gpm where
  toFun w := ⟨w.val, w.property.1, Or.inl (positive_clock w)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem reversing_square : reversingElement * reversingElement = 1 := by
  apply Subtype.ext; apply Subtype.ext; apply LinearEquiv.ext
  intro z
  change reversingWeyl.val (reversingWeyl.val z) = z
  rw [reversing_neg, reversing_neg, neg_neg]

/-- Time reversal adds precisely one central negation word. -/
theorem line_generators_exhaustive (w : Gpm) :
    ∃ (t : Bool) (word : List (Fin 7)),
      w = if t then reversingElement * includePositive (wordElement word)
        else includePositive (wordElement word) := by
  rcases w.property.2 with hc | ⟨_,hc⟩
  · let p : Gplus := ⟨w.val, w.property.1, Or.inl hc⟩
    obtain ⟨word, hw⟩ := positive_generators_exhaustive p
    exact ⟨false, word, (congrArg includePositive hw).symm⟩
  · have hp : (reversingElement*w).val.val PMSubstrate.ClockPlane.cu = PMSubstrate.ClockPlane.cu := by
      change reversingWeyl.val (w.val.val _) = _
      rw [hc, reversing_neg, neg_neg]
    let p : Gplus := ⟨(reversingElement*w).val, (reversingElement*w).property.1, Or.inl hp⟩
    obtain ⟨word, hw⟩ := positive_generators_exhaustive p
    refine ⟨true, word, ?_⟩
    have h : includePositive (wordElement word) = reversingElement*w := congrArg includePositive hw
    rw [h, ← mul_assoc, reversing_square, one_mul]
    rfl

end PMKAutomaton.ClockSymmetry
