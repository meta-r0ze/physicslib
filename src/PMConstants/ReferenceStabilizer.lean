import PMConstants.ReferenceAnchor

/-!
# What the lepton-doublet reference leaves unbroken

`SharedReference` selects the lepton doublet as the single reserved electroweak reference, and
`ReferenceAnchor` shows its two carriers have charge `Q = 0` (the neutrino) and `Q = -1` (the
electron). This module asks which generators leave the reference invariant.

* `electroweak_stabilizer`: a real electroweak generator `weakGen A + b·Y/2`, with `A` Hermitian
  and traceless, annihilates the neutral reference carrier exactly when it is `b·Q`,
  `Q = T₃ + Y/2`. The reference therefore leaves one electroweak direction unbroken, and that
  direction is the electric charge.
* `charged_carrier_breaks_charge`: the same reference held on the electron carrier is not
  annihilated by `Q`, so a reference that keeps `Q` unbroken sits on its neutral carrier.
* `colour_unbroken`: every colour generator annihilates both reference carriers, so the reference
  leaves colour wholly unbroken.
* `quark_reference_breaks_colour`: a left-handed quark carrier is moved by a colour generator, so a
  quark reference would break colour.

The pattern `SU(3) × SU(2) × U(1)_Y → SU(3) × U(1)_Q` is therefore a consequence of the selected
reference, in the sense of generators that fix the reference carrier. Not derived here: that the
maintained reference state is a single carrier vector rather than a mixture, and the dynamics
that holds it there.
-/

noncomputable section
namespace PMConstants.ReferenceStabilizer
open PMConstants Matrix GeneratorNormalization PacketTraceForm ReferenceAnchor

/-- A generator annihilates a carrier when its column at that carrier vanishes. -/
def Fixes (G : PacketGaugeActions.M) (v : PacketGaugeActions.Channels) : Prop := ∀ c, G c v = 0

lemma hyper_lepton (s t : Fin 2) :
    hyperGen (lepton s) (lepton t) = if s = t then -1/2 else 0 := by
  fin_cases s <;> fin_cases t <;>
    norm_num [hyperGen, lepton, PacketGaugeActions.charge, PacketGaugeActions.block]

lemma weak_lepton (A : Matrix (Fin 2) (Fin 2) ℂ) (s t : Fin 2) :
    weakGen A (lepton s) (lepton t) = A s t := by
  simp [weakGen, lepton, PacketGaugeActions.block]

lemma weakGen_smul (r : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : weakGen (r • A) = r • weakGen A := by
  unfold weakGen PacketGaugeActions.block
  rw [Matrix.kronecker_smul]
  simp [Matrix.fromBlocks_smul]

lemma charge_fixes_neutral : Fixes (t3 + hyperGen) (lepton 0) := by
  intro c
  rcases c with q | q | s | s
  · simp [t3, hyperGen, lepton, weakGen, PacketGaugeActions.charge, PacketGaugeActions.block]
  · simp [t3, hyperGen, lepton, weakGen, PacketGaugeActions.charge, PacketGaugeActions.block]
  · fin_cases s
    · exact reference_charges.1
    · simp [t3, hyperGen, lepton, weakGen, PacketGaugeActions.charge, PacketGaugeActions.block]
  · simp [t3, hyperGen, lepton, weakGen, PacketGaugeActions.charge, PacketGaugeActions.block]

/-- **The reference leaves exactly the electric charge unbroken.** -/
theorem electroweak_stabilizer (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : Aᴴ = A) (htr : A.trace = 0)
    (b : ℝ) :
    Fixes (weakGen A + (b : ℂ) • hyperGen) (lepton 0) ↔
      weakGen A + (b : ℂ) • hyperGen = (b : ℂ) • (t3 + hyperGen) := by
  constructor
  · intro h
    have h0 := h (lepton 0)
    have h1 := h (lepton 1)
    simp only [Matrix.add_apply, Matrix.smul_apply, weak_lepton, hyper_lepton] at h0 h1
    norm_num at h0 h1
    have h01 : A 0 1 = 0 := by
      have := congrFun (congrFun hA 0) 1
      simp [Matrix.conjTranspose_apply, h1] at this
      exact this.symm
    have htr' : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using htr
    have hAe : A = (b : ℂ) • !![(1 / 2 : ℂ), 0; 0, -1 / 2] := by
      ext i j; fin_cases i <;> fin_cases j
      · simp; linear_combination h0
      · simp [h01]
      · simp [h1]
      · simp; linear_combination htr' - h0
    rw [hAe, t3, smul_add, weakGen_smul]
  · intro h c
    rw [h, Matrix.smul_apply, charge_fixes_neutral c, smul_zero]

/-- **On the electron carrier the charge is broken.** -/
theorem charged_carrier_breaks_charge : ¬ Fixes (t3 + hyperGen) (lepton 1) := by
  intro h
  have := h (lepton 1)
  rw [reference_charges.2] at this
  norm_num at this

/-- **Colour is unbroken by the reference.** -/
theorem colour_unbroken (B : Matrix (Fin 3) (Fin 3) ℂ) (s : Fin 2) :
    Fixes (colourGen B) (lepton s) := by
  intro c
  rcases c with q | q | t | t <;> simp [colourGen, lepton, PacketGaugeActions.block]

/-- **A quark reference would break colour.** -/
theorem quark_reference_breaks_colour :
    ∃ B : Matrix (Fin 3) (Fin 3) ℂ, Bᴴ = B ∧ B.trace = 0 ∧ ¬ Fixes (colourGen B) qL := by
  refine ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 0], ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp [Matrix.trace, Fin.sum_univ_three]
  · intro h
    have := h (.inl (1, 0))
    simp [colourGen, qL, PacketGaugeActions.block, Matrix.kroneckerMap_apply] at this

end PMConstants.ReferenceStabilizer
