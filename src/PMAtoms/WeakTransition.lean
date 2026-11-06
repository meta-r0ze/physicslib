import PMAtoms.BetaCalibration
import PMAction.CarrierVacuumSector
import PMSubstrate.E8Values
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite weak transition operator

The interaction remainder `σ−χ = 3` supplies the three internal weak channels.
`PMAction.CarrierVacuumSector.identification` shows the three carrier sectors are
isometric, so the normalized operator assigns equal weight to each.  A transition
distributes one contact amplitude `G` equally over those channels.  The operator
is diagonal in the channel label; its squared trace is the per-tick hazard.

This is the finite operator model behind `BetaCalibration.betaHazardE8`.
-/

noncomputable section
namespace PMAtoms

/-- The `σ−χ = 3` internal weak channels. -/
abbrev WeakChannel : Type := Fin (PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi)

theorem weakChannel_card : Fintype.card WeakChannel = 3 := by
  unfold WeakChannel
  norm_num [PMSubstrate.E8Values.sigma, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]

/-- Amplitude carried by one internal weak channel. -/
def weakChannelAmplitude (G : ℝ) : ℝ :=
  G / (((PMSubstrate.E8Values.sigma - PMSubstrate.E8Values.chi : Nat)) : ℝ)

/-- Diagonal finite weak transition operator. -/
def weakTransitionOperator (G : ℝ) : WeakChannel → ℝ :=
  fun _ => weakChannelAmplitude G

/-- Per-tick weak hazard: squared operator trace over the internal channels. -/
def weakTransitionHazard (G : ℝ) : ℝ :=
  ∑ c : WeakChannel, (weakTransitionOperator G c) ^ 2

theorem weakChannelAmplitude_eq (G : ℝ) : weakChannelAmplitude G = G / 3 := by
  unfold weakChannelAmplitude
  norm_num [PMSubstrate.E8Values.sigma, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]

/-- **The channel sum reduces to `G²/(σ−χ)`.** -/
theorem weakTransitionHazard_eq (G : ℝ) :
    weakTransitionHazard G = G ^ 2 / 3 := by
  unfold weakTransitionHazard weakTransitionOperator weakChannelAmplitude
  norm_num [WeakChannel, PMSubstrate.E8Values.sigma, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]
  ring

theorem weakTransitionHazard_pos (G : ℝ) (hG : G ≠ 0) :
    0 < weakTransitionHazard G := by
  rw [weakTransitionHazard_eq]
  positivity

/-- Instantiate the operator with the E8 weak amplitude. -/
def weakHazardFromAmplitude : ℝ := weakTransitionHazard PMElementaryParticles.NeutronRate.fermiME

theorem weakHazardFromAmplitude_eq :
    weakHazardFromAmplitude = betaHazardE8 := by
  unfold weakHazardFromAmplitude betaHazardE8 weakAmplitudeSquared weakChannelCost
  rw [weakTransitionHazard_eq]
  norm_num [PMSubstrate.E8Values.sigma, PMSubstrate.E8Values.chi,
    PMSubstrate.baseline]
  ring

/-- A normalized three-channel weak current state. -/
def weakCurrent (psi : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun c => (1 / 3) * psi c

/-- Squared current weight over the three channels. -/
def weakCurrentWeight (psi : Fin 3 → ℝ) : ℝ :=
  ∑ c, (weakCurrent psi c) ^ 2

theorem weakCurrentWeight_eq (psi : Fin 3 → ℝ)
    (h : ∑ c, (psi c) ^ 2 = 3) :
    weakCurrentWeight psi = 1 / 3 := by
  unfold weakCurrentWeight weakCurrent
  calc
    ∑ c, ((1 / 3) * psi c) ^ 2 = (1 / 3 : ℝ) ^ 2 * ∑ c, (psi c) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = 1 / 3 := by rw [h]; norm_num

/-- Hazard from the normalized current and contact amplitude `G`. -/
def weakHazardFromCurrent (G : ℝ) (psi : Fin 3 → ℝ) : ℝ :=
  G ^ 2 * weakCurrentWeight psi

theorem weakHazardFromCurrent_eq (G : ℝ) (psi : Fin 3 → ℝ)
    (h : ∑ c, (psi c) ^ 2 = 3) :
    weakHazardFromCurrent G psi = G ^ 2 / 3 := by
  unfold weakHazardFromCurrent
  rw [weakCurrentWeight_eq psi h]
  ring

/-- Actual finite current entries: one unit per carrier channel.  The three
carrier sectors are isometric (`PMAction.CarrierVacuumSector.isometry`). -/
def weakCurrentEntries : Fin 3 → ℝ := fun _ => 1

theorem weakCurrentEntries_norm :
    ∑ c, (weakCurrentEntries c) ^ 2 = 3 := by
  simp [weakCurrentEntries]

/-- The unit-entry current gives the E8 channel hazard `G²/3`. -/
theorem weakHazardFromEntries_eq (G : ℝ) :
    weakHazardFromCurrent G weakCurrentEntries = G ^ 2 / 3 :=
  weakHazardFromCurrent_eq G weakCurrentEntries weakCurrentEntries_norm

open PMAction.CarrierVacuumSector

/-- Normalized trace of the actual carrier embedding on channel `c`. -/
noncomputable def weakCarrierEntry (c : Fin 3) : ℂ :=
  (1 / (Fintype.card PMAction.ConcreteFermion.Sites : ℂ)) *
    Matrix.trace (Matrix.conjTranspose (embedding c) * embedding c)

/-- The carrier isometry makes every normalized channel entry one. -/
theorem weakCarrierEntry_eq_one (c : Fin 3) : weakCarrierEntry c = 1 := by
  unfold weakCarrierEntry
  rw [isometry c, Matrix.trace_one]
  have hcard : (Fintype.card PMAction.ConcreteFermion.Sites : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := PMAction.ConcreteFermion.Sites)
  field_simp [hcard]

/-- Real channel entry extracted from the carrier trace. -/
noncomputable def weakCarrierEntryReal (c : Fin 3) : ℝ :=
  (weakCarrierEntry c).re

theorem weakCarrierEntryReal_eq_one (c : Fin 3) :
    weakCarrierEntryReal c = 1 := by
  unfold weakCarrierEntryReal
  rw [weakCarrierEntry_eq_one]
  norm_num

/-- The actual carrier entries are the unit entries used by the finite operator. -/
theorem weakCarrierEntries_eq :
    weakCarrierEntryReal = weakCurrentEntries := by
  funext c
  rw [weakCarrierEntryReal_eq_one]
  rfl

/-- The weak carrier operator on a carrier state space. -/
noncomputable def weakCarrierOperator (c : Fin 3) :
    Matrix PMAction.ConcreteFermion.Sites PMAction.ConcreteFermion.Sites ℂ :=
  Matrix.conjTranspose (embedding c) * embedding c

/-- The carrier isometry makes the operator the identity. -/
theorem weakCarrierOperator_eq_one (c : Fin 3) :
    weakCarrierOperator c = 1 :=
  isometry c

/-- Actual operator entries: diagonal one, off-diagonal zero. -/
theorem weakCarrierOperator_apply (c : Fin 3)
    (i j : PMAction.ConcreteFermion.Sites) :
    weakCarrierOperator c i j = if i = j then 1 else 0 := by
  rw [weakCarrierOperator_eq_one, Matrix.one_apply]

/-- The normalized trace entry is exactly the diagonal operator entry. -/
theorem weakCarrierEntry_eq_diagonal (c : Fin 3)
    (i : PMAction.ConcreteFermion.Sites) :
    weakCarrierOperator c i i = 1 := by
  rw [weakCarrierOperator_apply]
  simp

/-- Operator-derived channel entry: a diagonal matrix element of the carrier
weak operator. -/
noncomputable def weakOperatorEntry (c : Fin 3) : ℝ :=
  (weakCarrierOperator c
    (Classical.arbitrary PMAction.ConcreteFermion.Sites)
    (Classical.arbitrary PMAction.ConcreteFermion.Sites)).re

theorem weakOperatorEntry_eq_one (c : Fin 3) : weakOperatorEntry c = 1 := by
  unfold weakOperatorEntry
  rw [weakCarrierOperator_apply]
  simp

/-- The operator-derived entries are exactly `weakCurrentEntries`. -/
theorem weakOperatorEntry_eq_entries :
    weakOperatorEntry = weakCurrentEntries := by
  funext c
  rw [weakOperatorEntry_eq_one]
  rfl

/-- Off-diagonal carrier entries vanish. -/
theorem weakCarrierOperator_offdiag_zero (c : Fin 3)
    {i j : PMAction.ConcreteFermion.Sites} (h : i ≠ j) :
    weakCarrierOperator c i j = 0 := by
  rw [weakCarrierOperator_apply]
  simp [h]

end PMAtoms
