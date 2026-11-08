import PMElementaryParticles.ProtocolDynamics
import PMElementaryParticles.MuonLifetime

/-! **General substrate transition form.**

A decay is a sum over allowed final-state cohorts:

```
partialWidth i f = |⟨f|T|i⟩|² · phaseSpace i f   (when Decay i f)
totalWidth i     = Σ_f partialWidth i f
lifetime i       = 1 / totalWidth i
branching i f    = partialWidth i f / totalWidth i
```

`T` and the phase-space factor are supplied inputs here.  The point is to have
one form that the one-by-one particle rates instantiate, instead of separate
bespoke rate definitions.
-/

noncomputable section
namespace PMElementaryParticles.SubstrateTransition

open PMElementaryParticles.ProtocolDynamics

/-- A finite transition system on substrate states. -/
structure TransitionSystem where
  operator : State → List State → ℂ
  phaseSpace : State → List State → ℝ
  finals : Finset (List State)

/-- Partial width of one final-state cohort. -/
def partialWidth (S : TransitionSystem) (i : State) (f : List State) : ℝ := by
  classical
  exact if Decay i f then Complex.normSq (S.operator i f) * S.phaseSpace i f else 0

/-- Total width as a sum over the declared final states. -/
def totalWidth (S : TransitionSystem) (i : State) : ℝ :=
  ∑ f ∈ S.finals, partialWidth S i f

/-- Lifetime from the total width. -/
def lifetime (S : TransitionSystem) (i : State) : ℝ :=
  1 / totalWidth S i

/-- Branching fraction. -/
def branching (S : TransitionSystem) (i : State) (f : List State) : ℝ :=
  partialWidth S i f / totalWidth S i

theorem partialWidth_nonneg (S : TransitionSystem) (i : State) (f : List State)
    (hΦ : 0 ≤ S.phaseSpace i f) : 0 ≤ partialWidth S i f := by
  unfold partialWidth
  split_ifs
  · exact mul_nonneg (Complex.normSq_nonneg _) hΦ
  · exact le_rfl

theorem totalWidth_nonneg (S : TransitionSystem) (i : State)
    (hΦ : ∀ f ∈ S.finals, 0 ≤ S.phaseSpace i f) : 0 ≤ totalWidth S i := by
  unfold totalWidth
  exact Finset.sum_nonneg fun f hf => partialWidth_nonneg S i f (hΦ f hf)

theorem partialWidth_zero_of_not_decay (S : TransitionSystem) (i : State) (f : List State)
    (h : ¬ Decay i f) : partialWidth S i f = 0 := by
  simp [partialWidth, h]

/-- A single-cohort system: one allowed final state with unit operator entry. -/
def singleChannel (i : State) (f : List State) (phase : ℝ) : TransitionSystem where
  operator := fun i' f' => if i' = i ∧ f' = f then 1 else 0
  phaseSpace := fun i' f' => if i' = i ∧ f' = f then phase else 0
  finals := {f}

theorem singleChannel_totalWidth (i : State) (f : List State) (hdec : Decay i f) (phase : ℝ) :
    totalWidth (singleChannel i f phase) i = phase := by
  unfold totalWidth partialWidth singleChannel
  rw [Finset.sum_singleton]
  simp [hdec]

theorem singleChannel_lifetime (i : State) (f : List State) (hdec : Decay i f) (phase : ℝ) :
    lifetime (singleChannel i f phase) i = 1 / phase := by
  unfold lifetime
  rw [singleChannel_totalWidth i f hdec phase]

/-- Muon initial state: electron protocol at tier 1. -/
def muonInitial : State := (.electron, ⟨1, by decide⟩)

/-- Muon final state: electron and two neutrinos at tier 0. -/
def muonFinal : List State :=
  [(.electron, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩), (.neutrino, ⟨0, by decide⟩)]

theorem muon_decay : Decay muonInitial muonFinal :=
  PMElementaryParticles.ProtocolDynamics.muon_decay

/-- A single-cohort muon system with supplied phase space. -/
def muonSystem (phase : ℝ) : TransitionSystem :=
  singleChannel muonInitial muonFinal phase

theorem muonSystem_totalWidth (phase : ℝ) :
    totalWidth (muonSystem phase) muonInitial = phase :=
  singleChannel_totalWidth muonInitial muonFinal muon_decay phase

/-- The E8 muon width is an instance of the general single-cohort form. -/
def muonSystemE8 : TransitionSystem :=
  muonSystem PMElementaryParticles.MuonLifetime.muonWidth

theorem muonSystemE8_totalWidth :
    totalWidth muonSystemE8 muonInitial = PMElementaryParticles.MuonLifetime.muonWidth :=
  muonSystem_totalWidth PMElementaryParticles.MuonLifetime.muonWidth

end PMElementaryParticles.SubstrateTransition
