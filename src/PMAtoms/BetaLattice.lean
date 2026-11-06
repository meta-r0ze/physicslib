import PMAtoms.RateModel
import PMAtoms.MeanLife
import PMAtoms.LatticeSpectral
import Mathlib.Tactic

/-! **Experimental/candidate module.** Not part of `certifiedMass`.

# Finite E8 beta channel

The substrate route replaces the continuum Dalitz measure by a finite family of
open lattice modes.  A channel has `modes+1` labels and `active` active labels,
with `active ≤ modes`.  The decay rate is the `RateModel` cost rate on that
finite family; no continuum phase space is inserted.
-/

noncomputable section
namespace PMAtoms
open scoped BigOperators

/-- A finite beta channel: total label count `modes+1`, with `active` active modes. -/
structure BetaLatticeChannel where
  modes : Nat
  active : Nat
  h : active ≤ modes

namespace BetaLatticeChannel

/-- Number of labels in the finite mode family. -/
def size (c : BetaLatticeChannel) : Nat := c.modes + 1

/-- The active labels, as an initial segment of the finite family. -/
def event (c : BetaLatticeChannel) : Finset (Fin c.size) :=
  Finset.Iio ⟨c.active, Nat.lt_succ_of_le c.h⟩

/-- One transition family for the channel. -/
def family (c : BetaLatticeChannel) : Fin 1 → Finset (Fin c.size) :=
  fun _ => c.event

theorem event_card (c : BetaLatticeChannel) : c.event.card = c.active := by
  simp [event]

theorem prob_event (c : BetaLatticeChannel) :
    PMSubstrate.NetCost.prob c.event = (c.active : ℝ) / (c.size : ℝ) := by
  unfold PMSubstrate.NetCost.prob
  rw [event_card]
  have hsize : (Fintype.card (Fin c.size) : ℝ) = (c.modes + 1 : ℝ) := by
    rw [BetaLatticeChannel.size, Fintype.card_fin]
    norm_num
  rw [hsize, BetaLatticeChannel.size]
  norm_num

end BetaLatticeChannel

/-- Cost rate of a finite beta channel. -/
def betaLatticeCost (c0 : ℝ) (c : BetaLatticeChannel) : ℝ :=
  channelCost c0 c.family

/-- Decay rate of a finite beta channel. -/
def betaLatticeRate (β c0 : ℝ) (c : BetaLatticeChannel) : ℝ :=
  channelRate β c0 c.family

theorem betaLatticeRate_eq (β c0 : ℝ) (c : BetaLatticeChannel) :
    betaLatticeRate β c0 c =
      β * c0 * (c.active : ℝ) / (c.size : ℝ) := by
  unfold betaLatticeRate
  rw [channelRate_eq]
  simp [BetaLatticeChannel.family, BetaLatticeChannel.prob_event]
  ring

theorem betaLatticeCost_eq (c0 : ℝ) (c : BetaLatticeChannel) :
    betaLatticeCost c0 c = c0 * (c.active : ℝ) / (c.size : ℝ) := by
  unfold betaLatticeCost
  rw [channelCost_eq]
  simp [BetaLatticeChannel.family, BetaLatticeChannel.prob_event]
  ring

/-- Lifetime from the finite E8 cost rate. -/
def betaLatticeLifetime (β c0 : ℝ) (c : BetaLatticeChannel) : ℝ :=
  channelMeanLife β c0 c.family

theorem betaLatticeLifetime_eq (β c0 : ℝ) (c : BetaLatticeChannel) :
    betaLatticeLifetime β c0 c = 1 / betaLatticeRate β c0 c := rfl

theorem betaLatticeRate_pos (β c0 : ℝ) (c : BetaLatticeChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hactive : 0 < c.active) :
    0 < betaLatticeRate β c0 c := by
  rw [betaLatticeRate_eq]
  have hsize : 0 < (c.size : ℝ) := by
    unfold BetaLatticeChannel.size
    positivity
  have hnum : 0 < β * c0 * (c.active : ℝ) := by positivity
  exact div_pos hnum hsize

theorem betaLatticeLifetime_pos (β c0 : ℝ) (c : BetaLatticeChannel)
    (hβ : 0 < β) (hc0 : 0 < c0) (hactive : 0 < c.active) :
    0 < betaLatticeLifetime β c0 c := by
  unfold betaLatticeLifetime channelMeanLife MeanLife
  change 0 < 1 / betaLatticeRate β c0 c
  exact one_div_pos.mpr (betaLatticeRate_pos β c0 c hβ hc0 hactive)

/-- Boltzmann weight of a Dirichlet mode: `exp(−λ)`. -/
noncomputable def betaSpectralWeight (n a b c : Nat) : ℝ :=
  Real.exp (-(dirichletEigenvalue n a b c))

theorem betaSpectralWeight_pos (n a b c : Nat) : 0 < betaSpectralWeight n a b c := by
  unfold betaSpectralWeight
  positivity

/-- Weighted finite-channel rate: active spectral weight over total spectral weight. -/
noncomputable def betaWeightedRate (β c0 : ℝ) {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (S : Finset Ω) : ℝ :=
  β * c0 * S.sum w / Finset.univ.sum w

theorem betaWeightedRate_pos (β c0 : ℝ) {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → ℝ) (S : Finset Ω)
    (hβ : 0 < β) (hc0 : 0 < c0) (hw : ∀ i, 0 < w i)
    (hS : S.Nonempty) :
    0 < betaWeightedRate β c0 w S := by
  have htotal : 0 < Finset.univ.sum w := by
    apply Finset.sum_pos
    · intro i _
      exact hw i
    · exact Finset.univ_nonempty
  have hpart : 0 < S.sum w := by
    apply Finset.sum_pos
    · intro i _
      exact hw i
    · exact hS
  unfold betaWeightedRate
  exact div_pos (mul_pos (mul_pos hβ hc0) hpart) htotal

/-- Spectral finite-channel rate for the `n×n×n` cube. -/
noncomputable def betaSpectralRate (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n))) : ℝ :=
  betaWeightedRate β c0
    (fun p => betaSpectralWeight n (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1))
    S

set_option linter.style.haveILetI false in
theorem betaSpectralRate_pos (β c0 : ℝ) (n : Nat)
    (S : Finset (Fin n × (Fin n × Fin n)))
    (hβ : 0 < β) (hc0 : 0 < c0) (hn : 0 < n) (hS : S.Nonempty) :
    0 < betaSpectralRate β c0 n S := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold betaSpectralRate
  apply betaWeightedRate_pos
  · exact hβ
  · exact hc0
  · intro p
    exact betaSpectralWeight_pos n _ _ _
  · exact hS

/-- Open spectral modes below an energy cutoff. -/
noncomputable def betaOpenModes (n : Nat) (E : ℝ) :
    Finset (Fin n × (Fin n × Fin n)) := by
  classical
  exact Finset.univ.filter
    (fun p => dirichletEigenvalue n (p.1.val + 1) (p.2.1.val + 1) (p.2.2.val + 1) ≤ E)

/-- The lowest mode is open when the cutoff reaches its eigenvalue. -/
theorem betaOpenModes_nonempty {n : Nat} {E : ℝ} (hn : 0 < n)
    (hE : dirichletEigenvalue n 1 1 1 ≤ E) :
    (betaOpenModes n E).Nonempty := by
  refine ⟨(⟨0, hn⟩, (⟨0, hn⟩, ⟨0, hn⟩)), ?_⟩
  simp [betaOpenModes, hE]

/-- Cutoff-selected spectral beta rate. -/
noncomputable def betaSpectralRateCutoff (β c0 : ℝ) (n : Nat) (E : ℝ) : ℝ :=
  betaSpectralRate β c0 n (betaOpenModes n E)

theorem betaSpectralRateCutoff_pos (β c0 : ℝ) (n : Nat) (E : ℝ)
    (hβ : 0 < β) (hc0 : 0 < c0) (hn : 0 < n)
    (hE : dirichletEigenvalue n 1 1 1 ≤ E) :
    0 < betaSpectralRateCutoff β c0 n E := by
  unfold betaSpectralRateCutoff
  exact betaSpectralRate_pos β c0 n _ hβ hc0 hn
    (betaOpenModes_nonempty hn hE)

/-- The weighted rate never exceeds the bare `β·c0`. -/
theorem betaWeightedRate_le (β c0 : ℝ) {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w : Ω → ℝ) (S : Finset Ω)
    (hβ : 0 ≤ β) (hc0 : 0 ≤ c0) (hw : ∀ i, 0 < w i) :
    betaWeightedRate β c0 w S ≤ β * c0 := by
  have htotal : 0 < ∑ i, w i := by
    exact Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have hsub : S.sum w ≤ ∑ i, w i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => le_of_lt (hw i))
  unfold betaWeightedRate
  rw [div_le_iff₀ htotal]
  nlinarith [hsub, mul_nonneg hβ hc0]

set_option linter.style.haveILetI false in
theorem betaSpectralRateCutoff_le (β c0 : ℝ) (n : Nat) (E : ℝ)
    (hβ : 0 ≤ β) (hc0 : 0 ≤ c0) (hn : 0 < n) :
    betaSpectralRateCutoff β c0 n E ≤ β * c0 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold betaSpectralRateCutoff betaSpectralRate
  apply betaWeightedRate_le
  · exact hβ
  · exact hc0
  · intro p
    exact betaSpectralWeight_pos n _ _ _

end PMAtoms
