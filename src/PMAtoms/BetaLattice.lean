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

/-- The one-dimensional Dirichlet term is monotone in the mode index. -/
lemma dirichletTerm_mono {n a a' : Nat} (hn : 0 < n)
    (ha : 1 ≤ a) (haa : a ≤ a') (ha' : a' ≤ n) :
    2 - 2 * Real.cos (Real.pi * (a : ℝ) / ((n : ℝ) + 1)) ≤
      2 - 2 * Real.cos (Real.pi * (a' : ℝ) / ((n : ℝ) + 1)) := by
  have hx0 : 0 ≤ Real.pi * (a : ℝ) / ((n : ℝ) + 1) := by positivity
  have hxy : Real.pi * (a : ℝ) / ((n : ℝ) + 1) ≤
      Real.pi * (a' : ℝ) / ((n : ℝ) + 1) := by
    gcongr
  have hyπ : Real.pi * (a' : ℝ) / ((n : ℝ) + 1) ≤ Real.pi := by
    have hle : (a' : ℝ) ≤ (n : ℝ) + 1 := by
      have : a' ≤ n + 1 := Nat.le_trans ha' (Nat.le_succ n)
      exact_mod_cast this
    calc
      Real.pi * (a' : ℝ) / ((n : ℝ) + 1)
          ≤ Real.pi * ((n : ℝ) + 1) / ((n : ℝ) + 1) := by gcongr
      _ = Real.pi := by field_simp
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx0 hyπ hxy
  linarith

/-- The Dirichlet eigenvalue is monotone in the three mode indices. -/
lemma dirichletEigenvalue_mono {n a b c a' b' c' : Nat} (hn : 0 < n)
    (ha : 1 ≤ a) (haa : a ≤ a') (ha' : a' ≤ n)
    (hb : 1 ≤ b) (hbb : b ≤ b') (hb' : b' ≤ n)
    (hc : 1 ≤ c) (hcc : c ≤ c') (hc' : c' ≤ n) :
    dirichletEigenvalue n a b c ≤ dirichletEigenvalue n a' b' c' := by
  unfold dirichletEigenvalue
  have h1 := dirichletTerm_mono (n := n) hn ha haa ha'
  have h2 := dirichletTerm_mono (n := n) hn hb hbb hb'
  have h3 := dirichletTerm_mono (n := n) hn hc hcc hc'
  linarith

/-- The lowest mode has the smallest eigenvalue. -/
lemma dirichletEigenvalue_lowest_le {n a b c : Nat} (hn : 0 < n)
    (ha : 1 ≤ a) (ha' : a ≤ n)
    (hb : 1 ≤ b) (hb' : b ≤ n)
    (hc : 1 ≤ c) (hc' : c ≤ n) :
    dirichletEigenvalue n 1 1 1 ≤ dirichletEigenvalue n a b c :=
  dirichletEigenvalue_mono (n := n) hn (by norm_num) ha ha'
    (by norm_num) hb hb' (by norm_num) hc hc'

lemma dirichletEigenvalue_perm12 (n a b c : Nat) :
    dirichletEigenvalue n a b c = dirichletEigenvalue n b a c := by
  unfold dirichletEigenvalue
  ring

lemma dirichletEigenvalue_perm13 (n a b c : Nat) :
    dirichletEigenvalue n a b c = dirichletEigenvalue n c b a := by
  unfold dirichletEigenvalue
  ring

/-- Any non-lowest mode is at least as high as `(2,1,1)`; the first gap. -/
lemma dirichletEigenvalue_ge_next {n a b c : Nat} (hn : 1 < n)
    (ha : 1 ≤ a) (ha' : a ≤ n) (hb : 1 ≤ b) (hb' : b ≤ n)
    (hc : 1 ≤ c) (hc' : c ≤ n)
    (h : a ≠ 1 ∨ b ≠ 1 ∨ c ≠ 1) :
    dirichletEigenvalue n 2 1 1 ≤ dirichletEigenvalue n a b c := by
  rcases h with ha_ne | hb_ne | hc_ne
  · have ha2 : 2 ≤ a := by omega
    exact dirichletEigenvalue_mono (n := n) (a := 2) (b := 1) (c := 1)
      (a' := a) (b' := b) (c' := c) (by omega) (by norm_num) ha2 ha'
      (by norm_num) hb hb' (by norm_num) hc hc'
  · have hb2 : 2 ≤ b := by omega
    have hmono := dirichletEigenvalue_mono (n := n) (a := 1) (b := 2) (c := 1)
      (a' := a) (b' := b) (c' := c) (by omega) (by norm_num) ha ha'
      (by norm_num) hb2 hb' (by norm_num) hc hc'
    rw [← dirichletEigenvalue_perm12] at hmono
    exact hmono
  · have hc2 : 2 ≤ c := by omega
    have hmono := dirichletEigenvalue_mono (n := n) (a := 1) (b := 1) (c := 2)
      (a' := a) (b' := b) (c' := c) (by omega) (by norm_num) ha ha'
      (by norm_num) hb hb' (by norm_num) hc2 hc'
    rw [← dirichletEigenvalue_perm13] at hmono
    exact hmono

/-- Every Dirichlet eigenvalue on a cube is at most `12`. -/
lemma dirichletEigenvalue_le_twelve (n a b c : Nat) :
    dirichletEigenvalue n a b c ≤ 12 := by
  unfold dirichletEigenvalue
  have h1 := Real.neg_one_le_cos (Real.pi * (a : ℝ) / ((n : ℝ) + 1))
  have h2 := Real.neg_one_le_cos (Real.pi * (b : ℝ) / ((n : ℝ) + 1))
  have h3 := Real.neg_one_le_cos (Real.pi * (c : ℝ) / ((n : ℝ) + 1))
  nlinarith

/-- If the cutoff is above `12`, every mode of any cube is open. -/
theorem betaOpenModes_eq_univ_of_twelve_le {n : Nat} {E : ℝ} (hE : 12 ≤ E) :
    betaOpenModes n E = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro p
  simp only [betaOpenModes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_trans
    (dirichletEigenvalue_le_twelve n (p.1.val+1) (p.2.1.val+1) (p.2.2.val+1)) hE

/-- If the cutoff lies between the lowest and next eigenvalue, exactly the
lowest mode is open. -/
theorem betaOpenModes_eq_singleton_of_gap {n : Nat} {E : ℝ} (hn : 1 < n)
    (hlo : dirichletEigenvalue n 1 1 1 ≤ E)
    (hhi : E < dirichletEigenvalue n 2 1 1) :
    betaOpenModes n E =
      {(⟨0, by omega⟩, (⟨0, by omega⟩, ⟨0, by omega⟩))} := by
  ext p
  rcases p with ⟨a, b, c⟩
  simp only [betaOpenModes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hE
    by_contra hne
    have hdisj : a.val + 1 ≠ 1 ∨ b.val + 1 ≠ 1 ∨ c.val + 1 ≠ 1 := by
      by_contra h
      push Not at h
      apply hne
      ext <;> norm_num
      all_goals omega
    have hge := dirichletEigenvalue_ge_next (n := n) hn
      (a := a.val + 1) (b := b.val + 1) (c := c.val + 1)
      (Nat.succ_pos _) (Nat.succ_le_of_lt a.isLt)
      (Nat.succ_pos _) (Nat.succ_le_of_lt b.isLt)
      (Nat.succ_pos _) (Nat.succ_le_of_lt c.isLt) hdisj
    linarith
  · intro hp
    rcases hp with ⟨rfl, rfl, rfl⟩
    norm_num
    exact hlo

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
