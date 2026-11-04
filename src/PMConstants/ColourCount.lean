import PMConstants.StrongLedgerTest
import PMConstants.GaugeStiffness

/-!
# What fixes the colour ledger: an exploration

`StrongLedgerTest` reads the strong coupling as `α_s = α N_sys / L₃`, in the same channel-weighted
units that give `s = Δ/N_sys`. This module records what the data allow for `L₃` and which
substrate counts land there. None of them is yet derived from a colour refresh rule.

* `ledger_window`: if `α N_sys/L₃` is within 3σ of `0.1180 ± 0.0009`, then `11.66 < L₃ < 12.21`.
* Candidates inside the window (`candidates_in_window`):
  - `12`, the number of positive roots of D₄ (`positive_roots`): one refresh per link
    direction, the colour analogue of one weak refresh per clock tick (`Δ`);
  - `16η − 4 ≈ 11.907`, payload channels less one per dimension;
  - the paper's `N_sys/(16η + 1/4) ≈ 11.940`.
  `11` and `13` are outside. The window has width about 0.55, so three structurally different
  rules fit; the data cannot choose among them.
* `link_triangles`: each D₄ link lies on 8 minimal triangles (Paper II's plaquettes).
  A per-plaquette refresh rule would give a multiple of 8, not 12.

Which rule persists requires the colour refresh process itself: what is refreshed, how often,
and at which scale the ledger equals the running coupling (the window is about ±5% in scale
around `M_Z` at one loop, so every candidate places the matching scale at the link mass).
-/

noncomputable section
namespace PMConstants.ColourCount
open PMConstants CertifiedConstants StrongLedgerTest

theorem ledger_window {L : ℝ} (hL : 0 < L) (h : |α * footprint / L - 0.1180| < 3 * 0.0009) :
    11.66 < L ∧ L < 12.21 := by
  have hb := alpha_footprint_bounds
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · by_contra hc; push Not at hc
    have : α * footprint / 11.66 ≤ α * footprint / L :=
      div_le_div_of_nonneg_left (by linarith [hb.1]) hL hc
    have h3 : (0.1207 : ℝ) < α * footprint / 11.66 := by
      rw [lt_div_iff₀ (by norm_num)]; linarith [hb.1]
    linarith
  · by_contra hc; push Not at hc
    have : α * footprint / L ≤ α * footprint / 12.21 :=
      div_le_div_of_nonneg_left (by linarith [hb.1]) (by norm_num) hc
    have h3 : α * footprint / 12.21 < (0.1153 : ℝ) := by
      rw [div_lt_iff₀ (by norm_num)]; linarith [hb.2]
    linarith

theorem candidates_in_window :
    (11.66 : ℝ) < 12 ∧ (11.66 : ℝ) < 16 * overhead - 4 ∧ 16 * overhead - 4 < 12.21 ∧
      (11.66 : ℝ) < GaugeStiffness.strongWorkload ∧ GaugeStiffness.strongWorkload < 12.21 ∧
      ¬ ((11.66 : ℝ) < 11) ∧ ¬ ((13 : ℝ) < 12.21) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [overhead, GaugeStiffness.strongWorkload, footprint]

/-! ## D₄ counts -/

/-- Coordinates in `{-1, 0, 1}`. -/
def vec (k : Fin 4 → Fin 3) (i : Fin 4) : ℤ := (k i : ℤ) - 1

def dot (a b : Fin 4 → ℤ) : ℤ := ∑ i, a i * b i

def roots : Finset (Fin 4 → Fin 3) := Finset.univ.filter fun k => dot (vec k) (vec k) = 2

/-- First nonzero coordinate positive. -/
def positive (k : Fin 4 → Fin 3) : Prop :=
  ∃ i : Fin 4, vec k i = 1 ∧ ∀ j : Fin 4, j < i → vec k j = 0

instance : DecidablePred positive := fun k => by unfold positive; infer_instance

theorem root_count : roots.card = 24 := by decide +kernel

theorem positive_roots : (roots.filter positive).card = 12 := by decide +kernel

/-- The link `e₀ + e₁`. -/
def α0 : Fin 4 → Fin 3 := ![2, 2, 1, 1]

/-- Roots `β` with `α₀ − β` also a root: the triangles through the link `α₀`. -/
theorem link_triangles :
    (roots.filter fun k => ∃ m ∈ roots, ∀ i, vec α0 i - vec k i = vec m i).card = 8 := by
  decide +kernel

end PMConstants.ColourCount
