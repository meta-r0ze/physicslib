import PMConstants.StrongLedgerTest
import PMConstants.GaugeStiffness

/-!
# What fixes the colour ledger: an exploration

`StrongLedgerTest` reads the strong coupling as `α_s  = α N_sys / L₃`, in the same channel-weighted
units that give `s = Δ/N_sys`. This module records which substrate counts can supply `L₃`. None of
them is derived from a colour refresh rule here; `ColourChannels` derives the one that persists.

* Candidates for `L₃`:
  - `12`, the number of positive roots of D₄ (`positive_roots`): one refresh per link
    direction, the colour analogue of one weak refresh per clock tick (`Δ`);
  - `16η − 4`, payload channels less one per dimension;
  - the paper's `N_sys/(16η + 1/4)` (`GaugeStiffness.strongWorkload`).
  The three are structurally different and numerically close, so no comparison separates them;
  the rule does.
* `link_triangles`: each D₄ link lies on 8 minimal triangles (Paper II's plaquettes).
  A per-plaquette refresh rule would give a multiple of 8, not 12.

The measured window and which candidates sit in it are comparisons; they live in
`tools/e8p/E8PConstants/PMConstants/StrongLedgerPulls.lean`.

Which rule persists requires the colour refresh process itself: what is refreshed, how often,
and at which scale the ledger equals the running coupling (the window is about ±5% in scale
around `M_Z` at one loop, so every candidate places the matching scale at the link mass).
-/
noncomputable section
namespace PMConstants.ColourCount
open PMConstants CertifiedConstants StrongLedgerTest

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
