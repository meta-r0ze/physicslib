import PersistenceMechanics.Selection
import PersistenceMechanics.Gibbs
import PersistenceMechanics.LawSelection

/-!
# Persistence selection, reused from the framework (`PM/lean`)

The persistence-selection machinery is **already proved in `PM/lean`**
(`PersistenceMechanics`): survival composition (`ExponentialFilter`), the cost-proportional
hazard (`HazardForm`), the selection principle (`Selection`, *Proposition:
Selection by Operational Action*), the finite Gibbs / zero-temperature limit
(`Gibbs`) and law selection (`LawSelection`). This module does **not** re-prove
any of it; it states the cosmology-facing corollaries and is where Paper VI points.

* `higher_rate_vanishes` — a candidate with a higher asymptotic cost rate has
  survivor share tending to `0`, so the persistent (least-rate) option is what
  remains. This is the "one works forever, the other dies" selection, on constant
  rates.
* `least_rate_takes_over` — the least-rate candidates take over the surviving
  ensemble (`Selection.selection_principle`).
* `uniform_law_selected` — among candidate laws, the uniform law survives
  average-cost selection (`LawSelection.selected_uniform_average`).

**Scope.** These select a *state/law* among an explicit family with a cost. They
do not manufacture the coarse-grained cosmology: `L(a)`, perturbations, a metric
or an entropy law are not options the survival law can rank until a dynamics
defines the family. So persistence closes state/readout and law choices, not the
missing background dynamics.
-/

noncomputable section
namespace PMCosmology.PersistenceSelection
open Filter Topology Finset

/-- **A higher-rate candidate vanishes.** If candidate `i` has asymptotic cost
rate `s i` and some `j` is cheaper (`s j < s i`), then `i`'s share of the
surviving ensemble tends to `0`. On constant rates this is the "one survives, the
other dies" argument. -/
theorem higher_rate_vanishes {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {β : ℝ} (hβ : 0 < β) (s : ι → ℝ)
    {i j : ι} (hij : s j < s i) :
    Tendsto (fun T => PersistenceMechanics.Selection.survivor p β (fun k => s k * T) i)
      atTop (𝓝 0) :=
  PersistenceMechanics.Selection.selection hp hβ (fun k T => s k * T) s
    (fun _ => by simp) hij

/-- **The least-rate candidates take over** the surviving ensemble. -/
theorem least_rate_takes_over {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {β : ℝ} (hβ : 0 < β) (s : ι → ℝ) :
    Tendsto (fun T => ∑ i ∈ univ.filter
        (fun i => s i = univ.inf' univ_nonempty s),
        PersistenceMechanics.Selection.survivor p β (fun k => s k * T) i) atTop (𝓝 1) :=
  PersistenceMechanics.Selection.selection_principle hp hβ (fun k T => s k * T) s
    (fun _ => by simp)

/-- **Law selection.** Among candidate laws scored by average return cost, the
uniform law is the survivor (`LawSelection.selected_uniform_average`). This is the
"there is no free choice of law" statement, within an explicit law family. -/
theorem uniform_law_selected {Ω : Type*} [Fintype Ω] [Nonempty Ω] {ι : Type*}
    [Fintype ι] [Nonempty ι] (L : ι → Ω → ℝ)
    (hL : ∀ i, PersistenceMechanics.LawSelection.PosLaw (L i))
    (hu : ∃ i, L i = PersistenceMechanics.LawSelection.uniform) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {β : ℝ} (hβ : 0 < β) (S : ι → ℝ → ℝ)
    (hS : ∀ i, Tendsto
      (fun T => (S i T - PersistenceMechanics.LawSelection.averageRate (L i) * T) / T)
      atTop (𝓝 0)) :
    Tendsto (fun T => ∑ i ∈ univ.filter
        (fun i => L i = PersistenceMechanics.LawSelection.uniform),
        PersistenceMechanics.Selection.survivor w β (fun k => S k T) i) atTop (𝓝 1) :=
  PersistenceMechanics.LawSelection.selected_uniform_average L hL hu hw hβ S hS

end PMCosmology.PersistenceSelection
