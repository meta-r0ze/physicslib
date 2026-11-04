import PMConstants.ReadoutAccounting
import PersistenceMechanics.LawSelection

/-!
# The uniform preparation as an instance of law selection

`ReadoutAccounting.selected_is_uniform` names the uniform law on the sixteen carriers. This module
instantiates the framework theorem that selects it.

* `rescue`: the nonuniform per-carrier law `(6,3,6,3,2,2)/73` on `(Q, u, d, L, e, ν)` carriers,
  the preparation that would rescue the raw ledger reading. `rescue_law`: it is
  a strictly positive law; `rescue_ne_uniform`: it is not the uniform one.
* `candidates`: the family `{uniform, rescue}` on the actual packet channels.
* `preparation_selected`: with positive initial weights and survival actions growing at each law's
  average rate (`PersistenceMechanics.LawSelection.averageRate`, the reference visiting every carrier
  equally often), the surviving ensemble concentrates on the uniform law
  (`PersistenceMechanics.LawSelection.selected_uniform_average`).
* `any_family_selects_uniform`: the same for every finite positive family containing the uniform
  law.

Premises (now explicit, as the framework theorem states them): the candidates are positive laws on
the carriers, survival is the framework's hazard model with the average-rate reading, and the
actions grow at that rate. The physical identification of the carrier preparation process with this
survival model is the remaining input.
-/

noncomputable section
namespace PMConstants.PreparationSelection
open PMConstants PersistenceMechanics.LawSelection GaugeReadoutWeights Filter Topology Finset

abbrev Ch := PacketGaugeActions.Channels

def typeWeight : RequirementTable.Ty → ℝ
  | .Q => 6 | .u => 3 | .d => 6 | .L => 3 | .e => 2 | .n => 2

def rescue : Ch → ℝ := fun c => typeWeight (channelType c) / 73

lemma sum_channels (f : Ch → ℝ) :
    ∑ c, f c = ∑ q : PacketGaugeActions.Q, f (.inl q) + ∑ q : PacketGaugeActions.Q, f (.inr (.inl q)) +
      ∑ s : Fin 2, f (.inr (.inr (.inl s))) + ∑ s : Fin 2, f (.inr (.inr (.inr s))) := by
  simp only [Fintype.sum_sum_type]; ring

theorem rescue_law : PosLaw rescue := by
  refine ⟨fun c => ?_, ?_⟩
  · unfold rescue; rcases c with q | q | s | s <;>
      [skip; (obtain ⟨a, t⟩ := q; fin_cases t); skip; fin_cases s] <;>
      simp [channelType, typeWeight]
  · rw [sum_channels]
    simp [rescue, channelType, typeWeight, Fintype.sum_prod_type, Fin.sum_univ_succ]
    norm_num

theorem rescue_ne_uniform : rescue ≠ uniform := by
  intro h
  have := congrFun h (.inl (0, 0))
  have hc : Fintype.card Ch = 16 := by decide
  simp [rescue, uniform, channelType, typeWeight, hc] at this
  norm_num at this

def candidates : Fin 2 → Ch → ℝ := ![uniform, rescue]

open Classical in
/-- **The selected preparation.** -/
theorem preparation_selected {w : Fin 2 → ℝ} (hw : ∀ i, 0 < w i) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun T => ∑ i ∈ univ.filter (fun i => candidates i = uniform),
      PersistenceMechanics.Selection.survivor w β (fun k => averageRate (candidates k) * T) i)
      atTop (𝓝 1) := by
  refine selected_uniform_average candidates (fun i => ?_) ⟨0, rfl⟩ hw hβ _ (fun i => ?_)
  · fin_cases i
    · exact uniform_law
    · exact rescue_law
  · simp only [sub_self, zero_div]; exact tendsto_const_nhds

open Classical in
theorem any_family_selects_uniform {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → Ch → ℝ)
    (hL : ∀ i, PosLaw (L i)) (hu : ∃ i, L i = uniform) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun T => ∑ i ∈ univ.filter (fun i => L i = uniform),
      PersistenceMechanics.Selection.survivor w β (fun k => averageRate (L k) * T) i) atTop (𝓝 1) :=
  selected_uniform_average L hL hu hw hβ _ (fun i => by
    simp only [sub_self, zero_div]; exact tendsto_const_nhds)

end PMConstants.PreparationSelection
