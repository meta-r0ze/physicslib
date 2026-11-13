import PMConstants.ReadoutAccounting
import PersistenceMechanics.LawSelection
import PMSubstrate.ChannelSymmetry

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
survival model is the remaining input of this route.

**A second route needs no such identification.** Under Closure the preparation law is defined
inside the substrate, so it is invariant under the substrate's own symmetries, and those act
transitively on the channels (`PMSubstrate.ChannelSymmetry.invariant_constant`: an invariant law
takes one value on all 32 channels). `symmetric_preparation_uniform`: a law on the packet that
takes one value everywhere is the uniform law. `packet_preparation_uniform` wires it: the packet's
channels are the vector-class carriers of the two sectors among the 32 (`toChannel`), so a packet
law proportional to an invariant channel law is uniform. This is the premise Toll's channel measure already
uses (`ChannelSymmetry.invariant_uniform`); the survival route above then agrees with it.
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

/-- **A symmetric preparation is uniform.** A law on the packet channels that takes one value
everywhere (as Closure and the transitive channel symmetries force) is the uniform law. -/
theorem symmetric_preparation_uniform (p : Ch → ℝ) (hconst : ∀ c d, p c = p d)
    (hsum : ∑ c, p c = 1) : p = uniform := by
  funext c
  have h : ∑ d, p d = (Fintype.card Ch : ℝ) * p c := by
    rw [Finset.sum_congr rfl (fun d _ => hconst d c)]; simp
  have hc : (0 : ℝ) < Fintype.card Ch := by exact_mod_cast Fintype.card_pos
  rw [hsum] at h
  unfold uniform
  field_simp
  linarith

/-- The packet's channels among the 32 substrate channels: the vector-class carriers of the two
sectors (`chanTable` entries `0–7` and `16–23`), in `channelIndex` order. -/
def embed16 (i : Fin 16) : Fin 32 :=
  ⟨if i.val < 8 then i.val else i.val + 8, by have := i.isLt; split_ifs <;> omega⟩

def toChannel (c : Ch) : Bool × PMSubstrate.ChannelSymmetry.V4 :=
  PMSubstrate.ChannelSymmetry.chanTable (embed16 (PacketGaugeActions.channelIndex c))

theorem toChannel_mem : ∀ c : Ch, toChannel c ∈ PMSubstrate.ChannelSymmetry.channels := by
  decide +kernel

/-- **The packet preparation is uniform under Closure.** If the channel law `P` on the 32
substrate channels is invariant under the substrate's symmetries, and the packet's law is
proportional to `P` on the packet's channels, the packet's law is uniform. -/
theorem packet_preparation_uniform (P : Bool × PMSubstrate.ChannelSymmetry.V4 → ℝ)
    (hP : ∀ i, ∀ x ∈ PMSubstrate.ChannelSymmetry.channels,
      P (PMSubstrate.ChannelSymmetry.gen i x) = P x)
    (p : Ch → ℝ) (k : ℝ) (hp : ∀ c, p c = k * P (toChannel c)) (hsum : ∑ c, p c = 1) :
    p = uniform := by
  refine symmetric_preparation_uniform p (fun c d => ?_) hsum
  rw [hp c, hp d, PMSubstrate.ChannelSymmetry.invariant_constant P hP _ (toChannel_mem c),
    PMSubstrate.ChannelSymmetry.invariant_constant P hP _ (toChannel_mem d)]

end PMConstants.PreparationSelection
