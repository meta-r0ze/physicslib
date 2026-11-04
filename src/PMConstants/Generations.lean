import PMAction.CarrierCost

/-!
# Three generations as the pairs of distinct glue classes

A generation's sixteen channels are two domain-wall sectors of eight carriers each. Paper II's
packet of two glue classes has sixteen carriers (`PMAction.CarrierCost.packet_card`).

* `same_class_loses`: if both sectors use the same class, the vector-only readout is not
  injective: a left carrier and a right carrier coincide as substrate vectors. Distinct classes
  make this particular readout injective (`PMAction.CarrierCost.packet_vector_injective`).
  Requiring this readout to preserve every packet distinction therefore requires distinct classes.
  Conservation alone does not impose that readout: keeping a wall tag preserves equal-class
  packets (`GenerationEncoding.equal_class_boundary`).
* The pair-type classification treats the two sector assignments as the same type. This is
  a quotient contract; a sector-exchange symmetry by itself does not erase a wall label from
  physical states. `SectorExchange` supplies conditional mass algebra, not this identification.
* `three_pairs`: there are exactly three unordered pairs of distinct classes among the three
  nontrivial D₄ glue classes. No fourth pair exists.

Thus there are exactly three unordered distinct-class pair types under the vector-faithful,
sector-unordered packet contract. Identifying these types with all physical generations remains
a model obligation. They overlap as native carrier sets: see `GenerationEncoding` for the exact
capacity and linear-amplitude bounds when their generation distinctions are retained.
-/

namespace PMConstants.Generations
open PMAction PMAction.CarrierEvents PMAction.CarrierCost

theorem same_class_loses (a : Fin 3) :
    ¬ Function.Injective (@packetVector a a) := by
  intro h
  have : Nonempty (Carrier a) := Fintype.card_pos_iff.mp (by rw [carrier_card]; norm_num)
  obtain ⟨v⟩ := (inferInstance : Nonempty (Carrier a))
  have := h (a₁ := Sum.inl v) (a₂ := Sum.inr v) rfl
  cases this

theorem three_pairs :
    (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 < p.2).card = 3 := by decide

theorem packets_sixteen (a b : Fin 3) : Fintype.card (Packet a b) = 16 := packet_card a b

end PMConstants.Generations
