import PMAction.MassInsertion
import PMElementaryParticles.EPLabelGen

/-!
# Generation masses: what the upstream mass structure fixes for EP

EP's masses come from `PMAction`'s mass structure, not from the declared ledgers
(`LeptonMasses`, `QuarkMasses`, `TierLedger`, which stay comparison premises).

A generation puts one glue class on each wall. Its label is the third class
(`PMAction.GenerationLabel`). A generation's own mass joins its two walls, so it needs an
insertion of the label class (`PMAction.MassInsertion.bilinear_gap`). The reference sits in the
vector class `v` (`PMConstants.CarrierRepresentation`). The generation with label `v` is the
one whose walls carry neither copy of `v` (`MassInsertion.label_is_reference_iff`). Its insertion is
a vector displacement, which can stay off the reference axis; the other two generations'
insertions are spinor displacements, which always touch it (`PMFlavor.ExchangeAxis`), so they pass
through the reference node (`PMFlavor.NodeElimination`). So one generation is heavy and two are
light.

This module places EP's generations in that structure.

* `toGlue`: EP's library classes as glue classes (`ChannelPlacement`: class `0` is the vector
  coset `(0,1)`, `1` is `(1,0)`, `2` is `(1,1)`).
* `label_eq_key`: the label of EP generation `g`'s two walls (`wallClass g true`,
  `wallClass g false`) is `g`'s own glue class. EP's generation is the upstream label.
* `heavy_iff`: EP generation `g` has the label `v` (no wall in `v`) exactly when `g = 0`.
* `heavy_key`: that generation is the glue key `(0,1)`, the vector coset that carries the clock.

So EP generation `(0,1)` is the heavy one (third generation: τ, t, b). This is upstream's
ordering, set by where the reference sits. It is not the ledgers' reading of generation `0` as
"tier 0".

Open upstream (`PMAction/TODO.md`), so no mass values here: the direct zero-mode term that joins
the two walls is not in the wall Hamiltonian; the size of the node factor for a mass; the split
of the two light generations (degenerate at this order, `MassInsertion.light_pair_degenerate`);
and the lepton reading (lepton-axis states are one leg from the node, `NodeElimination`).
-/

namespace PMElementaryParticles.GenerationMasses

open PMElementaryParticles.ControlledGluedRegister PMElementaryParticles.EPSpine
open PMElementaryParticles.EPLabelGen PMAction.GenerationLabel

/-- EP's library classes as glue classes (`ChannelPlacement`). -/
def toGlue : Fin 3 → Glue
  | 0 => (0, 1)
  | 1 => (1, 0)
  | 2 => (1, 1)

/-- The reference's class: the vector class. -/
def refClass : Glue := toGlue 0

/-- **EP's generation is the upstream label.** The label of generation `g`'s two walls is `g`. -/
theorem label_eq_key : ∀ g : Fin 3,
    label (toGlue (wallClass g true)) (toGlue (wallClass g false)) = toGlue g := by decide

/-- **The heavy generation.** EP generation `g` carries the reference's class on neither wall
exactly when `g = 0`. -/
theorem heavy_iff : ∀ g : Fin 3,
    (toGlue (wallClass g true) ≠ refClass ∧ toGlue (wallClass g false) ≠ refClass) ↔ g = 0 := by
  decide

/-- The heavy generation has label `v`, by `MassInsertion.label_is_reference_iff`. -/
theorem heavy_label : label (toGlue (wallClass 0 true)) (toGlue (wallClass 0 false)) = refClass := by
  decide

/-- The heavy generation is the glue key `(0,1)`, the vector coset that carries the clock. -/
theorem heavy_key : ∀ g : Generation, genIndex g = 0 ↔ g.1 = (0, 1) := by decide

end PMElementaryParticles.GenerationMasses
