import PMConstants.Values
import Lean

/-!
# Constant provenance — the degrees-of-freedom ledger

The force of the PM result rests on **how many headline constants are predictions vs
comparisons**. This module labels each canonical constant by where it comes from, and points at the
actual declaration (a `Lean.Name`, so a non-existent reference fails to compile, and the table is
genuinely checked):

* `derived` — forced by the E8 integers and a pillar reading, with no free parameter;
* `conditional` — a consequence of a stated physical hypothesis (the EM matching law, a
  normalization, or an independent dressing);
* `anchor` — an external unit / measured input.

The point of the ledger: the *only* anchor is the electron mass; every other headline constant is
derived or a named conditional. So the comparison is not a fit — there is one dimensionful input and
a fixed integer substrate behind the dimensionless predictions.

(The companion comparison-level hypotheses — matching law, physical measure, state space — are
listed in `OPEN-PROBLEMS.md`; here we label the constants they act on.)
-/

noncomputable section
namespace PMConstants.Provenance

/-- Where a constant comes from. -/
inductive Source
  /-- Forced by the E8 integers and a pillar reading; no free parameter. -/
  | derived
  /-- A consequence of a stated physical hypothesis. -/
  | conditional
  /-- An external unit / measured input. -/
  | anchor
  deriving DecidableEq, Repr

/-- One row of the ledger: the constant, its provenance, and the declaration that fixes it. -/
structure Row where
  /-- The constant, as displayed. -/
  name : String
  /-- Where it comes from. -/
  source : Source
  /-- The declaration that fixes it (a real reference, checked at elaboration). -/
  decl : Lean.Name

/-- The canonical constants of `PMConstants.Values`, labelled by provenance. -/
def table : List Row :=
  [ ⟨"α",          .conditional, ``Values.alpha⟩
  , ⟨"α_s",        .conditional, ``Values.strong⟩
  , ⟨"sin²θ_W",    .conditional, ``Values.weakFraction⟩
  , ⟨"λ",          .derived,     ``Values.scalar⟩
  , ⟨"y_e",        .conditional, ``Values.electronYukawa⟩
  , ⟨"m_e (GeV)",  .anchor,      ``Values.electronGeV⟩
  , ⟨"v",          .derived,     ``Values.vev⟩
  , ⟨"m_H",        .derived,     ``Values.higgsMass⟩
  , ⟨"G_F",        .derived,     ``Values.fermi⟩
  , ⟨"g_W²",       .derived,     ``Values.weakSquared⟩
  , ⟨"g_Y²",       .derived,     ``Values.hyperchargeSquared⟩
  , ⟨"g_3²",       .derived,     ``Values.strongSquared⟩ ]

/-- The ledger names each headline constant once. -/
theorem table_nodup : (table.map Row.name).Nodup := by decide

/-- **One anchor.** Exactly one headline constant is an external input — the electron mass. -/
theorem anchor_count : (table.filter (fun r => r.source = .anchor)).length = 1 := by decide

/-- Every other constant is derived or a named conditional (twelve headline constants in all). -/
theorem table_length : table.length = 12 := by decide

end PMConstants.Provenance
