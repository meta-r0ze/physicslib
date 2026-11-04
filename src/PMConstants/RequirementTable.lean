import PMConstants.GaugeLedgers
import PMConstants.SectorLinks

/-!
# The requirement table from the representation and the forced charges

`GaugeLedgers` read its requirement table from Paper V. This module derives the table's columns
from data Paper III already uses: each channel's type (`Q, u, d, L, e, ν`), the colour and
isospin dimensions of each type (the multiplicities `6, 3, 3, 2, 1, 1` of `hyperIndex`), and the
hypercharges forced by flux, one unit link and a neutral sterile channel
(`SectorLinks.forced_by_links`).

* `colour_column`: a channel routes through the colour bulk exactly when its type is a colour
  triplet.
* `active_column`: a channel couples to the active temporal boundary exactly when its type is an
  SU(2) doublet, the states the weak links act on (left-handed sector, `LinkMass`).
* `hyper_column`: for any charges satisfying the forcing premises, a channel carries nonzero
  hypercharge exactly when it is not the sterile channel 16. Hypercharge's requirement is these
  fifteen plus the sterile reference against which flux is measured: all sixteen payloads.

The ledgers of `GaugeLedgers` then depend only on representation data already in Paper III and
on one stated premise: the sterile channel is the flux reference (Paper V), which the W mass
supports (`ResourceLedger.sterile_counted`).
-/

namespace PMConstants.RequirementTable
open PMConstants Hypercharge

inductive Ty | Q | u | d | L | e | n
  deriving DecidableEq

/-- Paper V's channel order: 1–6 `Q` (u_L, d_L), 7–9 `u`, 10–12 `d`, 13–14 `L`, 15 `e`, 16 `ν`. -/
def ty (i : Fin 16) : Ty :=
  if i.val < 6 then .Q else if i.val < 9 then .u else if i.val < 12 then .d
  else if i.val < 14 then .L else if i.val = 14 then .e else .n

def colourDim : Ty → ℕ | .Q => 3 | .u => 3 | .d => 3 | _ => 1
def isoDim : Ty → ℕ | .Q => 2 | .L => 2 | _ => 1

def hyper (Y : Charges) : Ty → ℚ
  | .Q => Y.q | .u => Y.u | .d => Y.d | .L => Y.l | .e => Y.e | .n => Y.n

theorem colour_column (i : Fin 16) :
    ResourceLedger.colourBulk i = true ↔ colourDim (ty i) = 3 := by
  fin_cases i <;> decide

theorem active_column (i : Fin 16) :
    ResourceLedger.activeBoundary i = true ↔ isoDim (ty i) = 2 := by
  fin_cases i <;> decide

theorem multiplicities :
    (Finset.univ.filter fun i => ty i = .Q).card = 6 ∧
    (Finset.univ.filter fun i => ty i = .u).card = 3 ∧
    (Finset.univ.filter fun i => ty i = .d).card = 3 ∧
    (Finset.univ.filter fun i => ty i = .L).card = 2 ∧
    (Finset.univ.filter fun i => ty i = .e).card = 1 ∧
    (Finset.univ.filter fun i => ty i = .n).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem hyper_column (Y : Charges) (hf : Flux Y) (hl : SectorLinks.OneLink Y 1) (hn : Y.n = 0)
    (i : Fin 16) : hyper Y (ty i) ≠ 0 ↔ i.val ≠ 15 := by
  have hY := SectorLinks.forced_by_links Y hf hl hn
  subst hY
  fin_cases i <;> simp [ty, hyper, standard]

end PMConstants.RequirementTable
