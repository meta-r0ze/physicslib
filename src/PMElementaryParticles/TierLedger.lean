import PMElementaryParticles.ProtocolDynamics

/-! **Tier ledger.**

The four geometric tiers are `Δ⁰…Δ³`.  The declared [Premise] ledger assigns each base protocol a subset:

```
up-type       0, 2, 3
down-type     0, 1, 2
electron      0, 1, 2
neutrino      0, 1, 2
```

The per-tier mass/decay status is a provenance ledger, not a derivation.  A
status records what the current library proves: `e8`, `comparison`, `partial`,
`blocked`, `notModeled`, or `stable`.

**Legacy audit status.** The tier sets are retained as a declared ledger and are
not derived by the persistence rebuild. The bit-ring trace has no
address-to-tier bit. Status: consistent premise, not contradicted.

The isolated-excitation trace books a label Toll on a 43-tick receiver period.
It carries no address-to-tier bit, so it does not replace this assignment.
The tier sets stay premises; `wireTier` still takes the identification as an
explicit input.

## Step counts checked against the tier hierarchy

The vector, spinor and conjugate-spinor signatures are `(7,7,2)`, `(4,4,0)` and `(4,4,8)`.
Each triple counts forward, backward and silent crossings.

The step statistics on one 43-ring cannot give the hierarchy. Every coset has forward = backward, so a uniform walk has no
drift. Its period cost scales with `1/p_move` (`7/8`, `1`, `1/2`): ratios at
most `2`. A no-backtrack period scales as `p_fwd^43`: ratios `(8/7)^43 ≈ 312`
and `(7/4)^43 ≈ 2.8×10¹⁰`, not powers of `Δ`. The ledgers need the leading
power `Δⁿ` (point, line, area, volume), so the rule must give each program a
whole number `n`. It cannot depend on the generation only: lepton and down
tiers are `{0,1,2}` but up tiers are `{0,2,3}` (`TierLedger.tiersFor`).
-/

noncomputable section
namespace PMElementaryParticles.TierLedger

open PMElementaryParticles.ProtocolInventory
open PMElementaryParticles.ProtocolDynamics

/-- Provenance status for a tier row. -/
inductive Provenance
  | e8
  | comparison
  | partialE8
  | blocked
  | notModeled
  | stable
  deriving DecidableEq, Repr

def t0 : Tier := ⟨0, by decide⟩
def t1 : Tier := ⟨1, by decide⟩
def t2 : Tier := ⟨2, by decide⟩
def t3 : Tier := ⟨3, by decide⟩

/-- Allowed tiers for up-type quarks. -/
def upTiers : List Tier := [t0, t2, t3]

/-- Allowed tiers for down-type quarks. -/
def downTiers : List Tier := [t0, t1, t2]

/-- Allowed tiers for the electron protocol. -/
def electronTiers : List Tier := [t0, t1, t2]

/-- Allowed tiers for the neutrino protocol. -/
def neutrinoTiers : List Tier := [t0, t1, t2]

/-- [Premise] The declared subset of a base protocol. -/
def tiersFor : BaseProtocol → List Tier
  | .up => upTiers
  | .down => downTiers
  | .electron => electronTiers
  | .neutrino => neutrinoTiers

theorem upTiers_length : upTiers.length = 3 := rfl
theorem downTiers_length : downTiers.length = 3 := rfl
theorem electronTiers_length : electronTiers.length = 3 := rfl
theorem neutrinoTiers_length : neutrinoTiers.length = 3 := rfl

/-- [Premise] Assignment of the three wire addresses for the selected protocol. -/
abbrev WireTierAssignment := BaseProtocol → Fin 3 → Tier

/-- Use a supplied assignment for the physical tier lookup. No address
is inferred from the order of the declared ledger. -/
def wireTier (identify : WireTierAssignment) (protocol : BaseProtocol) (address : Fin 3) : Tier :=
  identify protocol address

/-- These rows certify the arithmetic of the declared ledger. Physical
identification with a wire mode remains a premise. -/
def massProvenance : State → Provenance
  | (.neutrino, _) => Provenance.blocked
  | (protocol, t) =>
      if t ∈ tiersFor protocol then Provenance.partialE8 else Provenance.notModeled

/-- Decay provenance of a protocol state. -/
def decayProvenance : State → Provenance
  | (.up, t) => if t.val = 3 then Provenance.blocked else Provenance.notModeled
  | (.down, _) => Provenance.notModeled
  | (.electron, t) =>
      if t.val = 0 then Provenance.stable
      else if t.val = 1 then Provenance.e8
      else if t.val = 2 then Provenance.partialE8
      else Provenance.notModeled
  | (.neutrino, _) => Provenance.blocked


end PMElementaryParticles.TierLedger
