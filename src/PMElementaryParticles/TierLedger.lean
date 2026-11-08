import PMElementaryParticles.ProtocolDynamics

/-! **Tier ledger.**

The four geometric tiers are `Δ⁰…Δ³`.  Each base protocol occupies a subset:

```
up-type       0, 2, 3
down-type     0, 1, 2
electron      0, 1, 2
neutrino      0, 1, 2
```

The per-tier mass/decay status is a provenance ledger, not a derivation.  A
status records what the current library proves: `e8`, `comparison`, `partial`,
`blocked`, `notModeled`, or `stable`.
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

/-- The tier subset of a base protocol. -/
def tiersFor : BaseProtocol → List Tier
  | .up => upTiers
  | .down => downTiers
  | .electron => electronTiers
  | .neutrino => neutrinoTiers

theorem upTiers_length : upTiers.length = 3 := rfl
theorem downTiers_length : downTiers.length = 3 := rfl
theorem electronTiers_length : electronTiers.length = 3 := rfl
theorem neutrinoTiers_length : neutrinoTiers.length = 3 := rfl

/-- Mass provenance of a protocol state. -/
def massProvenance : State → Provenance
  | (.up, t) =>
      if t.val = 0 ∨ t.val = 2 ∨ t.val = 3 then Provenance.e8 else Provenance.notModeled
  | (.down, t) =>
      if t.val = 0 ∨ t.val = 1 ∨ t.val = 2 then Provenance.e8 else Provenance.notModeled
  | (.electron, t) =>
      if t.val = 0 ∨ t.val = 1 ∨ t.val = 2 then Provenance.e8 else Provenance.notModeled
  | (.neutrino, _) => Provenance.blocked

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
