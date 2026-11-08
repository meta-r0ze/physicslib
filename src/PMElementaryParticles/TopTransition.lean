import PMElementaryParticles.CarrierTransitionOperator

/-! **Top transition interface.**

The top is the up-type tier-3 state; the leading final state is a down-type tier-2
state plus a charged vector mode.  The charged vector is not part of the base
protocol inventory, so it is kept as an explicit boson label.  The rate is
structural: `|T|² · phase`.
-/

noncomputable section
namespace PMElementaryParticles.TopTransition

open PMElementaryParticles.ProtocolDynamics
open PMElementaryParticles.CarrierTransitionOperator

/-- Charged/neutral vector modes appearing in top decay. -/
inductive Boson
  | W
  | Z
  | photon
  deriving DecidableEq, Repr

def Boson.charge : Boson → ℚ
  | .W => 1
  | .Z => 0
  | .photon => 0

/-- Top initial state: up-type tier 3. -/
def topInitial : State := (.up, ⟨3, by decide⟩)

/-- Bottom final state: down-type tier 2. -/
def bottomFinal : State := (.down, ⟨2, by decide⟩)

/-- Top decay final state: bottom plus a charged vector. -/
structure TopFinal where
  bottom : State
  boson : Boson

def topFinal : TopFinal := ⟨bottomFinal, .W⟩

theorem top_charge_conserved : baseCharge .up = baseCharge .down + Boson.charge .W := by
  norm_num [baseCharge, Boson.charge]

/-- Leading carrier-product top amplitude. -/
def topT : ℂ := weakOf (CarrierBridge.ofBaseProtocol .up) * weakOf (CarrierBridge.ofBaseProtocol .down)

/-- Structural top width with a supplied phase-space factor. -/
def topRate (phase : ℝ) : ℝ := Complex.normSq topT * phase

theorem topRate_nonneg (phase : ℝ) (h : 0 ≤ phase) : 0 ≤ topRate phase := by
  unfold topRate
  exact mul_nonneg (Complex.normSq_nonneg _) h

end PMElementaryParticles.TopTransition
