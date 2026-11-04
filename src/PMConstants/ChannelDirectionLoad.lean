import PMSubstrate.Channels
import PMConstants.Partition

/-! Quadratic direction loads of the actual minimal D4 glue-class vectors.
These are the orthogonal coordinates in Paper I's proved even-sum model, not
permutations of the simple-root basis. The arithmetic establishes geometric
balance. Interpreting squared-coordinate load as operational collision exposure,
and identifying these axes with the register directions, remain physical bridges.
-/
noncomputable section
namespace PMConstants.ChannelDirectionLoad
open Finset PMSubstrate.Channels

def shell (c : ℕ) : Finset (Fin 4 → Fin 5) :=
  univ.filter fun k => glueClass (boxVec k) = c ∧ norm4 (boxVec k) = 4

def quadraticLoad (c : ℕ) (d : Fin 4) : ℤ :=
  ∑ k ∈ shell c, (boxVec k d)^2

/-- Each of the three actual nontrivial shells has the same load in each axis. -/
theorem shell_axis_load : ∀ c : Fin 3, ∀ d : Fin 4,
    quadraticLoad (c.val+1) d = 8 := by decide +kernel

theorem nontrivial_axis_load (c : ℕ) (hc : c=1 ∨ c=2 ∨ c=3) (d : Fin 4) :
    quadraticLoad c d = 8 := by
  rcases hc with rfl | rfl | rfl
  · exact shell_axis_load 0 d
  · exact shell_axis_load 1 d
  · exact shell_axis_load 2 d

/-- Doubled coordinates have squared norm four. Dividing by four normalizes
one minimal vector to one unit of quadratic load. -/
def directionLoad (c : ℕ) (d : Fin 4) : ℝ := (quadraticLoad c d : ℝ)/4

theorem direction_load_two (c : ℕ) (hc : c=1 ∨ c=2 ∨ c=3) (d : Fin 4) :
    directionLoad c d = 2 := by
  rw [directionLoad, nontrivial_axis_load c hc d]
  norm_num

/-- Two distinct nontrivial channel classes have geometric load four per axis.
The equality holds for any two nontrivial classes; distinctness specifies the
actual two-class channel interpretation inherited from Paper I. -/
theorem channel_pair_balanced (c e : ℕ) (hc : c=1 ∨ c=2 ∨ c=3)
    (he : e=1 ∨ e=2 ∨ e=3) (_hne : c ≠ e) (d : Fin 4) :
    directionLoad c d + directionLoad e d = 4 := by
  rw [direction_load_two c hc d, direction_load_two e he d]
  norm_num

/-- If collision loss is quadratic directional load divided by the 43 phases,
the geometric balance yields 16 eta along each fixed-direction phase cycle.
This statement exposes the operational loss law as a hypothesis. -/
theorem quadratic_loss_payload (c e : ℕ) (hc : c=1 ∨ c=2 ∨ c=3)
    (he : e=1 ∨ e=2 ∨ e=3) (hne : c ≠ e) (d : Fin 4)
    (loss : ℝ) (hloss : loss = (directionLoad c d + directionLoad e d)/43) :
    16-loss = 16*PMConstants.overhead := by
  rw [hloss, channel_pair_balanced c e hc he hne d]
  norm_num [PMConstants.overhead]

end PMConstants.ChannelDirectionLoad
