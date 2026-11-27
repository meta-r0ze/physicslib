import PersistenceMechanics.ReversibleEncoding
import PersistenceMechanics.ImpedanceMatching
import Mathlib.Tactic

/-! Exact versions of reversible remainder storage as a concrete instance of the upstream reversible-encoding rule.
The positive-real interface law is owned by PersistenceMechanics.ImpedanceMatching. -/
noncomputable section
namespace PMConstants.Interface

def encode (k n : ℕ) : ℕ × ℕ :=
  PersistenceMechanics.ReversibleEncoding.encode (fun x => x/k) (fun x => x%k) n

def decode (k : ℕ) (p : ℕ × ℕ) : ℕ := k*p.1+p.2

theorem decode_encode (k n : ℕ) : decode k (encode k n) = n := by
  simpa [decode, encode, PersistenceMechanics.ReversibleEncoding.encode, Nat.add_comm] using Nat.mod_add_div n k

theorem encoding_injective (k : ℕ) : Function.Injective (encode k) := by
  intro a b h
  have := congrArg (decode k) h
  simpa [decode_encode] using this

theorem remainder_bounded {k : ℕ} (hk : 0 < k) (n : ℕ) : (encode k n).2 < k :=
  Nat.mod_lt n hk

theorem forgetting_remainder_loses_information :
    (4 : ℕ)/3 = 5/3 ∧ (4 : ℕ) ≠ 5 := by norm_num


end PMConstants.Interface
