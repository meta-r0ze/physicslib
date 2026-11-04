import PMConstants.General.Encoding

/-! Exact relative descriptions retain the reference VALUE in addition to its
position. The removed self-difference is zero. Omitting the anchor value merges
constant configurations unless a quotient of states is explicitly intended.
These are information theorems, not a per-field maintenance-cost law. -/
namespace PMConstants.General.RelationalEncoding
variable {I A : Type*} [AddGroup A]

/-- Absolute anchor value and all nonself differences. -/
def encode (o : I) (x : I → A) : A × ({i : I // i ≠ o} → A) :=
  (x o, fun i => x i-x o)

theorem self_difference (o : I) (x : I → A) : x o-x o = 0 := sub_self _

theorem reference_and_differences_injective (o : I) : Function.Injective (encode (A := A) o) := by
  intro x y h
  have href : x o = y o := congrArg Prod.fst h
  funext i
  by_cases hi : i = o
  · simpa [hi] using href
  · have hd : x i-x o = y i-y o := congrFun (congrArg Prod.snd h) ⟨i, hi⟩
    calc x i = (x i-x o)+x o := (sub_add_cancel _ _).symm
         _ = (y i-y o)+y o := by rw [hd, href]
         _ = y i := sub_add_cancel _ _

/-- This is an explicit total decoder for arbitrary anchor/difference data. -/
def decode (o : I) [DecidableEq I] (p : A × ({i : I // i ≠ o} → A)) (i : I) : A :=
  if h : i = o then p.1 else p.2 ⟨i, h⟩+p.1

theorem decode_encode (o : I) [DecidableEq I] (x : I → A) : decode o (encode o x) = x := by
  funext i
  by_cases hi : i = o <;> simp [decode, encode, hi]

theorem differences_without_reference_not_injective (o : I) [Nontrivial A] :
    ¬ Function.Injective (fun x : I → A => fun i : {i : I // i ≠ o} => x i-x o) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have he : (fun _ : I => a) = (fun _ : I => b) := h (by funext i; simp)
  exact hab (congrFun he o)

end PMConstants.General.RelationalEncoding
