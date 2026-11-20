import PMSubstrate.E8Values

/-!
# The clock period `Delta`

PMAction's finite clock modules used the literal `43` for the period. The value is
the forced E8 clock period; this module gives PMAction its local name and ties it
to `PMSubstrate.E8Values.Delta`.
-/

namespace PMAction

abbrev Delta : ℕ := PMSubstrate.E8Values.Delta

theorem Delta_eq : Delta = PMSubstrate.E8Values.Delta := rfl

end PMAction
