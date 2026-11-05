import PMAtoms.E8AtomValues
import Mathlib.Tactic

/-!
# Nuclear magic numbers from E8

The standard spherical magic numbers and the actinide deformed closures all have
E8 expressions:

`2=χ`, `8=Dχ`, `20=Dσ`, `28=D(σ+χ)`, `50=χσ²`,
`82=2(Δ−χ)`, `126=(σ−χ)(Δ−1)`, `184=D(Δ+σ−χ)`.

The deformed actinide closures are `96=2(Δ+σ)` and
`152=(σ−χ)Δ+(ν+σ+χ)`.

This module records the ladder; the shell-correction energy is a separate model.
-/

namespace PMAtoms

/-- First nuclear magic number `2 = χ`. -/
def magic2 : Nat := χ
theorem magic2_eq : magic2 = 2 := by norm_num [magic2, χ, PMSubstrate.baseline]

/-- `8 = Dχ`. -/
def magic8 : Nat := D * χ
theorem magic8_eq : magic8 = 8 := by norm_num [magic8, D, χ, PMSubstrate.baseline]

/-- `20 = Dσ`. -/
def magic20 : Nat := D * σ
theorem magic20_eq : magic20 = 20 := by norm_num [magic20, D, σ, PMSubstrate.baseline]

/-- `28 = D(σ+χ)`. -/
def magic28 : Nat := D * (σ + χ)
theorem magic28_eq : magic28 = 28 := by norm_num [magic28, D, σ, χ, PMSubstrate.baseline]

/-- `50 = χσ²`. -/
def magic50 : Nat := χ * σ ^ 2
theorem magic50_eq : magic50 = 50 := by norm_num [magic50, χ, σ, PMSubstrate.baseline]

/-- `82 = 2(Δ−χ)`. -/
def magic82 : Nat := 2 * (Δ - χ)
theorem magic82_eq : magic82 = 82 := by
  norm_num [magic82, Δ, χ, PMSubstrate.baseline]

/-- `126 = (σ−χ)(Δ−1)`. -/
def magic126 : Nat := (σ - χ) * (Δ - 1)
theorem magic126_eq : magic126 = 126 := by
  norm_num [magic126, σ, χ, Δ, PMSubstrate.baseline]

/-- Deformed proton closure `96 = 2(Δ+σ)`. -/
def magic96 : Nat := 2 * (Δ + σ)
theorem magic96_eq : magic96 = 96 := by
  norm_num [magic96, Δ, σ, PMSubstrate.baseline]

/-- Deformed neutron closure `152 = (σ−χ)Δ + (ν+σ+χ)`. -/
def magic152 : Nat := (σ - χ) * Δ + (ν + σ + χ)
theorem magic152_eq : magic152 = 152 := by
  norm_num [magic152, σ, χ, Δ, ν, PMSubstrate.baseline]

/-- `184 = D(Δ+σ−χ)`. -/
def magic184 : Nat := D * (Δ + σ - χ)
theorem magic184_eq : magic184 = 184 := by
  norm_num [magic184, D, Δ, σ, χ, PMSubstrate.baseline]

/-- The spherical and deformed nuclear closure ladder. -/
def nuclearMagic : List Nat :=
  [magic2, magic8, magic20, magic28, magic50, magic82, magic96, magic126, magic152, magic184]

theorem nuclearMagic_eq : nuclearMagic = [2, 8, 20, 28, 50, 82, 96, 126, 152, 184] := by
  simp [nuclearMagic, magic2_eq, magic8_eq, magic20_eq, magic28_eq, magic50_eq,
    magic82_eq, magic96_eq, magic126_eq, magic152_eq, magic184_eq]


/-- Nuclear shell occupations between the E8 closures. -/
def nuclearShellSizes : List Nat :=
  [magic2, magic8 - magic2, magic20 - magic8, magic28 - magic20,
   magic50 - magic28, magic82 - magic50, magic96 - magic82,
   magic126 - magic96, magic152 - magic126, magic184 - magic152]

theorem nuclearShellSizes_eq :
    nuclearShellSizes = [2, 6, 12, 8, 22, 32, 14, 30, 26, 32] := by
  simp [nuclearShellSizes, magic2_eq, magic8_eq, magic20_eq, magic28_eq,
    magic50_eq, magic82_eq, magic96_eq, magic126_eq, magic152_eq, magic184_eq]

end PMAtoms
