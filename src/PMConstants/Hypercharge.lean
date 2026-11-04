import Mathlib.Tactic

/-!
# Charge selection from specified conservation and coupling constraints

The representation content (one generation, including a sterile singlet) and
the charge normalization are hypotheses. These are not derived from rank alone.
Linear flux conservation by itself leaves a continuous right-quark split.
Gauge-invariant Yukawa couplings plus a neutral sterile channel and a unit
scalar charge remove the freedom. No geometric numerator is chosen by hand.
-/

namespace PMConstants.Hypercharge

structure Charges where
  q : ℚ
  u : ℚ
  d : ℚ
  l : ℚ
  e : ℚ
  n : ℚ
  deriving DecidableEq

/-- Left-handed multiplicities minus right-handed multiplicities. -/
def Flux (Y : Charges) : Prop :=
  3 * Y.q + Y.l = 0 ∧ 2 * Y.q - Y.u - Y.d = 0 ∧
    6 * Y.q - 3 * Y.u - 3 * Y.d + 2 * Y.l - Y.e - Y.n = 0

/-- Charge balance of the four scalar-mediated left/right couplings.
`h` is the scalar charge; its conjugate carries `-h`. -/
def Yukawa (Y : Charges) (h : ℚ) : Prop :=
  Y.u = Y.q + h ∧ Y.d = Y.q - h ∧ Y.e = Y.l - h ∧ Y.n = Y.l + h

def standard : Charges := ⟨1/3, 4/3, -2/3, -1, -2, 0⟩

def family (q h : ℚ) : Charges :=
  ⟨q, q+h, q-h, -3*q, -3*q-h, -3*q+h⟩

def cubic (Y : Charges) : ℚ :=
  6 * Y.q^3 - 3 * Y.u^3 - 3 * Y.d^3 + 2 * Y.l^3 - Y.e^3 - Y.n^3

/-- The polynomial cancellation test for the mixed Abelian/weak factor. -/
def mixedWeak (Y : Charges) : ℚ := 3 * Y.q + Y.l

theorem family_conserves (q h : ℚ) :
    Flux (family q h) ∧ Yukawa (family q h) h ∧
      cubic (family q h) = 0 ∧ mixedWeak (family q h) = 0 := by
  dsimp [Flux, Yukawa, family, cubic, mixedWeak]
  constructor
  · constructor
    · ring
    · constructor <;> ring
  · refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, ?_⟩ <;> ring

/-- Unit scalar normalization plus cancellation still permits different charges
unless the sterile channel's neutrality is imposed. -/
theorem neutrality_needed :
    Flux (family 0 1) ∧ Yukawa (family 0 1) 1 ∧
      cubic (family 0 1) = 0 ∧ family 0 1 ≠ standard := by
  obtain ⟨hf, hy, hc, -⟩ := family_conserves 0 1
  refine ⟨hf, hy, hc, ?_⟩
  intro heq
  have := congrArg Charges.q heq
  norm_num [family, standard] at this

/-- The charges are uniquely selected by these explicit physical constraints. -/
theorem charges_forced (Y : Charges) (hf : Flux Y) (hy : Yukawa Y 1)
    (hn : Y.n = 0) : Y = standard := by
  obtain ⟨hweak, -, -⟩ := hf
  obtain ⟨hu, hd, he, hn'⟩ := hy
  have hl : Y.l = -1 := by linarith
  have hq : Y.q = 1/3 := by linarith
  have hu' : Y.u = 4/3 := by linarith
  have hd' : Y.d = -2/3 := by linarith
  have he' : Y.e = -2 := by linarith
  cases Y
  simp only [standard, Charges.mk.injEq]
  exact ⟨hq, hu', hd', hl, he', hn⟩

theorem standard_satisfies :
    Flux standard ∧ Yukawa standard 1 ∧ standard.n = 0 ∧ cubic standard = 0 := by
  norm_num [Flux, Yukawa, standard, cubic]

/-- With the doublet flux fixed and a neutral sterile channel, linear
conservation alone permits every real-valued (here rational) split `t`. -/
def split (t : ℚ) : Charges := ⟨1/3, 1/3+t, 1/3-t, -1, -2, 0⟩

theorem split_conserves (t : ℚ) : Flux (split t) := by
  dsimp [Flux, split]
  constructor
  · ring
  · constructor <;> ring

/-- The cubic condition closes the split up to exchanging the two singlets. -/
theorem cubic_selects_split (t : ℚ) :
    cubic (split t) = 0 ↔ t = 1 ∨ t = -1 := by
  have heq : cubic (split t) = 6 * (1-t^2) := by dsimp [cubic, split]; ring
  rw [heq]
  constructor
  · intro h
    have : (t-1)*(t+1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

theorem channel_count : 3*2 + 3 + 3 + 2 + 1 + 1 = (16 : ℕ) := by decide

end PMConstants.Hypercharge
