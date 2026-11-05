import PMSubstrate.Impedance

/-!
# Canonical E8 record values

The forced substrate record `baseline` is the single source for the E8 values
used by every later paper. This module gives them stable names and proves the
numerals once, so downstream modules can import `PMSubstrate.E8Values` instead
of spelling `4`, `43`, `16`, `5`, `2`, or `172` by hand.

Core record:

* `D = 4`, `Delta = 43`, `nu = 16`, `sigma = 5`, `chi = 2`;
* `RM = D·Delta = 172`;
* `N = 2·nu = 32`;
* `intrinsicLoad = nu + sigma + chi = 23`;
* `embeddingLoad = intrinsicLoad + 2·D = 31`;
* `substrateLoad = RM + nu = 188`;
* `overhead = (RM − 1)/RM = 171/172`.

The equations are `rfl` because `baseline` is the forced record; the point is the
API, not new arithmetic.
-/

noncomputable section
namespace PMSubstrate.E8Values

/-- Coordinate dimension `D`. -/
def D : ℕ := baseline.dimension
/-- Clock period `Delta`. -/
def Delta : ℕ := baseline.period
/-- Chiral channel count `nu`. -/
def nu : ℕ := baseline.sectorChannels
/-- Embedding dimension `sigma`. -/
def sigma : ℕ := baseline.embeddingDimension
/-- Euler characteristic `chi`. -/
def chi : ℕ := baseline.eulerCharacteristic

/-- Frame size `R_M = D·Delta`. -/
def RM : ℕ := baseline.resolution
/-- Node capacity `N = 2·nu`. -/
def N : ℕ := baseline.nodeCapacity
/-- Intrinsic label count `nu + sigma + chi`. -/
def intrinsicLoad : ℕ := baseline.intrinsicLoad
/-- Embedding load `intrinsicLoad + 2D`. -/
def embeddingLoad : ℕ := baseline.embeddingLoad
/-- Substrate load `R_M + nu`. -/
def substrateLoad : ℕ := baseline.substrateLoad

/-- One reserved frame cell out of `R_M`. -/
def overhead : ℝ := ((RM - 1 : ℕ) : ℝ) / (RM : ℝ)

@[simp] theorem D_eq : D = 4 := rfl
@[simp] theorem Delta_eq : Delta = 43 := rfl
@[simp] theorem nu_eq : nu = 16 := rfl
@[simp] theorem sigma_eq : sigma = 5 := rfl
@[simp] theorem chi_eq : chi = 2 := rfl
@[simp] theorem RM_eq : RM = 172 := rfl
@[simp] theorem N_eq : N = 32 := rfl
@[simp] theorem intrinsicLoad_eq : intrinsicLoad = 23 := rfl
@[simp] theorem embeddingLoad_eq : embeddingLoad = 31 := rfl
@[simp] theorem substrateLoad_eq : substrateLoad = 188 := rfl

@[simp] theorem overhead_eq : overhead = 171 / 172 := by
  norm_num [overhead, RM, PMSubstrate.baseline, PMSubstrate.Parameters.resolution]

end PMSubstrate.E8Values
