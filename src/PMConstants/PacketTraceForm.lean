import PMConstants.PacketGaugeActions
import PMConstants.StiffnessIndices

/-! Exact quadratic trace form of the common packet representation. These
are representation indices, not an independent choice of physical workload.
Fundamental-generator normalization and the uniform comparison ensemble are
explicit when interpreting the resulting coefficients. -/
noncomputable section
namespace PMConstants.PacketTraceForm
open Matrix PacketGaugeActions
open scoped Kronecker

lemma trace_block (A B : Matrix Q Q ℂ) (C D : Matrix (Fin 2) (Fin 2) ℂ) :
    (block A B C D).trace=A.trace+B.trace+C.trace+D.trace := by
  simp [block,Matrix.trace,Matrix.diag,Fintype.sum_sum_type]
  ring

/-- Lie generators are linear maps: inactive blocks are zero, not identity. -/
def weakGen (A : Matrix (Fin 2) (Fin 2) ℂ) : M := block (1 ⊗ₖ A) 0 A 0
def colourGen (B : Matrix (Fin 3) (Fin 3) ℂ) : M := block (B ⊗ₖ 1) (B ⊗ₖ 1) 0 0
def hyperGen : M := (1/2 : ℂ) • charge

theorem weak_trace_product (A A' : Matrix (Fin 2) (Fin 2) ℂ) :
    (weakGen A*weakGen A').trace=4*(A*A').trace := by
  simp [weakGen,block_mul,trace_block,← mul_kronecker_mul,trace_kronecker,trace_one]
  ring

theorem colour_trace_product (B B' : Matrix (Fin 3) (Fin 3) ℂ) :
    (colourGen B*colourGen B').trace=4*(B*B').trace := by
  simp [colourGen,block_mul,trace_block,← mul_kronecker_mul,trace_kronecker,trace_one]
  ring

theorem weak_colour_trace (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) :
    (weakGen A*colourGen B).trace=B.trace*A.trace := by
  simp [weakGen,colourGen,block_mul,trace_block,← mul_kronecker_mul,trace_kronecker]

theorem weak_hyper_trace (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (weakGen A*hyperGen).trace=0 := by
  simp [weakGen,hyperGen,charge,block_mul,trace_block,
    trace_smul,trace_kronecker,trace_one]

theorem colour_hyper_trace (B : Matrix (Fin 3) (Fin 3) ℂ) :
    (colourGen B*hyperGen).trace=(2/3 : ℂ)*B.trace := by
  simp [colourGen,hyperGen,charge,block_mul,trace_block,
    ← mul_kronecker_mul,trace_smul,trace_kronecker,trace_one,trace_diagonal,Fin.sum_univ_succ]
  ring

theorem hyper_trace_square : (hyperGen*hyperGen).trace=(10/3 : ℂ) := by
  norm_num [hyperGen,charge,Matrix.mul_smul,Matrix.smul_mul,block_mul,trace_block,
    ← mul_kronecker_mul,trace_smul,trace_kronecker,trace_one,trace_diagonal,
    diagonal_mul_diagonal,Fin.sum_univ_succ]

def joint (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ) (b : ℝ) : M :=
  weakGen A+colourGen B+(b : ℂ) • hyperGen

lemma weak_hermitian (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) :
    (weakGen A).IsHermitian := by
  change (weakGen A)ᴴ=weakGen A
  simp [weakGen,block_star,conjTranspose_kronecker,hA.eq]

lemma colour_hermitian (B : Matrix (Fin 3) (Fin 3) ℂ) (hB : B.IsHermitian) :
    (colourGen B).IsHermitian := by
  change (colourGen B)ᴴ=colourGen B
  simp [colourGen,block_star,conjTranspose_kronecker,hB.eq]

lemma hyper_hermitian : hyperGen.IsHermitian := by
  change hyperGenᴴ=hyperGen
  simp [hyperGen,conjTranspose_smul,PacketGaugeActions.charge_hermitian.eq]

theorem joint_hermitian (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (b : ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) : (joint A B b).IsHermitian := by
  change (joint A B b)ᴴ=joint A B b
  simp [joint,conjTranspose_add,conjTranspose_smul,(weak_hermitian A hA).eq,
    (colour_hermitian B hB).eq,hyper_hermitian.eq]

/-- Mixed terms vanish for the traceless non-Abelian generators. -/
theorem joint_trace_square (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 3) (Fin 3) ℂ) (b : ℝ) (hA : A.trace=0) (hB : B.trace=0) :
    (joint A B b*joint A B b).trace=
      4*(A*A).trace+4*(B*B).trace+(10/3 : ℂ)*(b : ℂ)^2 := by
  have hc1 : (colourGen B*weakGen A).trace=0 := by
    rw [trace_mul_comm,weak_colour_trace,hA,mul_zero]
  have hc2 : (hyperGen*weakGen A).trace=0 := by rw [trace_mul_comm,weak_hyper_trace]
  have hc3 : (hyperGen*colourGen B).trace=0 := by
    rw [trace_mul_comm,colour_hyper_trace,hB,mul_zero]
  simp only [joint,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,trace_add,trace_smul,
    smul_eq_mul,weak_trace_product,colour_trace_product,weak_colour_trace,weak_hyper_trace,
    colour_hyper_trace,hyper_trace_square,hA,hB,hc1,hc2,hc3]
  ring

/-- At the stated fundamental trace normalization the packet indices agree
with the earlier symbolic count, now derived from the actual operators. -/
theorem normalized_indices (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : (A*A).trace=1/2) (hB : (B*B).trace=1/2) :
    (weakGen A*weakGen A).trace=2 ∧ (colourGen B*colourGen B).trace=2 ∧
      (hyperGen*hyperGen).trace=10/3 := by
  rw [weak_trace_product,colour_trace_product,hA,hB,hyper_trace_square]
  norm_num

/-- Reindexing onto the actual carriers preserves the trace form. -/
theorem packet_trace_product (X Y : M) :
    (onPacket X*onPacket Y).trace=(X*Y).trace := by
  rw [← map_mul]
  change (∑ v : CarrierActions.Packet, (X*Y) (channelEquiv.symm v) (channelEquiv.symm v))=_
  exact Equiv.sum_comp channelEquiv.symm (fun c => (X*Y) c c)

end PMConstants.PacketTraceForm
