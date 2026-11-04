import PMConstants.LinkEvolution

/-! Controlled quadratic response of uniform comparison on a finite Hermitian
packet. This derives the normalized trace coefficient, retaining the chosen
readout and repair semantics as physical inputs. -/
noncomputable section
namespace PMConstants.MeanTraceResponse
open Matrix Finset PMAction PMAction.LinkExpansion
open PMAction.InterferenceReadout LinkSpectralResponse.HermitianTransport
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {H : Matrix n n ℂ}

omit [Nonempty n] in
lemma trace_conjugate (V D : Matrix n n ℂ) (hv : Vᴴ*V=1) :
    (V*D*Vᴴ).trace=D.trace := by rw [trace_mul_cycle,hv,one_mul]

def energy (lam : n → ℝ) (ε : ℝ) : ℝ := ∑ k, (2-2*Real.cos (ε*lam k))

theorem mean_energy (h : H.IsHermitian) (ε : ℝ) :
    meanFlag (transport h ε)=energy h.eigenvalues ε/(4*Fintype.card n) := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  rw [mean_trace _ (transport_unitary h ε)]
  unfold transport
  rw [trace_conjugate _ _ (basis_left h)]
  simp only [phaseDiag,trace_diagonal,Complex.re_sum,Complex.exp_ofReal_mul_I_re]
  unfold energy
  rw [sum_sub_distrib]
  simp only [sum_const,card_univ,nsmul_eq_mul,← mul_sum]
  field_simp
  ring

omit [Nonempty n] in
theorem trace_square_real (h : H.IsHermitian) :
    (H*H).trace.re=∑ k, h.eigenvalues k^2 := by
  have hs := congrArg (fun X => X*X) (generated h)
  rw [hs,LinkEvolution.conjugate_mul _ _ _ (basis_left h),
    trace_conjugate _ _ (basis_left h)]
  simp [genDiag,diagonal_mul_diagonal,trace_diagonal,Complex.re_sum,pow_two]

/-- The constant is independent of ε and valid on the supplied positive radius. -/
def coefficient (h : H.IsHermitian) : ℝ :=
  (5/48*(∑ k, h.eigenvalues k^4))/(4*Fintype.card n)

theorem coefficient_nonneg (h : H.IsHermitian) : 0 ≤ coefficient h := by
  have hs : 0 ≤ ∑ k, h.eigenvalues k^4 := sum_nonneg (fun _ _ => by positivity)
  unfold coefficient
  positivity

/-- Uniform comparison has leading coefficient Re Tr(H²)/(4 dim), not simply
an unweighted count of labels on which H can act. -/
theorem controlled_mean (h : H.IsHermitian) {ε : ℝ} (he : |ε| ≤ radius h) :
    |meanFlag (transport h ε)-ε^2*((H*H).trace.re/(4*Fintype.card n))| ≤
      coefficient h*ε^4 := by
  have hb := diag_expansion h.eigenvalues ε (fun _ : n => (1 : ℂ)) (small_eigenphases h he)
  simp only [diag_cost,diag_generator,Complex.normSq_one,one_mul] at hb
  change |energy h.eigenvalues ε-ε^2*(∑ k, h.eigenvalues k^2)| ≤
    5/48*ε^4*(∑ k, h.eigenvalues k^4) at hb
  have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℝ) < 4*Fintype.card n := by positivity
  rw [mean_energy h ε,trace_square_real h]
  have ha : energy h.eigenvalues ε/(4*Fintype.card n)-
      ε^2*((∑ k, h.eigenvalues k^2)/(4*Fintype.card n))=
      (energy h.eigenvalues ε-ε^2*(∑ k, h.eigenvalues k^2))/(4*Fintype.card n) := by ring
  rw [ha,abs_div,abs_of_pos hd]
  calc
    _ ≤ (5/48*ε^4*(∑ k, h.eigenvalues k^4))/(4*Fintype.card n) :=
      div_le_div_of_nonneg_right hb hd.le
    _ = coefficient h*ε^4 := by unfold coefficient; ring

theorem exponential_mean (h : H.IsHermitian) {ε : ℝ} (he : |ε| ≤ radius h) :
    |meanFlag (NormedSpace.exp (((ε : ℂ)*Complex.I) • H))-
      ε^2*((H*H).trace.re/(4*Fintype.card n))| ≤ coefficient h*ε^4 := by
  rw [← LinkEvolution.transport_eq_exp h ε]
  exact controlled_mean h he

end PMConstants.MeanTraceResponse
