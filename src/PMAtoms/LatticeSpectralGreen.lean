import PMAtoms.LatticeSpectral

/-!
# Spectral Green identity

Scaffold for the second spectral target.

Target:

```lean
theorem cubeLapN_spectralGreen (n : Nat) (j : CubeVertex n) :
    cubeLapN n (fun i => spectralGreen n i j) =
      fun v => if v = j then 1 else 0
```

The finite sine sums are available in Mathlib as
`Real.sin_mul_sum_cos` and `Real.sum_cos`; these are the right starting point for
the orthogonality proof.

The proof should use `cubeLapN_mode`, the sine orthogonality

`∑ x, sin(πa x/(n+1)) sin(πb x/(n+1)) = (n+1)/2 · δ_{ab}`

and the normalization `(2/(n+1))^3`.
-/

noncomputable section
namespace PMAtoms

/-- The spectral Green function is symmetric.  Already proved in the parent
module; kept here as the entry point for the inverse-Laplacian proof. -/
theorem spectralGreen_symm' (n : Nat) (u v : CubeVertex n) :
    spectralGreen n u v = spectralGreen n v u :=
  spectralGreen_symm n u v

end PMAtoms
