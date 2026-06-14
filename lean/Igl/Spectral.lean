import Mathlib
import Igl.Separable

/-!
# Spectral factorized integral (paper Appendix `proof_spectral`)

The spectral counterpart of the Master Formula. Expanding the Green's function in the
eigenbasis produces *additive* eigenvalues `∑ⱼ λ_{nⱼ}`; the exponential-sum surrogate
`1/λ ≈ ∑ₖ γₖ e^{-αₖλ}` turns the additive coupling into a **product**
`e^{-αₖ ∑ⱼ λ_{nⱼ}} = ∏ⱼ e^{-αₖ λ_{nⱼ}}` (`exp_neg_sum_eigs`).  Once every factor depends on a
single axis, the multi-index mode sum factorizes across the `d` axes exactly as the
continuous Fubini factorization does (`spectral_factorization`).

Blueprint nodes:
* `thm:exp-neg-sum`        → `IGL.exp_neg_sum_eigs`
* `thm:spectral-factor`    → `IGL.spectral_factorization`
-/

namespace IGL

variable {d M K : ℕ}

/-- **Additive eigenvalues become a product under the exponential.** The algebraic heart of
the spectral exponential-sum trick: `exp(-(α · ∑ⱼ λⱼ)) = ∏ⱼ exp(-(α · λⱼ))`. -/
theorem exp_neg_sum_eigs (α : ℝ) (lam : Fin d → ℝ) :
    Real.exp (-(α * ∑ j, lam j)) = ∏ j, Real.exp (-(α * lam j)) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_neg_distrib]

/-- **Spectral factorized integral.** With the exponential-sum surrogate applied modewise and
a source that is separable in the eigenbasis (`f̂_n = ∏ⱼ g j (n j)`), the spectral solution
collapses to a finite `K`-term sum, each term a product over the `d` axes of a one-dimensional
mode sum:
`∑ₖ γₖ ∑_n (∏ⱼ e^{-αₖ λ_{nⱼ}} φ_{nⱼ}(ξⱼ)) f̂_n = ∑ₖ γₖ ∏ⱼ ∑ₘ e^{-αₖ λⱼₘ} φⱼₘ(ξⱼ) gⱼₘ`.
The multi-index sum over modes `n : Fin d → Fin M` factorizes across axes (`Finset.prod_univ_sum`),
the discrete analogue of `fubini_dfold`. -/
theorem spectral_factorization
    (γ α : Fin K → ℝ) (lam : Fin d → Fin M → ℝ)
    (φ : Fin d → Fin M → ℝ → ℝ) (g : Fin d → Fin M → ℝ) (ξ : Fin d → ℝ) :
    (∑ k, γ k * ∑ n : Fin d → Fin M,
        (∏ j, Real.exp (-(α k * lam j (n j))) * φ j (n j) (ξ j)) * ∏ j, g j (n j))
      = ∑ k, γ k * ∏ j, ∑ m, Real.exp (-(α k * lam j m)) * φ j m (ξ j) * g j m := by
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr (by simp [Fintype.piFinset_univ]) fun n _ => ?_
  rw [← Finset.prod_mul_distrib]

end IGL
