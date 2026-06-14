import Mathlib
import Igl.Separable

/-!
# The separability barrier: sufficiency (paper Appendix `proof_barrier`)

When the metric factor `√|g|` is itself separable, `√|g|(ζ) = ∏ⱼ χⱼ(ζⱼ)`, the compensated
Green's integral still factorizes into `d` one-dimensional integrals: the metric is
absorbed factor-by-factor and the barrier does not appear. This is `fubini_dfold` with the
metric merged into each axis.
-/

open MeasureTheory

namespace IGL

variable {d R : ℕ}

/-- **Separability barrier — sufficiency.** If the metric factor is separable,
`√|g|(ζ) = ∏ⱼ χⱼ(ζⱼ)`, then the compensated Green's integral against a rank-`R` separable
source factorizes into `d` one-dimensional integrals, the metric absorbed into each axis:
`∫ (∏ⱼGⱼ)·(∑ᵣ wᵣ∏ⱼφᵣⱼ)·(∏ⱼχⱼ) = ∑ᵣ wᵣ ∏ⱼ ∫ Gⱼ φᵣⱼ χⱼ`. -/
theorem barrier_if_factorization
    (w : Fin R → ℝ) (G : Fin d → ℝ → ℝ → ℝ) (φ : Fin R → Fin d → ℝ → ℝ)
    (χ : Fin d → ℝ → ℝ) (ξ : Fin d → ℝ)
    (hint : ∀ r, Integrable (fun ζ : Fin d → ℝ =>
      (∏ j, G j (ξ j) (ζ j)) * (∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j))) :
    ∫ ζ : Fin d → ℝ, (∏ j, G j (ξ j) (ζ j)) *
        (∑ r, w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j)
      = ∑ r, w r * ∏ j, ∫ ζj, G j (ξ j) ζj * φ r j ζj * χ j ζj := by
  have hint' : ∀ r, Integrable (fun ζ : Fin d → ℝ =>
      (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j)) := by
    intro r
    have hfun : (fun ζ : Fin d → ℝ =>
        (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j))
        = fun ζ => w r * ((∏ j, G j (ξ j) (ζ j)) * (∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j)) := by
      funext ζ; ring
    rw [hfun]; exact (hint r).const_mul (w r)
  have key : ∀ r,
      ∫ ζ : Fin d → ℝ, (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j)
        = w r * ∏ j, ∫ ζj, G j (ξ j) ζj * φ r j ζj * χ j ζj := by
    intro r
    have hfun : (fun ζ : Fin d → ℝ =>
        (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j))
        = fun ζ => w r * ∏ j, (G j (ξ j) (ζ j) * φ r j (ζ j) * χ j (ζ j)) := by
      funext ζ
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    rw [hfun, integral_const_mul, fubini_dfold fun j ζj => G j (ξ j) ζj * φ r j ζj * χ j ζj]
  have hmain : (fun ζ : Fin d → ℝ =>
      (∏ j, G j (ξ j) (ζ j)) * (∑ r, w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j))
      = fun ζ => ∑ r, (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)) * ∏ j, χ j (ζ j) := by
    funext ζ
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hmain, integral_finsetSum Finset.univ fun r _ => hint' r]
  exact Finset.sum_congr rfl fun r _ => key r

end IGL
