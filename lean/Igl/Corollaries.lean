import Mathlib
import Igl.Separable

/-!
# Tier-1 corollaries of the Master Formula

* `IGL.additiveGreen_factorization` — the `K = 1` (Additive-Green) special case.
* `IGL.kan_reduction`              — the `G = Id` (reproducing-kernel / KAN) limit.
* `IGL.gauge_invariance`           — invariance under a measure-preserving reparametrisation.
-/

open MeasureTheory

namespace IGL

variable {d R : ℕ}

/-- **Additive-Green (`K = 1`).** With a single separable kernel `∏_j G_j(ξ^j,ζ^j)` and a
rank-`R` separable source, the prediction integral factorises as
`∑_r w_r ∏_j I_{r,j}(ξ^j)`. The `K = 1` instance of the Master Formula. -/
theorem additiveGreen_factorization
    (w : Fin R → ℝ) (G : Fin d → ℝ → ℝ → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) (ξ : Fin d → ℝ)
    (hint : ∀ r, Integrable
      (fun ζ : Fin d → ℝ => (∏ j, G j (ξ j) (ζ j)) * ∏ j, φ r j (ζ j))) :
    ∫ ζ : Fin d → ℝ, (∏ j, G j (ξ j) (ζ j)) * separableSource w φ ζ
      = ∑ r, w r * ∏ j, partialIntegral (G j) (φ r j) (ξ j) := by
  have hint' : ∀ r, Integrable
      (fun ζ : Fin d → ℝ => (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j))) := by
    intro r
    have hfun :
        (fun ζ : Fin d → ℝ => (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)))
          = fun ζ => w r * ((∏ j, G j (ξ j) (ζ j)) * ∏ j, φ r j (ζ j)) := by
      funext ζ; ring
    rw [hfun]; exact (hint r).const_mul (w r)
  have key : ∀ r,
      ∫ ζ : Fin d → ℝ, (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j))
        = w r * ∏ j, partialIntegral (G j) (φ r j) (ξ j) := by
    intro r
    have hfun :
        (fun ζ : Fin d → ℝ => (∏ j, G j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)))
          = fun ζ => w r * ∏ j, (G j (ξ j) (ζ j) * φ r j (ζ j)) := by
      funext ζ; rw [Finset.prod_mul_distrib]; ring
    rw [hfun, integral_const_mul, fubini_dfold fun j ζj => G j (ξ j) ζj * φ r j ζj]
    rfl
  unfold separableSource
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ fun r _ => hint' r]
  exact Finset.sum_congr rfl fun r _ => key r

/-- **KAN limit (`G = Id` / reproducing kernel).** If each 1-D integral reproduces its
source factor — `I_{k,r,j}(ξ^j) = φ_{r,j}(ξ^j)`, the identity-kernel condition — then the
IGL output collapses to a Kolmogorov–Arnold form: a sum of products of univariate
functions of the coordinates. -/
theorem kan_reduction {K : ℕ}
    (γ : Fin K → ℝ) (w : Fin R → ℝ) (Gk : Fin K → Fin d → ℝ → ℝ → ℝ)
    (φ : Fin R → Fin d → ℝ → ℝ) (ξ : Fin d → ℝ)
    (hrep : ∀ k r j, partialIntegral (Gk k j) (φ r j) (ξ j) = φ r j (ξ j)) :
    iglParticular γ w Gk φ ξ = ∑ k, ∑ r, γ k * w r * ∏ j, φ r j (ξ j) := by
  unfold iglParticular
  simp_rw [hrep]

/-- **Gauge invariance.** The prediction integral is unchanged under any measure-preserving
reparametrisation `e` of coordinate space — in particular the random rotation used to make
intrinsic coordinates non-axis-aligned. The paper's "source transforms inversely" is the
change of variables `h ∘ e`. -/
theorem gauge_invariance (e : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ))
    (he : MeasurePreserving e) (h : (Fin d → ℝ) → ℝ) :
    ∫ ζ : Fin d → ℝ, h (e ζ) = ∫ ζ : Fin d → ℝ, h ζ :=
  he.integral_comp' h

end IGL
