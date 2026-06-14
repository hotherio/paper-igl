import Mathlib
import Igl.Fubini

/-!
# IGL separable structure and the Fubini factorization (general rank)

Blueprint nodes (see `blueprint/src/content.tex`):
* `def:separable-source`  → `IGL.separableSource`
* `def:separable-kernel`  → `IGL.separableKernel`
* `def:partial-integral`  → `IGL.partialIntegral`
* `def:igl-output`        → `IGL.iglParticular`
* `thm:fubini-dfold`      → `IGL.fubini_dfold`        (PROVED)
* `thm:fubini-general`    → `IGL.fubini_factorization` (stub — first leaf to formalize)
-/

open MeasureTheory

namespace IGL

variable {d R K : ℕ}

/-- Rank-`R` separable (CP) source: `f̂(ζ) = ∑_r w_r ∏_j φ_{r,j}(ζ^j)`. -/
def separableSource (w : Fin R → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun ζ => ∑ r, w r * ∏ j, φ r j (ζ j)

/-- Rank-`K` separable Green's kernel: `G(ξ,ζ) = ∑_k γ_k ∏_j G_{k,j}(ξ^j,ζ^j)`. -/
def separableKernel (γ : Fin K → ℝ) (Gk : Fin K → Fin d → ℝ → ℝ → ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
  fun ξ ζ => ∑ k, γ k * ∏ j, Gk k j (ξ j) (ζ j)

/-- The 1-D integral `I_{k,r,j}(ξ^j) = ∫ G_{k,j}(ξ^j, ζ^j) φ_{r,j}(ζ^j) dζ^j`. -/
noncomputable def partialIntegral (Gkj : ℝ → ℝ → ℝ) (φrj : ℝ → ℝ) (ξj : ℝ) : ℝ :=
  ∫ ζj, Gkj ξj ζj * φrj ζj

/-- IGL particular solution `u(ξ) = ∑_{k,r} γ_k w_r ∏_j I_{k,r,j}(ξ^j)`. -/
noncomputable def iglParticular (γ : Fin K → ℝ) (w : Fin R → ℝ)
    (Gk : Fin K → Fin d → ℝ → ℝ → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun ξ => ∑ k, ∑ r, γ k * w r * ∏ j, partialIntegral (Gk k j) (φ r j) (ξ j)

/-- **d-fold separable factorization** (Fubini core, a single CP term): a product of `d`
univariate factors integrates over `ℝ^d` to the product of the `d` one-dimensional
integrals. Generalises `igl_separable_factorization` from 2 factors to `d`. -/
theorem fubini_dfold (h : Fin d → ℝ → ℝ) :
    ∫ ζ : Fin d → ℝ, ∏ j, h j (ζ j) = ∏ j, ∫ ζj, h j ζj :=
  integral_fintype_prod_eq_prod fun j => h j

/-- **IGL Fubini factorization (general rank).** With a rank-`R` separable source and a
rank-`K` separable kernel, the `d`-dimensional Green's integral collapses to the CP sum
`∑_{k,r} γ_k w_r ∏_j I_{k,r,j}(ξ^j)` — the `O(Nᵈ) → O(KRd)` reduction. The integrability
hypothesis is what lets the finite `k,r` sums pass through the integral; the per-term
`d`-fold collapse is `fubini_dfold`. First leaf to hand to `lean-formalize`. -/
theorem fubini_factorization
    (γ : Fin K → ℝ) (w : Fin R → ℝ)
    (Gk : Fin K → Fin d → ℝ → ℝ → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) (ξ : Fin d → ℝ)
    (hint : ∀ k r, Integrable
      (fun ζ : Fin d → ℝ => (∏ j, Gk k j (ξ j) (ζ j)) * ∏ j, φ r j (ζ j))) :
    ∫ ζ : Fin d → ℝ, separableKernel γ Gk ξ ζ * separableSource w φ ζ
      = iglParticular γ w Gk φ ξ := by
  -- each expanded `(k,r)` summand is integrable (scale the `hint` integrand)
  have hterm : ∀ k r, Integrable
      (fun ζ : Fin d → ℝ => (γ k * ∏ j, Gk k j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j))) := by
    intro k r
    have hfun :
        (fun ζ : Fin d → ℝ => (γ k * ∏ j, Gk k j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)))
          = fun ζ => (γ k * w r) * ((∏ j, Gk k j (ξ j) (ζ j)) * ∏ j, φ r j (ζ j)) := by
      funext ζ; ring
    rw [hfun]
    exact (hint k r).const_mul (γ k * w r)
  -- each `(k,r)` term collapses to a product of 1-D integrals via `fubini_dfold`
  have key : ∀ k r,
      ∫ ζ : Fin d → ℝ, (γ k * ∏ j, Gk k j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j))
        = γ k * w r * ∏ j, partialIntegral (Gk k j) (φ r j) (ξ j) := by
    intro k r
    have hfun :
        (fun ζ : Fin d → ℝ => (γ k * ∏ j, Gk k j (ξ j) (ζ j)) * (w r * ∏ j, φ r j (ζ j)))
          = fun ζ => (γ k * w r) * ∏ j, (Gk k j (ξ j) (ζ j) * φ r j (ζ j)) := by
      funext ζ; rw [Finset.prod_mul_distrib]; ring
    rw [hfun, integral_const_mul, fubini_dfold fun j ζj => Gk k j (ξ j) ζj * φ r j ζj]
    rfl
  unfold separableKernel separableSource iglParticular
  simp_rw [Fintype.sum_mul_sum]
  rw [integral_finsetSum Finset.univ fun k _ => integrable_finsetSum _ fun r _ => hterm k r]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum Finset.univ fun r _ => hterm k r]
  exact Finset.sum_congr rfl fun r _ => key k r

end IGL
