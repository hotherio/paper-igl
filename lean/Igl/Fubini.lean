import Mathlib

open MeasureTheory

/-- **IGL Fubini factorization (rank-1 / separable case).**
A separable integrand `f(x)·g(y)` over a product space integrates to the product of the
one-dimensional integrals. This is the mathematical heart of IGL's Fubini trick: a
rank-`R` separable source `f̂ = ∑ᵣ wᵣ ∏ⱼ φᵣⱼ` lets the `d`-dimensional Green's integral
`u = G ∗ f̂` collapse into `d` independent 1-D integrals — the `O(Nᵈ) → O(KRd)` reduction. -/
theorem igl_separable_factorization (f g : ℝ → ℝ) :
    ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂(volume.prod volume) = (∫ x, f x) * (∫ y, g y) :=
  integral_prod_mul f g
