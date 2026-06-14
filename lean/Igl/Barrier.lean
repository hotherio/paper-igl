import Mathlib
import Igl.Separable
import Igl.Rank

/-!
# The separability barrier (paper Appendix `proof_barrier`)

The metric volume factor `√|g|` is what can block the Master Formula's factorization. This
file formalizes the two halves of the paper's barrier discussion:

* **Sufficiency ("if")** — `barrier_if_factorization`: when the metric factor is *itself*
  separable, `√|g|(ζ) = ∏ⱼ χⱼ(ζⱼ)`, the compensated Green's integral still factorizes into
  `d` one-dimensional integrals. The metric is absorbed factor-by-factor; the barrier does not
  appear. This is `fubini_dfold` with the metric merged into each axis.

* **Necessity ("only if")** — `barrierWitness_not_rank_one`: a concrete metric `1 + ζ₀ζ₁` that
  is *not* rank-1 (not of product form), so no single separable kernel factorizes the
  compensated integral for it. This is the rigorous kernel of the paper's informal necessity
  argument. The *general* converse ("any non-separable `√|g|` blocks factorization") is not a
  clean theorem without genericity hypotheses on the function families (a zero/constant source
  factorizes anything), so it is left as the remark below rather than stated as an axiom.

Blueprint nodes:
* `thm:barrier-if`        → `IGL.barrier_if_factorization`
* `thm:barrier-only-if`   → `IGL.barrierWitness_not_rank_one`
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

/-- A concrete non-separable metric factor on `ℝ²`: `g(ζ) = 1 + ζ₀·ζ₁`. -/
def barrierWitness : (Fin 2 → ℝ) → ℝ := fun ζ => 1 + ζ 0 * ζ 1

/-- **Separability barrier — necessity (witness).** The metric factor `1 + ζ₀ζ₁` is *not*
rank-1: it is not of product form `a(ζ₀)·b(ζ₁)`. Hence a single separable kernel cannot
absorb it and factorize the compensated integral — the rigorous core of the paper's "only if"
direction. (The general converse needs non-degeneracy hypotheses; see the module docstring.) -/
theorem barrierWitness_not_rank_one : ¬ HasCPRank barrierWitness 1 := by
  rintro ⟨ι, inst, w, φ, hcard, he⟩
  obtain ⟨i₀, hi₀⟩ := (@Fintype.card_eq_one_iff ι inst).mp hcard
  have hg : ∀ ζ : Fin 2 → ℝ,
      barrierWitness ζ = w i₀ * (φ i₀ 0 (ζ 0) * φ i₀ 1 (ζ 1)) := by
    intro ζ
    rw [he ζ, @Fintype.sum_eq_single ι ℝ inst _ (fun i => w i * ∏ j, φ i j (ζ j)) i₀
          (fun b hb => absurd (hi₀ b) hb), Fin.prod_univ_two]
  set a := φ i₀ 0 with ha
  set b := φ i₀ 1 with hb
  set c := w i₀ with hc
  have e00 : (1 : ℝ) = c * (a 0 * b 0) := by have := hg ![0, 0]; simpa [barrierWitness] using this
  have e11 : (1 + 1 : ℝ) = c * (a 1 * b 1) := by
    have := hg ![1, 1]; simpa [barrierWitness] using this
  have e01 : (1 : ℝ) = c * (a 0 * b 1) := by have := hg ![0, 1]; simpa [barrierWitness] using this
  have e10 : (1 : ℝ) = c * (a 1 * b 0) := by have := hg ![1, 0]; simpa [barrierWitness] using this
  have key : c * (a 0 * b 0) * (c * (a 1 * b 1)) = c * (a 0 * b 1) * (c * (a 1 * b 0)) := by
    ring
  rw [← e00, ← e11, ← e01, ← e10] at key
  norm_num at key

end IGL
