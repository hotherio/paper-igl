import Mathlib
import Igl.Separable

/-!
# CP-rank bounds and rank-friendly differentiation (paper §Low-rank, §Operator coupling)

A constructive CP-rank predicate for multivariate functions, and the two structural rank
bounds the paper's compensation analysis relies on:

* `HasCPRank.add` — **sub-additivity** `rank(f+g) ≤ rank f + rank g`
  (the additive operator correction `rank(f̂) ≤ rank(f̃√|g|) + rank(L_coup u*)`);
* `HasCPRank.mul` — **sub-multiplicativity** `rank(f·g) ≤ rank f · rank g`
  (the multiplicative metric absorption `rank(f̃·√|g|) ≤ rank(f̃)·rank(√|g|)`);
* `applyCoordOp_hasCPRank` — **differentiation is rank-friendly**: a separable operator
  `L = ∑ⱼ Lⱼ` maps a rank-`R` source to one of rank `≤ R·d`.

The predicate is carried over an arbitrary finite index type `ι` (rank `= card ι`), which makes
`add`/`mul` direct corollaries of `Fintype.sum_sum_type` / `Fintype.sum_prod_type`. We bound
the rank from above (constructive witnesses); no minimal-rank theory is needed.

Blueprint nodes:
* `def:cp-rank`            → `IGL.HasCPRank`
* `thm:cp-rank-add`        → `IGL.HasCPRank.add`
* `thm:cp-rank-mul`        → `IGL.HasCPRank.mul`
* `thm:diff-rank-friendly` → `IGL.applyCoordOp_hasCPRank`
-/

namespace IGL

variable {d : ℕ}

/-- **CP-rank (upper-bound) predicate.** `HasCPRank f n` holds when `f` can be written as a
sum of `n` separable (rank-1) terms `f(ζ) = ∑ᵢ wᵢ ∏ⱼ φᵢⱼ(ζⱼ)`, the index set carried as a
finite type of cardinality `n`. -/
def HasCPRank (f : (Fin d → ℝ) → ℝ) (n : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (φ : ι → Fin d → ℝ → ℝ),
    Fintype.card ι = n ∧ ∀ ζ, f ζ = ∑ i, w i * ∏ j, φ i j (ζ j)

/-- A rank-`R` separable source has CP-rank `R`. -/
theorem separableSource_hasCPRank {R : ℕ} (w : Fin R → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) :
    HasCPRank (separableSource w φ) R :=
  ⟨Fin R, inferInstance, w, φ, Fintype.card_fin R, fun _ => rfl⟩

/-- **Sub-additivity of CP-rank:** `rank(f+g) ≤ rank f + rank g`. Witness: the disjoint union
of the two term families. -/
theorem HasCPRank.add {m n : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : HasCPRank f m) (hg : HasCPRank g n) : HasCPRank (f + g) (m + n) := by
  obtain ⟨ιf, instf, w, φ, hcardf, hfe⟩ := hf
  obtain ⟨ιg, instg, v, ψ, hcardg, hge⟩ := hg
  letI := instf; letI := instg
  refine ⟨ιf ⊕ ιg, inferInstance, Sum.elim w v, Sum.elim φ ψ, ?_, ?_⟩
  · simp [Fintype.card_sum, hcardf, hcardg]
  · intro ζ
    rw [Pi.add_apply, hfe ζ, hge ζ, Fintype.sum_sum_type]
    simp [Sum.elim_inl, Sum.elim_inr]

/-- **Sub-multiplicativity of CP-rank:** `rank(f·g) ≤ rank f · rank g` (pointwise product).
Witness: the product index, multiplying factor families axis-by-axis. -/
theorem HasCPRank.mul {m n : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : HasCPRank f m) (hg : HasCPRank g n) : HasCPRank (f * g) (m * n) := by
  obtain ⟨ιf, instf, w, φ, hcardf, hfe⟩ := hf
  obtain ⟨ιg, instg, v, ψ, hcardg, hge⟩ := hg
  letI := instf; letI := instg
  refine ⟨ιf × ιg, inferInstance, fun p => w p.1 * v p.2,
    fun p j x => φ p.1 j x * ψ p.2 j x, ?_, ?_⟩
  · simp [Fintype.card_prod, hcardf, hcardg]
  · intro ζ
    rw [Pi.mul_apply, hfe ζ, hge ζ, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.prod_mul_distrib]; ring

/-- A coordinate-wise operator `L = ∑ⱼ Lⱼ` acting on a separable source: each `Lⱼ` replaces
the `j`-th univariate factor of every term. -/
def applyCoordOp {R : ℕ} (Lj : Fin d → (ℝ → ℝ) → (ℝ → ℝ))
    (w : Fin R → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) : (Fin d → ℝ) → ℝ :=
  fun ζ => ∑ r, w r * ∑ j, ∏ i, (if i = j then Lj j (φ r j) else φ r i) (ζ i)

/-- **Differentiation is rank-friendly.** Applying a coordinate-wise separable operator
`L = ∑ⱼ Lⱼ` to a rank-`R` separable source yields a function of CP-rank `≤ R·d`: the `(r,j)`
term differentiates the `j`-th factor of the `r`-th source term. -/
theorem applyCoordOp_hasCPRank {R : ℕ} (Lj : Fin d → (ℝ → ℝ) → (ℝ → ℝ))
    (w : Fin R → ℝ) (φ : Fin R → Fin d → ℝ → ℝ) :
    HasCPRank (applyCoordOp Lj w φ) (R * d) := by
  refine ⟨Fin R × Fin d, inferInstance, fun p => w p.1,
    fun p i => if i = p.2 then Lj p.2 (φ p.1 p.2) else φ p.1 i, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · intro ζ
    simp only [applyCoordOp]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]

end IGL
