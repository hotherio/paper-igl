import Mathlib

/-!
# Cited classical facts (Tier 3)

Mathlib v4.30.0 has **no** elliptic-PDE Green's-function theory and **no** exponential-sum
approximation theory (verified: no `greensFunction` / `fundamentalSolution` / `Helmholtz`
/ Riesz–Newtonian potential, no exp-sum results). The classical results IGL builds on are
therefore introduced here as named `axiom`s rather than proved.

This is deliberately **not** `sorry`: a `sorry` is an unproved *gap* in something we claim
to prove, whereas these are *citations* of established mathematics outside Mathlib's
current scope. Any theorem that uses them lists them by name under `#print axioms`, so the
dependence on a cited fact is always auditable. (The `lean-sorry-gate` hook flags added
axioms for exactly this reason — to keep them visible.)
-/

namespace IGL

/-- (CITED) A Green's kernel for the chosen elliptic operator `L`: the integral kernel
`G` with `u = G * f` solving `L u = f`. Posited per operator; not constructed in Mathlib. -/
axiom greensKernel (d : ℕ) : (Fin d → ℝ) → (Fin d → ℝ) → ℝ

/-- The separable rank needed to approximate the Green's kernel to accuracy `ε`. -/
axiom expSumRank : ℝ → ℕ

end IGL
