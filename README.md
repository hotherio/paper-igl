# paper-igl

**Intrinsic Green's Learning (IGL)** — the seminal paper.

IGL models a target function on a manifold as the solution of a linear PDE whose *source* is
learned from data: rather than approximating the target directly, it learns a source and
integrates it against a Green's kernel. An encoder discovers a low-dimensional chart on which
both the source and the kernel decompose, giving a finite separable **Master Formula** with
linear-in-intrinsic-dimension cost.

## Layout

```
paper/
  main.tex            LaTeX source (Intrinsic Green's Learning)
  math_commands.tex   macros
  iclr2026_conference.{bib,bst,sty}, fancyhdr.sty, natbib.sty   style + bibliography
  figures/            figures referenced by main.tex
```

## Building

```bash
cd paper && latexmk -pdf main.tex
# or: pdflatex main.tex && bibtex main && pdflatex main.tex && pdflatex main.tex
```

Build artifacts (`*.aux`, `*.log`, `main.pdf`, …) are gitignored.

## Formalization

A Lean 4 / Mathlib formalization of the IGL theory lives in [`lean/`](lean/). It
kernel-checks (Lean 4.30.0, Mathlib v4.30.0) the paper's theorems:

- the **Master Formula** / factorized integral and its `d`-fold Fubini core, with the
  **KAN** (`G = Id`), **Additive-Green** (`K = 1`), and **gauge-invariance** corollaries;
- the **spectral** factorized integral (`Igl/Spectral.lean`);
- the **separability barrier** — sufficiency, plus a concrete necessity witness
  (`Igl/Barrier.lean`);
- **CP-rank** sub-additivity / sub-multiplicativity and **rank-friendly differentiation**
  (`Igl/Rank.lean`).

The only cited axiom is the Braess–Hackbusch exponential-sum bound `K = O(log 1/ε)`
(`Igl/Classical.lean`), made explicit and auditable via `#print axioms` — no `sorry`.
A natural-language proof blueprint is in [`lean/blueprint/`](lean/blueprint/); see
[`lean/RESEARCH.md`](lean/RESEARCH.md) for the formalization ledger.

```bash
cd lean && lake exe cache get && lake build
```

## Related

- **Python package** — [`hotherio/intrinsic-green-learning`](https://github.com/hotherio/intrinsic-green-learning).
