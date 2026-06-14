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

## Related

- **Lean formalization** of the IGL theory (rank-1 / d-fold separable factorization, the
  Master Formula, gauge invariance, the KAN and Additive-Green reductions) is maintained as a
  separate formalization project — home TBD; not vendored here.
- **Python package** — [`hotherio/intrinsic-green-learning`](https://github.com/hotherio/intrinsic-green-learning).
