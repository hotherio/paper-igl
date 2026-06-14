# Research ledger — IGL (Intrinsic Green's Learning)

> The `lean-math:math-research` orchestrator reads and updates this file. It records *where we
> are*; the `blueprint/` graph + `bin/axiom-report` are the source of truth for *what is proved*.

## Snapshot
- **Entry point:** existing formalization, extended to cover the full paper
- **Current phase:** F formalize — closed the paper→formalization gap (spectral form, separability
  barrier if-direction + necessity witness, CP-rank bounds, rank-friendly differentiation);
  18/19 nodes clean, 1 cited axiom.
- **Home:** vendored into `paper-igl/lean` (this directory), alongside the paper (per user).
- **Last updated:** 2026-06-14

## Conjecture / claims
- **Main claim:** IGL's Green's-integral operator factorises into a finite separable
  rank-K×R sum (the Master Formula), with gauge/change-of-variables invariance and the
  KAN (G=Id) and Additive-Green (K=1) reductions as corollaries.
- **Sub-claims / lemmas:** rank-1 & d-fold separable factorization (Fubini), separable
  source/kernel, particular IGL instance, gauge invariance, KAN reduction, additive-Green
  reduction, exponential-sum separable rank bound K=O(log 1/ε).
- **Success criteria:** Tier-1 results kernel-checked clean; Tier-3 analytic facts may be
  cited as axioms (explicitly, surfaced by `#print axioms`).

## Gate decisions (append-only log)
| Date | Gate | Decision | Why |
| --- | --- | --- | --- |
| 2026-06-14 | G: status acceptable? | **LOOP BACK — build it** | discharge `expSumRank_logBound`: D coverage → F formalize, then re-check G |
| 2026-06-14 | D: build vs axiomatize | **PENDING — user** | coverage done: scaffolding Present (Gaussian integral, trapezoid defs, Poisson summation), but the quantitative exp-convergence quadrature bound is Missing (real new analysis dev; crux = uniform Poisson-tail rate) |
| 2026-06-14 | exp-sum bound | **KEEP as cited axiom** (user) | established math outside Mathlib; auditable via `#print axioms`, not `sorry` |
| 2026-06-14 | formalization home | **VENDOR into `paper-igl/lean`** (user) | proofs live alongside the paper |
| 2026-06-14 | scope | **all 4 gap theorems + necessity witness** (user) | spectral, barrier-if, diff-rank, CP-rank bounds, + d=2 ¬rank-1 |

## Node status (refresh from `bin/axiom-report`)
| Node (`\lean{}` name) | Status | Notes |
| --- | --- | --- |
| IGL.separableSource | clean | |
| IGL.separableKernel | clean | |
| IGL.partialIntegral | clean | |
| IGL.iglParticular | clean | |
| igl_separable_factorization | clean | rank-1 factorization |
| IGL.fubini_dfold | clean | d-fold separable |
| IGL.fubini_factorization | clean | Master Formula |
| IGL.kan_reduction | clean | G=Id corollary |
| IGL.additiveGreen_factorization | clean | K=1 corollary |
| IGL.gauge_invariance | clean | change-of-variables invariance |
| IGL.exp_neg_sum_eigs | clean | additive eigenvalues → product (Spectral.lean) |
| IGL.spectral_factorization | clean | spectral factorized integral (Spectral.lean) |
| IGL.HasCPRank | clean | constructive CP-rank predicate (Rank.lean) |
| IGL.separableSource_hasCPRank | clean | rank-R source has CP-rank R |
| IGL.HasCPRank.add | clean | sub-additivity rank(f+g)≤rank f+rank g |
| IGL.HasCPRank.mul | clean | sub-multiplicativity rank(f·g)≤rank f·rank g |
| IGL.applyCoordOp_hasCPRank | clean | differentiation rank-friendly (≤ R·d) |
| IGL.barrier_if_factorization | clean | separability barrier, if-direction (Barrier.lean) |
| IGL.barrierWitness_not_rank_one | clean | barrier necessity, d=2 ¬rank-1 witness |
| IGL.expSumRank_logBound | **axiom** | depends on `IGL.expSumRank`, `IGL.greensKernel` — Tier-3 elliptic-Green's exp-sum bound, cited axiom (kept per user) |

## Citations to carry into the write-up
- Quemy, A. (2026). *Intrinsic Green's Learning.* https://quemy.info/2026-03-21-intrinsic-greens-learning.html — (formatting handled by `aq:scientific-writing`)

## Open questions / next step
- Optional Phase H: prose write-up of the proofs via `lean-math:blueprint-pdf` (the blueprint
  graph is already updated with the new nodes).
- The exp-sum bound `expSumRank_logBound` remains the single cited axiom (kept by decision).
