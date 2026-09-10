# QCW-GMCR: A Four-Valued Graph Model for Conflict Resolution, Formalized in Lean 4

Machine-checked formalization of the core of the **Quasi-Closed World Graph
Model for Conflict Resolution (QCW-GMCR)** — an extension of the standard
Graph Model for Conflict Resolution (GMCR) with Belnap's four-valued logic
for representing epistemic ambiguity at the option level.

Companion repository for the preprint:

> Yukiko Kato, *A Four-Valued Graph Model for Conflict Resolution: Core
> Framework and a Machine-Checked Formalization in Lean 4*, arXiv:XXXX.XXXXX.

## Contents

```
Basic.lean          -- the formalization (classical GMCR + coalition stability + four-valued layer)
lakefile.toml       -- Lake project configuration (mathlib dependency)
lean-toolchain      -- pinned Lean version (leanprover/lean4:v4.21.0)
lake-manifest.json  -- resolved dependency revisions (exact mathlib commit)
paper/              -- arXiv preprint (qcw_gmcr_arxiv.tex, .pdf)
```

The pinned `lean-toolchain` and the mathlib revision recorded in
`lake-manifest.json` fix the exact environment under which every theorem
compiles without `sorry`, so the claim is independently reproducible from
this commit.

### Part 1 — Classical GMCR

- `GraphModel`: graph models over arbitrary types of DMs and states, with
  moves and strict preferences as raw relations (no axioms — the results
  below hold even for intransitive preferences). A sanction to `u` is
  required to satisfy `¬ (pref i u s)`, matching the paper's shorthand
  `s ≿ᵢ t := ¬(t ≻ᵢ s)`.
- Unilateral improvements (`UI`), coalitional reachability (`CMove`, `CUI`),
  and the four standard stability concepts (`NashStable`, `GMRStable`,
  `SMRStable`, `SEQStable`).
- **Verified:** the classical stability hierarchy
  Nash ⊆ SMR ⊆ GMR and Nash ⊆ SEQ ⊆ GMR, improvement reachability ⊆
  reachability (`cui_imp_cmove`), and legal (Fang–Hipel–Kilgour) ⊆
  unrestricted reachability (`lmove_imp_cmove`).

### Part 2 — Coalition stability

- Classical coalition stability over the same `GraphModel`, reusing the
  coalition-general reachability of Part 1: coalitional Nash, GMR, SMR, and
  SEQ stability (`CNash/CGMR/CSMR/CSEQStableForCoalition/ForDM/Equilibrium`),
  with class-based opponent responses (`ClassStepMove`, `R_C`,
  `ClassStepImprove`, `R_C_double_plus`) and an explicit indifference
  relation with weak-order axioms available (unused by the theorems below).
- **Verified:** the coalitional hierarchy CNash ⊆ CSMR ⊆ CGMR and
  CNash ⊆ CSEQ ⊆ CGMR (`cnash_implies_csmr`, `csmr_implies_cgmr`,
  `cseq_implies_cgmr`, plus composed `cnash_implies_cgmr`,
  `cnash_implies_cseq`), and class improvement ⊆ class reachability
  (`R_C_dpp_subset_R_C`).

### Part 3 — Four-valued layer (QCW-GMCR)

- `Val4`: Belnap's truth space {Y, N, YN, U} with decidable equality;
  four-valued conjunction (`Val4.conj`), transition-warrant connective
  (`Val4.entail`), knowledge order (`le_k`).
- **Verified:** commutativity / associativity / idempotence of conjunction,
  absorption by N (`conj_N_left`), identity of Y (`conj_Y_left`);
  compositional propagation over arbitrary finite option sets
  (`propagation_property_i`, `propagation_property_iv`); the four canonical
  reduction operators (`delta_cons`, `delta_prec`, `delta_opt`,
  `delta_cont`) with classical extension and truth monotonicity
  (`*_truth_monotone`) — including the machine-checked **refutation** of
  knowledge monotonicity for `delta_cons`, `delta_opt`, `delta_cont`
  (`*_not_knowledge_monotone`; only `delta_prec` is knowledge-monotone);
  the graded reachability hierarchy (`definite_imp_credible`,
  `credible_imp_possible`).
- Computable set-difference definition of the quasi-closed state space
  (`qcwStateSpace`, the `S_reduced \ (F ∪ B)` part of Def. 5.7; the boundary
  construction `B = {s : ∃ i f, s →ᵢ f}` is not itself formalized), and the
  subjective assessment/preference core of the hypergame structure
  (`QcwHypergame`) with a shared-safe-core membership predicate over supplied
  subjective state spaces (`is_in_shared_safe_core`).

All results in the repository compile without `sorry`.

## Building

Requires [elan](https://github.com/leanprover/elan), which reads
`lean-toolchain` and installs the pinned Lean automatically. From the
repository root:

```bash
lake exe cache get   # fetch prebuilt mathlib for the pinned revision
lake build           # compiles Basic.lean; succeeds iff all theorems check
```

A successful `lake build` is the reproduction of the paper's central claim:
every listed theorem checks under the pinned Lean/mathlib environment with no
`sorry`. The committed `lake-manifest.json` pins the exact mathlib commit, so
`lake build` resolves the same dependencies on any machine. Opening the folder
in VS Code with the Lean 4 extension additionally provides interactive goal
states.

## Roadmap

Next formalization targets (informal proofs given in the preprint): the
corrected FDE characterization of definite reachability (Prop. 4.7) and the
finite hypergame-existence counterexample (Remark 8.1) — both proved on paper;
the quasi-closed world invariant (Thm. 5.8); path entailment decay (Thm. 4.9);
the level-ℓ stability hierarchy over full graph models (Thm. 6.2); the level-ℓ
grading of the coalitional concepts (their classical core is verified); and
the corrected hypergame CA-equilibrium existence theorem (Thm. 8.2). The
exhaustiveness of the four deterministic classical-extension reduction
operators (Thm. 5.5) is proved in the preprint, and its per-operator axioms
are machine-checked.

## Citation

```bibtex
@misc{kato2026qcwgmcr,
  title   = {A Four-Valued Graph Model for Conflict Resolution:
             Core Framework and a Machine-Checked Formalization in Lean 4},
  author  = {Kato, Yukiko},
  year    = {2026},
  eprint  = {XXXX.XXXXX},
  archivePrefix = {arXiv}
}
```

## License

TBD (e.g., Apache-2.0 for code; arXiv license for the paper).
