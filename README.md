# QCW-GMCR: A Four-Valued Graph Model for Conflict Resolution, Formalized in Lean 4

Machine-checked formalization of the core of the **Quasi-Closed World Graph
Model for Conflict Resolution (QCW-GMCR)** — an extension of the standard
Graph Model for Conflict Resolution (GMCR) with Belnap's four-valued logic
for representing epistemic ambiguity at the option level.

Companion repository for the preprint:

> Yukiko Kato, *A Four-Valued Graph Model for Conflict Resolution: Core
> Framework and a Machine-Checked Formalization in Lean 4*. Preprint forthcoming on arXiv.

## Contents

```
Basic.lean          -- the formalization (classical GMCR + coalition stability + four-valued layer)
Robust.lean         -- robust stability under epistemic disturbance (Lean core only)
lakefile.toml       -- Lake project configuration (mathlib dependency)
lean-toolchain      -- pinned Lean version (leanprover/lean4:v4.21.0)
lake-manifest.json  -- resolved dependency revisions (exact mathlib commit)

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

### Part 4 — Robust stability under epistemic disturbance (`Robust.lean`)

Companion formalization for the preprint *Robust Stability under Epistemic
Disturbance in the Graph Model for Conflict Resolution* (Y. Kato), the sequel to
*Epistemic Disturbance in the Graph Model for Conflict Resolution*
(arXiv:2610.11690). `Robust.lean` is self-contained (Lean core only; it does not
import Mathlib or `Basic.lean`); its four-valued layer (`Val4`, `conj`, the
knowledge order, `delta_cons/prec/opt/cont`) follows the definitions of
`Basic.lean`, inside the namespace `RobustGMCR`. Stability is stated in a
perceived model with legal sequences of opponents' moves and, for SEQ, credible
moves, as in the preprint.

- **Verified:** monotonicity of Nash, GMR, SMR and SEQ stability in move sets
  (`stable_mono`); soundness of the pessimistic and optimistic tests
  (`sound_pess`, `sound_opt`) for any set of epistemic states containing the
  reachable set; reachable sets lie in the product of componentwise closures
  and, under monotone accumulation, in the upper set of the start
  (`reach_local`, `reach_upset`), giving the evidence-agnostic test
  (`sound_agnostic`); exactness of the pessimistic test for product sets of
  epistemic states under componentwise operators (`exact_pess`,
  `exact_robust_iff`), with `delta_prec`, `delta_cont` and `delta_cons` shown
  componentwise (`prec_componentwise`, `cont_componentwise`,
  `cons_componentwise`) and `delta_opt` shown not to be
  (`opt_not_componentwise`); from definite starts, the collapse of `delta_opt`
  to `delta_prec` and of `delta_cons` to `delta_cont` (`opt_eq_prec_of_ne_U`,
  `cons_eq_cont_of_ne_U`, `conjList_ne_U`), and the bluff/denial theorem at
  the level of perceived models (`bluff_model`, `denial_model`).
- `#print axioms`: `stable_mono`, `sound_pess`, `sound_opt`, the hierarchy
  theorems and `stable_legal_imp_unrestricted` use no axioms;
  the other listed theorems use only `propext` (and, for exactness,
  `Classical.choice` and `Quot.sound`). No `sorry`.
- **Legal versus unrestricted reachability:** `Stable` uses legal sequences
  (no DM moves twice in succession; Fang–Hipel–Kilgour 1993), `StableU` the
  unrestricted reachability used by `CMove`/`CUI` in `Basic.lean`. Verified:
  legal ⊆ unrestricted reachability (`LReach.toUReach`, the analogue of
  `lmove_imp_cmove`); legal stability implies unrestricted stability for Nash,
  GMR, SMR and SEQ (`stable_legal_imp_unrestricted`); the hierarchy
  Nash ⇒ SMR ⇒ GMR and Nash ⇒ SEQ ⇒ GMR for both definitions
  (`nash_imp_smr`, `smr_imp_gmr`, `nash_imp_seq`, `seq_imp_gmr` and their
  `…U` versions; SEQ ⇒ GMR under `CredSub`, which holds in every perceived
  model by `perceived_credSub`); and a four-state model in which a state is
  GMR-stable with unrestricted but not with legal reachability
  (`LegalCounterexample.unrestricted_gmr`, `LegalCounterexample.not_legal_gmr`).
- Not formalized (proved in the preprint): the equality of the reachable set
  with the product of componentwise closures for separable actions, exactness
  for additive sign-coherent actions, and the results on equilibria, sequences
  by a single actor and coalitions.

Note: `Basic.lean` states GMR/SMR/SEQ with unrestricted coalition reachability
(`CMove`, `CUI`), whereas the standard definitions, the preprints and
`Robust.lean` use legal sequences (no DM moves twice in succession). The two
definitions differ when an opponent's graph is not transitive; legal stability
implies unrestricted stability, and the hierarchy holds for both (see above).

All results in the repository compile without `sorry`.

## Building

Requires [elan](https://github.com/leanprover/elan), which reads
`lean-toolchain` and installs the pinned Lean automatically. From the
repository root:

```bash
lake exe cache get   # fetch prebuilt mathlib for the pinned revision
lake build           # compiles Basic.lean and Robust.lean; succeeds iff all theorems check
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



## License

TBD (e.g., Apache-2.0 for code; arXiv license for the paper).
