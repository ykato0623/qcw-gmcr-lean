/-
  Robust stability under epistemic disturbance in the graph model for
  conflict resolution: machine-checked core results.

  Self-contained (Lean core only, no Mathlib). The four-valued layer
  (`Val4`, `conj`, the knowledge order and the reduction operators
  `delta_cons`, `delta_prec`, `delta_opt`, `delta_cont`) follows the
  definitions of `Basic.lean` in the QCW-GMCR development; everything is placed
  in the namespace `RobustGMCR` to avoid clashes.

  Correspondence with the paper:
  * `stable_mono`              : monotonicity of stability in move sets
                                 (Lemma 2.1, after Kato, arXiv:2610.11690)
  * `sound_pess`, `sound_opt`  : Theorem 4.2 (soundness)
  * `reach_upset`, `reach_local`, `sound_agnostic`
                               : Proposition 5.2 (a), (b) and the
                                 evidence-agnostic test
  * `exact_pess`, `exact_robust_iff`
                               : Theorem 6.1 (exactness), for product
                                 reachable sets and the operators
                                 `delta_prec`, `delta_cont`, `delta_cons`
  * `opt_not_componentwise`    : the obstruction for `delta_opt` (cf. Example 6.2)
  * `opt_eq_prec_of_ne_U`, `cons_eq_cont_of_ne_U`, `conjList_ne_U`
                               : Proposition 8.1 (b)
  * `bluff_add`, `denial_remove`, `bluff_model`, `denial_model`
                               : Theorem 8.3 (bluff and denial)

  Legal versus unrestricted reachability:
  * `Stable` uses legal sequences (no DM moves twice in succession), as in
    Fang–Hipel–Kilgour (1993) and the preprints; `StableU` uses unrestricted
    sequences, as `CMove`/`CUI` in `Basic.lean`.
  * `LReach.toUReach`           : legal ⊆ unrestricted (cf. `lmove_imp_cmove`)
  * `stable_legal_imp_unrestricted`
                               : legal stability implies unrestricted stability
  * `nash_imp_smr`, `smr_imp_gmr`, `nash_imp_seq`, `seq_imp_gmr` (legal) and
    `nash_imp_smrU`, `smr_imp_gmrU`, `nash_imp_seqU`, `seq_imp_gmrU`
    (unrestricted)             : the stability hierarchy for both definitions
  * `LegalCounterexample.unrestricted_gmr`, `LegalCounterexample.not_legal_gmr`
                               : the converse fails (a non-transitive opponent)
-/

namespace RobustGMCR

/-! ## Four-valued layer (as in `Basic.lean`) -/

inductive Val4
  | N   -- definite false
  | U   -- unknown
  | YN  -- both
  | Y   -- definite true
  deriving DecidableEq, Repr

namespace Val4

def conj : Val4 → Val4 → Val4
  | Y,  x  => x
  | x,  Y  => x
  | N,  _  => N
  | _,  N  => N
  | YN, U  => N
  | U,  YN => N
  | YN, YN => YN
  | U,  U  => U

/-- Knowledge order, as a Boolean test (the same relation as `le_k` in `Basic.lean`). -/
def leKb : Val4 → Val4 → Bool
  | U,  _   => true
  | _,  YN  => true
  | N,  N   => true
  | Y,  Y   => true
  | _,  _   => false

def le_k (a b : Val4) : Prop := leKb a b = true

theorem le_k_refl (a : Val4) : le_k a a := by
  cases a <;> rfl

theorem le_k_trans {a b c : Val4} (h1 : le_k a b) (h2 : le_k b c) : le_k a c := by
  unfold le_k at *
  cases a <;> cases b <;> cases c <;> simp_all [leKb]

theorem le_k_antisymm {a b : Val4} (h1 : le_k a b) (h2 : le_k b a) : a = b := by
  unfold le_k at *
  cases a <;> cases b <;> simp_all [leKb]

/-- Conjunction is monotone in the knowledge order. -/
theorem conj_le_k {a a' b b' : Val4} (h1 : le_k a a') (h2 : le_k b b') :
    le_k (conj a b) (conj a' b') := by
  unfold le_k at *
  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all [leKb, conj]

/-- The four reduction operators (as in `Basic.lean`):
`delta_cons` = δ_NN, `delta_prec` = δ_NY, `delta_opt` = δ_YY, `delta_cont` = δ_YN. -/
def delta_cons : Val4 → Bool
  | Y => true
  | _ => false

def delta_prec : Val4 → Bool
  | Y  => true
  | YN => true
  | _  => false

def delta_opt : Val4 → Bool
  | N => false
  | _ => true

def delta_cont : Val4 → Bool
  | Y => true
  | U => true
  | _ => false

end Val4

open Val4

/-! ## Stability in a perceived model, with legal sequences -/

section Stability

variable {N S : Type}

/-- A perceived model: the moves each DM is perceived to have, and the moves
of each DM that are perceived to be credible (used for opponents in SEQ). -/
structure PModel (N S : Type) where
  mv   : N → S → S → Prop
  cred : N → S → S → Prop

/-- Nonempty legal sequences of moves by DMs other than `i` along `r`, in which
no DM moves twice in succession; `LReach r i s j t` records the last mover `j`. -/
inductive LReach (r : N → S → S → Prop) (i : N) : S → N → S → Prop
  | single {j : N} {s t : S} : j ≠ i → r j s t → LReach r i s j t
  | cons {j k : N} {s t u : S} : j ≠ i → j ≠ k → LReach r i s k t → r j t u →
      LReach r i s j u

theorem LReach.mono {r r' : N → S → S → Prop} {i : N}
    (h : ∀ j, j ≠ i → ∀ s t, r j s t → r' j s t) {s : S} {j : N} {t : S}
    (hr : LReach r i s j t) : LReach r' i s j t := by
  induction hr with
  | single hj hm => exact LReach.single hj (h _ hj _ _ hm)
  | cons hj hjk _ hm ih => exact LReach.cons hj hjk ih (h _ hj _ _ hm)

inductive Concept
  | nash | gmr | smr | seq

variable (pref : N → S → S → Prop)

/-- Stability of `s` for `i` in the perceived model `P`. A sanction ends at a
state `u` with `¬ pref i u s` (i.e. `s ≿ᵢ u`). -/
def Stable (P : PModel N S) (c : Concept) (i : N) (s : S) : Prop :=
  match c with
  | .nash => ∀ t, ¬ (P.mv i s t ∧ pref i t s)
  | .gmr  => ∀ t, P.mv i s t → pref i t s →
      ∃ u k, LReach P.mv i t k u ∧ ¬ pref i u s
  | .smr  => ∀ t, P.mv i s t → pref i t s →
      ∃ u k, LReach P.mv i t k u ∧ ¬ pref i u s ∧ ∀ v, P.mv i u v → ¬ pref i v s
  | .seq  => ∀ t, P.mv i s t → pref i t s →
      ∃ u k, LReach P.cred i t k u ∧ ¬ pref i u s

/-- `Q` is at least as favourable to stability for `i` as `P`: fewer own moves,
more opponents' moves and credible moves. -/
def Favours (i : N) (P Q : PModel N S) : Prop :=
  (∀ s t, Q.mv i s t → P.mv i s t) ∧
  (∀ j, j ≠ i → ∀ s t, P.mv j s t → Q.mv j s t) ∧
  (∀ j, j ≠ i → ∀ s t, P.cred j s t → Q.cred j s t)

/-- Monotonicity of stability in move sets (both directions at once). -/
theorem stable_mono {i : N} {P Q : PModel N S} (h : Favours i P Q)
    (c : Concept) (s : S) (hs : Stable pref P c i s) : Stable pref Q c i s := by
  obtain ⟨hown, hopp, hcred⟩ := h
  cases c with
  | nash =>
      intro t ht
      exact hs t ⟨hown _ _ ht.1, ht.2⟩
  | gmr =>
      intro t hm hp
      obtain ⟨u, k, hr, hu⟩ := hs t (hown _ _ hm) hp
      exact ⟨u, k, LReach.mono hopp hr, hu⟩
  | smr =>
      intro t hm hp
      obtain ⟨u, k, hr, hu, hesc⟩ := hs t (hown _ _ hm) hp
      exact ⟨u, k, LReach.mono hopp hr, hu, fun v hv => hesc v (hown _ _ hv)⟩
  | seq =>
      intro t hm hp
      obtain ⟨u, k, hr, hu⟩ := hs t (hown _ _ hm) hp
      exact ⟨u, k, LReach.mono hcred hr, hu⟩

theorem stable_congr {i : N} {P Q : PModel N S} (h1 : Favours i P Q) (h2 : Favours i Q P)
    (c : Concept) (s : S) : Stable pref P c i s ↔ Stable pref Q c i s :=
  ⟨stable_mono pref h1 c s, stable_mono pref h2 c s⟩

/-! ## Legal versus unrestricted reachability

The standard definitions (Fang, Hipel and Kilgour 1993) use legal sequences, in
which no DM moves twice in succession; `Stable` above follows them.
`Basic.lean` states GMR, SMR and SEQ with unrestricted reachability
(`CMove (opp i)`, `CUI (opp i)`: transitive closures of the opponents' joint
moves and improvements). `UReach` and `StableU` below are the corresponding
unrestricted notions. -/

/-- Unrestricted reachability: nonempty sequences of moves by DMs other than `i`
along `r`, with no restriction on consecutive movers. -/
inductive UReach (r : N → S → S → Prop) (i : N) : S → S → Prop
  | single {j : N} {s t : S} : j ≠ i → r j s t → UReach r i s t
  | tail {j : N} {s t u : S} : UReach r i s t → j ≠ i → r j t u → UReach r i s u

/-- The last mover of a legal sequence is not `i`. -/
theorem LReach.last_ne {r : N → S → S → Prop} {i : N} {s : S} {j : N} {t : S}
    (h : LReach r i s j t) : j ≠ i := by
  cases h with
  | single hj _ => exact hj
  | cons hj _ _ _ => exact hj

/-- Legal sequences are sequences (the analogue of `lmove_imp_cmove` in `Basic.lean`). -/
theorem LReach.toUReach {r : N → S → S → Prop} {i : N} {s : S} {j : N} {t : S}
    (h : LReach r i s j t) : UReach r i s t := by
  induction h with
  | single hj hm => exact UReach.single hj hm
  | cons hj _ _ hm ih => exact UReach.tail ih hj hm

/-- Stability with unrestricted reachability (the form used in `Basic.lean`). -/
def StableU (P : PModel N S) (c : Concept) (i : N) (s : S) : Prop :=
  match c with
  | .nash => ∀ t, ¬ (P.mv i s t ∧ pref i t s)
  | .gmr  => ∀ t, P.mv i s t → pref i t s →
      ∃ u, UReach P.mv i t u ∧ ¬ pref i u s
  | .smr  => ∀ t, P.mv i s t → pref i t s →
      ∃ u, UReach P.mv i t u ∧ ¬ pref i u s ∧ ∀ v, P.mv i u v → ¬ pref i v s
  | .seq  => ∀ t, P.mv i s t → pref i t s →
      ∃ u, UReach P.cred i t u ∧ ¬ pref i u s

/-- Stability with legal sequences implies stability with unrestricted sequences,
for every concept: the legal definition is the more demanding one. -/
theorem stable_legal_imp_unrestricted (P : PModel N S) (c : Concept) (i : N) (s : S)
    (h : Stable pref P c i s) : StableU pref P c i s := by
  cases c with
  | nash => exact h
  | gmr =>
      intro t hm hp
      obtain ⟨u, _, hr, hu⟩ := h t hm hp
      exact ⟨u, hr.toUReach, hu⟩
  | smr =>
      intro t hm hp
      obtain ⟨u, _, hr, hu, hesc⟩ := h t hm hp
      exact ⟨u, hr.toUReach, hu, hesc⟩
  | seq =>
      intro t hm hp
      obtain ⟨u, _, hr, hu⟩ := h t hm hp
      exact ⟨u, hr.toUReach, hu⟩

/-- Credible moves of the opponents are among their moves (in the standard model:
unilateral improvements are unilateral moves). -/
def CredSub (P : PModel N S) (i : N) : Prop :=
  ∀ j, j ≠ i → ∀ s t, P.cred j s t → P.mv j s t

theorem UReach.mono {r r' : N → S → S → Prop} {i : N}
    (h : ∀ j, j ≠ i → ∀ s t, r j s t → r' j s t) {s t : S}
    (hr : UReach r i s t) : UReach r' i s t := by
  induction hr with
  | single hj hm => exact UReach.single hj (h _ hj _ _ hm)
  | tail _ hj hm ih => exact UReach.tail ih hj (h _ hj _ _ hm)

/-! ### The stability hierarchy, for both definitions -/

section Hierarchy

variable {P : PModel N S} {i : N} {s : S}

theorem nash_imp_smr (h : Stable pref P .nash i s) : Stable pref P .smr i s :=
  fun t hm hp => absurd ⟨hm, hp⟩ (h t)

theorem smr_imp_gmr (h : Stable pref P .smr i s) : Stable pref P .gmr i s :=
  fun t hm hp =>
    let ⟨u, k, hr, hu, _⟩ := h t hm hp
    ⟨u, k, hr, hu⟩

theorem nash_imp_seq (h : Stable pref P .nash i s) : Stable pref P .seq i s :=
  fun t hm hp => absurd ⟨hm, hp⟩ (h t)

theorem seq_imp_gmr (hcs : CredSub P i) (h : Stable pref P .seq i s) :
    Stable pref P .gmr i s :=
  fun t hm hp =>
    let ⟨u, k, hr, hu⟩ := h t hm hp
    ⟨u, k, LReach.mono hcs hr, hu⟩

theorem nash_imp_smrU (h : StableU pref P .nash i s) : StableU pref P .smr i s :=
  fun t hm hp => absurd ⟨hm, hp⟩ (h t)

theorem smr_imp_gmrU (h : StableU pref P .smr i s) : StableU pref P .gmr i s :=
  fun t hm hp =>
    let ⟨u, hr, hu, _⟩ := h t hm hp
    ⟨u, hr, hu⟩

theorem nash_imp_seqU (h : StableU pref P .nash i s) : StableU pref P .seq i s :=
  fun t hm hp => absurd ⟨hm, hp⟩ (h t)

theorem seq_imp_gmrU (hcs : CredSub P i) (h : StableU pref P .seq i s) :
    StableU pref P .gmr i s :=
  fun t hm hp =>
    let ⟨u, hr, hu⟩ := h t hm hp
    ⟨u, UReach.mono hcs hr, hu⟩

end Hierarchy

/-! ## Pessimistic and optimistic models; soundness (Theorem 4.2) -/

variable {K : Type}

/-- Pessimistic model over a set `R` of epistemic states: own moves of `i`
perceived at some state of `R`; other DMs' (credible) moves perceived at every
state of `R`. -/
def pess (P : K → PModel N S) (R : K → Prop) (i : N) : PModel N S where
  mv j s t := (j = i → ∃ κ, R κ ∧ (P κ).mv j s t) ∧ (j ≠ i → ∀ κ, R κ → (P κ).mv j s t)
  cred j s t := ∀ κ, R κ → (P κ).cred j s t

/-- Optimistic model: the reverse. -/
def opt (P : K → PModel N S) (R : K → Prop) (i : N) : PModel N S where
  mv j s t := (j = i → ∀ κ, R κ → (P κ).mv j s t) ∧ (j ≠ i → ∃ κ, R κ ∧ (P κ).mv j s t)
  cred j s t := ∃ κ, R κ ∧ (P κ).cred j s t

theorem favours_pess (P : K → PModel N S) (R : K → Prop) (i : N) {κ : K} (hκ : R κ) :
    Favours i (pess P R i) (P κ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t h
    exact ⟨fun _ => ⟨κ, hκ, h⟩, fun hne => absurd rfl hne⟩
  · intro j hj s t h
    exact h.2 hj κ hκ
  · intro j _ s t h
    exact h κ hκ

theorem favours_opt (P : K → PModel N S) (R : K → Prop) (i : N) {κ : K} (hκ : R κ) :
    Favours i (P κ) (opt P R i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t h
    exact h.1 rfl κ hκ
  · intro j hj s t h
    exact ⟨fun hji => absurd hji hj, fun _ => ⟨κ, hκ, h⟩⟩
  · intro j _ s t h
    exact ⟨κ, hκ, h⟩

/-- Theorem 4.2 (a): stability in the pessimistic model implies stability at
every epistemic state of `R` (in particular, of any reachable set contained in `R`). -/
theorem sound_pess (P : K → PModel N S) (R : K → Prop) (i : N) (c : Concept) (s : S)
    (h : Stable pref (pess P R i) c i s) : ∀ κ, R κ → Stable pref (P κ) c i s :=
  fun _ hκ => stable_mono pref (favours_pess P R i hκ) c s h

/-- Theorem 4.2 (b): instability in the optimistic model implies instability at
every epistemic state of `R`. -/
theorem sound_opt (P : K → PModel N S) (R : K → Prop) (i : N) (c : Concept) (s : S)
    (h : ¬ Stable pref (opt P R i) c i s) : ∀ κ, R κ → ¬ Stable pref (P κ) c i s :=
  fun _ hκ hst => h (stable_mono pref (favours_opt P R i hκ) c s hst)

/-- Soundness transfers to any subset (e.g. the reachable set) of `R`. -/
theorem sound_pess_subset (P : K → PModel N S) (R Rch : K → Prop) (hsub : ∀ κ, Rch κ → R κ)
    (i : N) (c : Concept) (s : S) (h : Stable pref (pess P R i) c i s) :
    ∀ κ, Rch κ → Stable pref (P κ) c i s :=
  fun κ hκ => sound_pess pref P R i c s h κ (hsub κ hκ)

end Stability

/-! ## Reachable sets and their over-approximations (Proposition 5.2) -/

section Reach

variable {C : Type}

/-- A local action acts on each component through its own map. -/
abbrev LocalAct (C : Type) := C → Val4 → Val4

def apply (g : LocalAct C) (κ : C → Val4) : C → Val4 := fun c => g c (κ c)

/-- Epistemic states reachable from `κ0` by finite sequences of available actions. -/
inductive Reach (A : LocalAct C → Prop) (κ0 : C → Val4) : (C → Val4) → Prop
  | base : Reach A κ0 κ0
  | step {κ : C → Val4} {g : LocalAct C} : Reach A κ0 κ → A g → Reach A κ0 (apply g κ)

/-- Componentwise closure `V_c`. -/
inductive VReach (A : LocalAct C → Prop) (κ0 : C → Val4) (c : C) : Val4 → Prop
  | base : VReach A κ0 c (κ0 c)
  | step {v : Val4} {g : LocalAct C} : VReach A κ0 c v → A g → VReach A κ0 c (g c v)

def Inflationary (g : LocalAct C) : Prop := ∀ c v, le_k v (g c v)

/-- Proposition 5.2 (b): reachable states lie in the product of the `V_c`. -/
theorem reach_local {A : LocalAct C → Prop} {κ0 κ : C → Val4} (h : Reach A κ0 κ) :
    ∀ c, VReach A κ0 c (κ c) := by
  induction h with
  | base => exact fun c => VReach.base
  | step _ hg ih => exact fun c => VReach.step (ih c) hg

/-- Proposition 5.2 (a): under monotone accumulation, reachable states lie in
the upper set of `κ0`. -/
theorem reach_upset {A : LocalAct C → Prop} (hinf : ∀ g, A g → Inflationary g)
    {κ0 κ : C → Val4} (h : Reach A κ0 κ) : ∀ c, le_k (κ0 c) (κ c) := by
  induction h with
  | base => exact fun c => le_k_refl _
  | step _ hg ih => exact fun c => le_k_trans (ih c) (hinf _ hg c _)

end Reach

/-! ## Perceived models generated by four-valued assessments -/

section Perception

variable {N S C : Type}

/-- Arc data: owner, endpoints, requirement (a list of capability components),
and the intention component assessing whether the move is an improvement for
its owner. -/
structure ArcSys (N S C : Type) where
  Arc    : Type
  owner  : Arc → N
  tail   : Arc → S
  head   : Arc → S
  req    : Arc → List C
  intent : Arc → C

/-- Warrant of a requirement list: four-valued conjunction (empty conjunction `Y`). -/
def conjList (κ : C → Val4) : List C → Val4
  | []      => Y
  | c :: cs => conj (κ c) (conjList κ cs)

def perceived (A : ArcSys N S C) (δ : Val4 → Bool) (κ : C → Val4) : PModel N S where
  mv j s t := ∃ a, A.owner a = j ∧ A.tail a = s ∧ A.head a = t ∧ δ (conjList κ (A.req a)) = true
  cred j s t := ∃ a, A.owner a = j ∧ A.tail a = s ∧ A.head a = t ∧
      δ (conjList κ (A.req a)) = true ∧ δ (κ (A.intent a)) = true

/-- In a perceived model, credible moves are perceived moves, so the hierarchy
`seq_imp_gmr` / `seq_imp_gmrU` applies without further assumptions. -/
theorem perceived_credSub (A : ArcSys N S C) (δ : Val4 → Bool) (κ : C → Val4) (i : N) :
    CredSub (perceived A δ κ) i := by
  rintro j _ s t ⟨a, ho, hs, ht, hd, _⟩
  exact ⟨a, ho, hs, ht, hd⟩

variable (pref : N → S → S → Prop)

/-- The evidence-agnostic test: if `s` is stable for `i` in the pessimistic model
over the upper set of `κ0`, it is stable at every epistemic state reachable by
inflationary actions — whatever the interpretation maps are. -/
theorem sound_agnostic (A : ArcSys N S C) (δ : Val4 → Bool) (i : N) (c : Concept) (s : S)
    (κ0 : C → Val4) (Act : LocalAct C → Prop) (hinf : ∀ g, Act g → Inflationary g)
    (h : Stable pref (pess (perceived A δ) (fun κ => ∀ x, le_k (κ0 x) (κ x)) i) c i s) :
    ∀ κ, Reach Act κ0 κ → Stable pref (perceived A δ κ) c i s :=
  sound_pess_subset pref (perceived A δ) _ (Reach Act κ0) (fun _ hκ => reach_upset hinf hκ)
    i c s h

end Perception

/-! ## Componentwise form of three operators; the obstruction for δ_YY -/

section Componentwise

variable {C : Type}

/-- `δ` acts componentwise through the predicate `p`. -/
def Componentwise (δ : Val4 → Bool) (p : Val4 → Bool) : Prop :=
  ∀ (κ : C → Val4) (l : List C), δ (conjList κ l) = true ↔ ∀ x, x ∈ l → p (κ x) = true

def hasF : Val4 → Bool
  | Y => true
  | YN => true
  | _ => false

def noA : Val4 → Bool
  | Y => true
  | U => true
  | _ => false

def isY : Val4 → Bool
  | Y => true
  | _ => false

theorem prec_conj (a b : Val4) :
    delta_prec (conj a b) = (hasF a && delta_prec b) := by
  cases a <;> cases b <;> rfl

theorem cont_conj (a b : Val4) :
    delta_cont (conj a b) = (noA a && delta_cont b) := by
  cases a <;> cases b <;> rfl

theorem cons_conj (a b : Val4) :
    delta_cons (conj a b) = (isY a && delta_cons b) := by
  cases a <;> cases b <;> rfl

theorem componentwise_of_conj {δ p : Val4 → Bool} (hY : δ Y = true)
    (hc : ∀ a b, δ (conj a b) = (p a && δ b)) : Componentwise (C := C) δ p := by
  intro κ l
  induction l with
  | nil => simp [conjList, hY]
  | cons x xs ih =>
      simp only [conjList, hc, Bool.and_eq_true, ih, List.mem_cons]
      constructor
      · rintro ⟨hx, hxs⟩ y (rfl | hy)
        · exact hx
        · exact hxs y hy
      · intro h
        exact ⟨h x (Or.inl rfl), fun y hy => h y (Or.inr hy)⟩

theorem prec_componentwise : Componentwise (C := C) delta_prec hasF :=
  componentwise_of_conj rfl prec_conj

theorem cont_componentwise : Componentwise (C := C) delta_cont noA :=
  componentwise_of_conj rfl cont_conj

theorem cons_componentwise : Componentwise (C := C) delta_cons isY :=
  componentwise_of_conj rfl cons_conj

/-- `delta_opt` (δ_YY) is not componentwise for any predicate: this is the
obstruction behind Example 6.2. -/
theorem opt_not_componentwise : ¬ ∃ p : Val4 → Bool, Componentwise (C := Bool) delta_opt p := by
  rintro ⟨p, hp⟩
  -- component `true` carries U, component `false` carries YN
  let κ : Bool → Val4 := fun b => if b then U else YN
  have hU : p U = true := by
    have := (hp κ [true]).1 (by rfl)
    exact this true (by simp)
  have hYN : p YN = true := by
    have := (hp κ [false]).1 (by rfl)
    exact this false (by simp)
  have hboth := (hp κ [true, false]).2 (by
    intro x _
    cases x
    · simpa [κ] using hYN
    · simpa [κ] using hU)
  exact absurd hboth (by decide)

end Componentwise

/-! ## Exactness for product reachable sets (Theorem 6.1) -/

section Exactness

open Classical

variable {N S C : Type}

variable (A : ArcSys N S C) (δ : Val4 → Bool) (p : Val4 → Bool) (i : N)
variable (V : C → Val4 → Prop)

/-- Product set of epistemic states. -/
def Prod (V : C → Val4 → Prop) (κ : C → Val4) : Prop := ∀ x, V x (κ x)

/-- Structural assumptions: requirements of `i`'s arcs consist of own components,
requirements and intention components of other DMs' arcs do not, and no
intention component occurs in a requirement. -/
structure Separated (Own : C → Prop) : Prop where
  own_req   : ∀ a, A.owner a = i → ∀ x, x ∈ A.req a → Own x
  other_req : ∀ a, A.owner a ≠ i → ∀ x, x ∈ A.req a → ¬ Own x
  other_int : ∀ a, A.owner a ≠ i → ¬ Own (A.intent a)
  int_req   : ∀ a b, A.owner a ≠ i → ¬ (A.intent a ∈ A.req b)

/-- The pessimistic witness: on own components choose a value satisfying `p` when
possible; on intention components a value rejected by `δ`; on the other
components a value violating `p`; otherwise any admissible value. -/
noncomputable def witness (Own : C → Prop) (hne : ∀ x, ∃ v, V x v) (x : C) : Val4 :=
  if Own x then
    (if h : ∃ v, V x v ∧ p v = true then Classical.choose h else Classical.choose (hne x))
  else if (∃ a, A.owner a ≠ i ∧ A.intent a = x) then
    (if h : ∃ v, V x v ∧ δ v = false then Classical.choose h else Classical.choose (hne x))
  else
    (if h : ∃ v, V x v ∧ p v = false then Classical.choose h else Classical.choose (hne x))

theorem witness_mem (Own : C → Prop) (hne : ∀ x, ∃ v, V x v) :
    Prod V (witness A δ p i V Own hne) := by
  intro x
  unfold witness
  split
  · split
    · rename_i h; exact (Classical.choose_spec h).1
    · exact Classical.choose_spec (hne x)
  · split
    · split
      · rename_i h; exact (Classical.choose_spec h).1
      · exact Classical.choose_spec (hne x)
    · split
      · rename_i h; exact (Classical.choose_spec h).1
      · exact Classical.choose_spec (hne x)

/-- On own components, the witness satisfies `p` whenever some admissible value does. -/
theorem witness_own (Own : C → Prop) (hne : ∀ x, ∃ v, V x v) {x : C} (hx : Own x)
    {v : Val4} (hv : V x v) (hp : p v = true) : p (witness A δ p i V Own hne x) = true := by
  have h : ∃ v, V x v ∧ p v = true := ⟨v, hv, hp⟩
  simp only [witness, hx, if_true, dif_pos h]
  exact (Classical.choose_spec h).2

/-- On other capability components, if the witness satisfies `p` then every
admissible value does. -/
theorem witness_other (Own : C → Prop) (hne : ∀ x, ∃ v, V x v) {x : C} (hx : ¬ Own x)
    (hnint : ¬ ∃ a, A.owner a ≠ i ∧ A.intent a = x)
    (hw : p (witness A δ p i V Own hne x) = true) : ∀ v, V x v → p v = true := by
  intro v hv
  by_cases h : ∃ v, V x v ∧ p v = false
  · simp only [witness, hx, if_false, hnint, dif_pos h] at hw
    have := (Classical.choose_spec h).2
    rw [this] at hw
    exact absurd hw (by decide)
  · cases hpv : p v
    · exact absurd ⟨v, hv, hpv⟩ h
    · rfl

/-- On intention components, if the witness is accepted by `δ` then every
admissible value is. -/
theorem witness_int (Own : C → Prop) (hne : ∀ x, ∃ v, V x v) {x : C} (hx : ¬ Own x)
    (hint : ∃ a, A.owner a ≠ i ∧ A.intent a = x)
    (hw : δ (witness A δ p i V Own hne x) = true) : ∀ v, V x v → δ v = true := by
  intro v hv
  by_cases h : ∃ v, V x v ∧ δ v = false
  · simp only [witness, hx, if_false, hint, if_true, dif_pos h] at hw
    have := (Classical.choose_spec h).2
    rw [this] at hw
    exact absurd hw (by decide)
  · cases hdv : δ v
    · exact absurd ⟨v, hv, hdv⟩ h
    · rfl

/-- Theorem 6.1 (exactness), pessimistic side: for a product set of epistemic
states and an operator acting componentwise, the pessimistic model is the
perceived model of a single admissible epistemic state. -/
theorem exact_pess (hcw : Componentwise (C := C) δ p) (Own : C → Prop)
    (hsep : Separated A i Own) (hne : ∀ x, ∃ v, V x v) :
    let κs := witness A δ p i V Own hne
    Prod V κs ∧ Favours i (perceived A δ κs) (pess (perceived A δ) (Prod V) i) ∧
      Favours i (pess (perceived A δ) (Prod V) i) (perceived A δ κs) := by
  intro κs
  have hmem : Prod V κs := witness_mem A δ p i V Own hne
  -- requirement components of other DMs' arcs are never intention components
  have hnint : ∀ a, A.owner a ≠ i → ∀ x, x ∈ A.req a → ¬ ∃ b, A.owner b ≠ i ∧ A.intent b = x := by
    rintro a _ x hx ⟨b, hb, rfl⟩
    exact hsep.int_req b a hb hx
  -- an other DM's arc perceived at the witness is perceived everywhere
  have hall : ∀ a, A.owner a ≠ i → δ (conjList κs (A.req a)) = true →
      ∀ κ, Prod V κ → δ (conjList κ (A.req a)) = true := by
    intro a ha hw κ hκ
    rw [hcw] at hw ⊢
    intro x hx
    exact witness_other A δ p i V Own hne (hsep.other_req a ha x hx) (hnint a ha x hx)
      (hw x hx) _ (hκ x)
  refine ⟨hmem, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · -- own moves of the pessimistic model are perceived at the witness
    intro s t h
    obtain ⟨κ, hκ, a, ho, hs, ht, hd⟩ := h.1 rfl
    refine ⟨a, ho, hs, ht, ?_⟩
    rw [hcw] at hd ⊢
    intro x hx
    exact witness_own A δ p i V Own hne (hsep.own_req a ho x hx) (hκ x) (hd x hx)
  · intro j hj s t h
    refine ⟨fun hji => absurd hji hj, fun _ κ hκ => ?_⟩
    obtain ⟨a, ho, hs, ht, hd⟩ := h
    exact ⟨a, ho, hs, ht, hall a (ho ▸ hj) hd κ hκ⟩
  · intro j hj s t h κ hκ
    obtain ⟨a, ho, hs, ht, hd, hint⟩ := h
    refine ⟨a, ho, hs, ht, hall a (ho ▸ hj) hd κ hκ, ?_⟩
    exact witness_int A δ p i V Own hne (hsep.other_int a (ho ▸ hj)) ⟨a, ho ▸ hj, rfl⟩ hint _
      (hκ _)
  · intro s t h
    exact ⟨fun _ => ⟨κs, hmem, h⟩, fun hne' => absurd rfl hne'⟩
  · intro j hj s t h
    exact h.2 hj κs hmem
  · intro j _ s t h
    exact h κs hmem

/-- Corollary: for product reachable sets and componentwise operators, robust
stability is decided exactly by the pessimistic model. -/
theorem exact_robust_iff (pref : N → S → S → Prop) (hcw : Componentwise (C := C) δ p)
    (Own : C → Prop) (hsep : Separated A i Own) (hne : ∀ x, ∃ v, V x v)
    (c : Concept) (s : S) :
    (∀ κ, Prod V κ → Stable pref (perceived A δ κ) c i s) ↔
      Stable pref (pess (perceived A δ) (Prod V) i) c i s := by
  obtain ⟨hmem, h1, h2⟩ := exact_pess A δ p i V hcw Own hsep hne
  constructor
  · intro h
    exact stable_mono pref h1 c s (h _ hmem)
  · intro h
    exact sound_pess pref (perceived A δ) (Prod V) i c s h

end Exactness

/-! ## Definite starts: operator collapse and bluff/denial (Prop. 8.1, Thm. 8.3) -/

section Definite

variable {C : Type}

theorem opt_eq_prec_of_ne_U {v : Val4} (h : v ≠ U) : delta_opt v = delta_prec v := by
  cases v <;> simp_all [delta_opt, delta_prec]

theorem cons_eq_cont_of_ne_U {v : Val4} (h : v ≠ U) : delta_cons v = delta_cont v := by
  cases v <;> simp_all [delta_cons, delta_cont]

/-- Conjunctions of values other than `U` are not `U`. -/
theorem conjList_ne_U (κ : C → Val4) (l : List C) (h : ∀ x, x ∈ l → κ x ≠ U) :
    conjList κ l ≠ U := by
  induction l with
  | nil => simp [conjList]
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs := ih (fun y hy => h y (by simp [hy]))
      simp only [conjList]
      revert hx hxs
      cases κ x <;> cases conjList κ xs <;> simp [conj]

/-- Values above a definite value are not `U`. -/
theorem ne_U_of_definite {a b : Val4} (ha : a = Y ∨ a = N) (h : le_k a b) : b ≠ U := by
  rcases ha with rfl | rfl <;> cases b <;> simp_all [le_k, leKb]

theorem conjList_single (κ : C → Val4) (x : C) : conjList κ [x] = κ x := by
  simp only [conjList]
  cases κ x <;> rfl

theorem conjList_le_k (κ0 κ : C → Val4) (h : ∀ x, le_k (κ0 x) (κ x)) (l : List C) :
    le_k (conjList κ0 l) (conjList κ l) := by
  induction l with
  | nil => exact le_k_refl _
  | cons x xs ih => exact conj_le_k (h x) ih

/-- Theorem 8.3 (a), on warrants: if the start is definite and contradiction is
read as availability (`delta_prec` or `delta_opt`), further evidence can only add
perceived moves. -/
theorem bluff_add (δ : Val4 → Bool) (hδ : δ = delta_prec ∨ δ = delta_opt)
    (κ0 κ : C → Val4) (hdef : ∀ x, κ0 x = Y ∨ κ0 x = N) (h : ∀ x, le_k (κ0 x) (κ x))
    (l : List C) (h0 : δ (conjList κ0 l) = true) : δ (conjList κ l) = true := by
  have hne0 : conjList κ0 l ≠ U :=
    conjList_ne_U κ0 l (fun x _ => ne_U_of_definite (hdef x) (le_k_refl _))
  have hne : conjList κ l ≠ U :=
    conjList_ne_U κ l (fun x _ => ne_U_of_definite (hdef x) (h x))
  have hle := conjList_le_k κ0 κ h l
  have key : delta_prec (conjList κ0 l) = true → delta_prec (conjList κ l) = true := by
    intro hp
    revert hp hle
    unfold le_k
    cases conjList κ0 l <;> cases conjList κ l <;> simp [delta_prec, leKb]
  rcases hδ with rfl | rfl
  · exact key h0
  · rw [opt_eq_prec_of_ne_U hne0] at h0
    rw [opt_eq_prec_of_ne_U hne]
    exact key h0

/-- Theorem 8.3 (b), on warrants: if the start is definite and contradiction is
read as unavailability (`delta_cont` or `delta_cons`), further evidence can only
remove perceived moves. -/
theorem denial_remove (δ : Val4 → Bool) (hδ : δ = delta_cont ∨ δ = delta_cons)
    (κ0 κ : C → Val4) (hdef : ∀ x, κ0 x = Y ∨ κ0 x = N) (h : ∀ x, le_k (κ0 x) (κ x))
    (l : List C) (h1 : δ (conjList κ l) = true) : δ (conjList κ0 l) = true := by
  have hne0 : conjList κ0 l ≠ U :=
    conjList_ne_U κ0 l (fun x _ => ne_U_of_definite (hdef x) (le_k_refl _))
  have hne : conjList κ l ≠ U :=
    conjList_ne_U κ l (fun x _ => ne_U_of_definite (hdef x) (h x))
  have hle := conjList_le_k κ0 κ h l
  have key : delta_cons (conjList κ l) = true → delta_cons (conjList κ0 l) = true := by
    intro hp
    revert hp hle hne0
    unfold le_k
    cases conjList κ0 l <;> cases conjList κ l <;> simp [delta_cons, leKb]
  rcases hδ with rfl | rfl
  · rw [← cons_eq_cont_of_ne_U hne] at h1
    rw [← cons_eq_cont_of_ne_U hne0]
    exact key h1
  · exact key h1

/-- Theorem 8.3 at the level of perceived models: for `delta_prec`/`delta_opt`
every perceived (credible) move at the start remains perceived (credible) at any
epistemic state above a definite start. -/
theorem bluff_model {Dm St : Type} (A : ArcSys Dm St C) (δ : Val4 → Bool)
    (hδ : δ = delta_prec ∨ δ = delta_opt)
    (κ0 κ : C → Val4) (hdef : ∀ x, κ0 x = Y ∨ κ0 x = N) (h : ∀ x, le_k (κ0 x) (κ x)) :
    (∀ j s t, (perceived A δ κ0).mv j s t → (perceived A δ κ).mv j s t) ∧
    (∀ j s t, (perceived A δ κ0).cred j s t → (perceived A δ κ).cred j s t) := by
  constructor
  · rintro j s t ⟨a, ho, hs, ht, hd⟩
    exact ⟨a, ho, hs, ht, bluff_add δ hδ κ0 κ hdef h _ hd⟩
  · rintro j s t ⟨a, ho, hs, ht, hd, hi⟩
    refine ⟨a, ho, hs, ht, bluff_add δ hδ κ0 κ hdef h _ hd, ?_⟩
    -- the intention component is a one-element conjunction
    have := bluff_add δ hδ κ0 κ hdef h [A.intent a] (by rw [conjList_single]; exact hi)
    rw [conjList_single] at this
    exact this

theorem denial_model {Dm St : Type} (A : ArcSys Dm St C) (δ : Val4 → Bool)
    (hδ : δ = delta_cont ∨ δ = delta_cons)
    (κ0 κ : C → Val4) (hdef : ∀ x, κ0 x = Y ∨ κ0 x = N) (h : ∀ x, le_k (κ0 x) (κ x)) :
    (∀ j s t, (perceived A δ κ).mv j s t → (perceived A δ κ0).mv j s t) ∧
    (∀ j s t, (perceived A δ κ).cred j s t → (perceived A δ κ0).cred j s t) := by
  constructor
  · rintro j s t ⟨a, ho, hs, ht, hd⟩
    exact ⟨a, ho, hs, ht, denial_remove δ hδ κ0 κ hdef h _ hd⟩
  · rintro j s t ⟨a, ho, hs, ht, hd, hi⟩
    refine ⟨a, ho, hs, ht, denial_remove δ hδ κ0 κ hdef h _ hd, ?_⟩
    have := denial_remove δ hδ κ0 κ hdef h [A.intent a] (by rw [conjList_single]; exact hi)
    rw [conjList_single] at this
    exact this

end Definite

end RobustGMCR

/-! ## The converse fails: unrestricted stability does not imply legal stability -/

namespace LegalCounterexample

open RobustGMCR

/-- Four states. DM `false` (the focal DM) can move `s → t`; DM `true` can move
`t → u` and `u → v`, but not `t → v` directly. -/
inductive St
  | s | t | u | v
  deriving DecidableEq

def mv : Bool → St → St → Prop
  | false, .s, .t => True
  | true,  .t, .u => True
  | true,  .u, .v => True
  | _,     _,  _  => False

def P : PModel Bool St := ⟨mv, mv⟩

/-- Strict preference of the focal DM: `t` and `u` are better than `s`, `v` is not. -/
def pref : Bool → St → St → Prop
  | false, .t, .s => True
  | false, .u, .s => True
  | _,     _,  _  => False

theorem bool_contra {a b : Bool} (ha : a ≠ false) (hb : b ≠ false) (hab : a ≠ b) : False := by
  cases a <;> cases b <;> simp_all

/-- From `t`, the only state reachable by a legal sequence of the opponent is `u`:
the opponent cannot move twice in succession. -/
theorem legal_from_t {k : Bool} {x : St} (h : LReach mv false .t k x) : x = .u := by
  cases h with
  | single hk hm =>
      cases k
      · exact absurd rfl hk
      · cases x <;> simp_all [mv]
  | cons hj hjk hprev _ =>
      exact (bool_contra hj hprev.last_ne hjk).elim

/-- `s` is GMR-stable for the focal DM with unrestricted reachability
(the opponent can continue from `u` to `v`). -/
theorem unrestricted_gmr : StableU pref P .gmr false .s := by
  intro x hm _
  cases x <;> simp [P, mv] at hm
  have h1 : UReach P.mv false St.t St.u :=
    UReach.single (j := true) (by decide) (show mv true St.t St.u from True.intro)
  have h2 : UReach P.mv false St.t St.v :=
    UReach.tail (j := true) h1 (by decide) (show mv true St.u St.v from True.intro)
  exact ⟨St.v, h2, by simp [pref]⟩

/-- … but not with legal sequences. -/
theorem not_legal_gmr : ¬ Stable pref P .gmr false .s := by
  intro h
  obtain ⟨y, k, hr, hy⟩ := h .t True.intro True.intro
  have := legal_from_t hr
  subst this
  exact hy True.intro

end LegalCounterexample
