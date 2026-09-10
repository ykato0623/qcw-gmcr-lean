import Mathlib

set_option linter.unusedSectionVars false

universe u v

/-- グラフモデル。`N` は意思決定主体 (DM) の型、`S` は状態の型。 -/
structure GraphModel (N : Type u) (S : Type v) where
  move : N → S → S → Prop
  pref : N → S → S → Prop

namespace GraphModel

variable {N : Type u} {S : Type v} (G : GraphModel N S)

def UI (i : N) (s t : S) : Prop :=
  G.move i s t ∧ G.pref i t s

def jointMove (H : Set N) (s t : S) : Prop :=
  ∃ i ∈ H, G.move i s t

def jointUI (H : Set N) (s t : S) : Prop :=
  ∃ i ∈ H, G.UI i s t

def CMove (H : Set N) : S → S → Prop :=
  Relation.TransGen (G.jointMove H)

def CUI (H : Set N) : S → S → Prop :=
  Relation.TransGen (G.jointUI H)

def opp (i : N) : Set N := {j | j ≠ i}

def NashStable (i : N) (s : S) : Prop :=
  ∀ t, ¬ G.UI i s t

def GMRStable (i : N) (s : S) : Prop :=
  ∀ t, G.UI i s t → ∃ u, G.CMove (opp i) t u ∧ ¬ G.pref i u s

def SMRStable (i : N) (s : S) : Prop :=
  ∀ t, G.UI i s t →
    ∃ u, G.CMove (opp i) t u ∧ ¬ G.pref i u s ∧
      ∀ v, G.move i u v → ¬ G.pref i v s

def SEQStable (i : N) (s : S) : Prop :=
  ∀ t, G.UI i s t → ∃ u, G.CUI (opp i) t u ∧ ¬ G.pref i u s

def IsEquilibrium (stable : N → S → Prop) (s : S) : Prop :=
  ∀ i, stable i s

theorem cui_imp_cmove {H : Set N} {s t : S} (h : G.CUI H s t) :
    G.CMove H s t := by
  have h' : Relation.TransGen (G.jointUI H) s t := h
  clear h
  induction h' with
  | single hab =>
      obtain ⟨i, hi, hui⟩ := hab
      exact Relation.TransGen.single ⟨i, hi, hui.1⟩
  | tail _ hab ih =>
      obtain ⟨i, hi, hui⟩ := hab
      exact Relation.TransGen.tail ih ⟨i, hi, hui.1⟩

theorem NashStable.gmrStable {i : N} {s : S}
    (h : G.NashStable i s) : G.GMRStable i s :=
  fun t ht => absurd ht (h t)

theorem NashStable.smrStable {i : N} {s : S}
    (h : G.NashStable i s) : G.SMRStable i s :=
  fun t ht => absurd ht (h t)

theorem NashStable.seqStable {i : N} {s : S}
    (h : G.NashStable i s) : G.SEQStable i s :=
  fun t ht => absurd ht (h t)

theorem SMRStable.gmrStable {i : N} {s : S}
    (h : G.SMRStable i s) : G.GMRStable i s := by
  intro t ht
  obtain ⟨u, hreach, hsanc, -⟩ := h t ht
  exact ⟨u, hreach, hsanc⟩

theorem SEQStable.gmrStable {i : N} {s : S}
    (h : G.SEQStable i s) : G.GMRStable i s := by
  intro t ht
  obtain ⟨u, hreach, hsanc⟩ := h t ht
  exact ⟨u, G.cui_imp_cmove hreach, hsanc⟩

theorem nash_equilibrium_imp_gmr_equilibrium {s : S}
    (h : IsEquilibrium G.NashStable s) : IsEquilibrium G.GMRStable s :=
  fun i => (h i).gmrStable

inductive LMove (H : Set N) : S → N → S → Prop
  | single {i : N} {s t : S} (hi : i ∈ H) (h : G.move i s t) : LMove H s i t
  | cons {i j : N} {s t u : S} (hj : j ∈ H) (hne : j ≠ i)
      (h : LMove H s i t) (h' : G.move j t u) : LMove H s j u

def CMoveLegal (H : Set N) (s t : S) : Prop := ∃ i, G.LMove H s i t

theorem lmove_imp_cmove {H : Set N} {i : N} {s t : S}
    (h : G.LMove H s i t) : G.CMove H s t := by
  induction h with
  | single hi hm => exact Relation.TransGen.single ⟨_, hi, hm⟩
  | cons hj _ _ h' ih => exact Relation.TransGen.tail ih ⟨_, hj, h'⟩

/-! ## 提携安定性 (Coalition Stability) — Inohara–Hipel 型の4概念と包含定理 -/

variable (indiff : N → S → S → Prop) -- 無差別: s ∼_i t

-- 弱順序の公理群(現時点の定理では未使用; 必要になった定理で明示的に仮定する)
variable (pref_refl : ∀ i s, indiff i s s)
variable (pref_symm : ∀ i s t, indiff i s t → indiff i t s)
variable (pref_trans : ∀ i s t u, (G.pref i s t ∨ indiff i s t) →
  (G.pref i t u ∨ indiff i t u) → (G.pref i s u ∨ indiff i s u))
variable (pref_complete : ∀ i s t, G.pref i s t ∨ G.pref i t s ∨ indiff i s t)
variable (pref_asymm : ∀ i s t, G.pref i s t → ¬ G.pref i t s ∧ ¬ indiff i s t)

/-- 提携 H の到達可能性 R_H(s)(`CMove` の集合表示)。 -/
def R_H (H : Set N) (s : S) : Set S :=
  { t | G.CMove H s t }

/-- 提携改善到達可能性 R_H⁺⁺(s):H の移動列で到達し、H の全員が s より厳密に改善。 -/
def R_H_double_plus (H : Set N) (s : S) : Set S :=
  { t | t ∈ G.R_H H s ∧ ∀ i ∈ H, G.pref i t s }

/-- φ_H^u(s):少なくとも1人のメンバー i について s ≽_i x となる状態(制裁先)。 -/
def phi_H_u (H : Set N) (s : S) : Set S :=
  { x | ∃ i ∈ H, G.pref i s x ∨ indiff i s x }

/-- 対抗者のクラス P(N∖H):H と交わらない非空提携の全体。 -/
def P_N_minus_H (H : Set N) : Set (Set N) :=
  { K | K.Nonempty ∧ Disjoint K H }

/-- クラス C による1ステップ移動:C のいずれかの提携のメンバーが動く。 -/
def ClassStepMove (C : Set (Set N)) (s t : S) : Prop :=
  ∃ K ∈ C, G.jointMove K s t

/-- クラス到達可能性 R_C。 -/
def R_C (C : Set (Set N)) (s : S) : Set S :=
  { t | Relation.TransGen (G.ClassStepMove C) s t }

/-- クラス C による1ステップ提携改善:C のいずれかの提携 K が提携改善を行う。 -/
def ClassStepImprove (C : Set (Set N)) (s t : S) : Prop :=
  ∃ K ∈ C, t ∈ G.R_H_double_plus K s

/-- クラス改善到達可能性 R_C⁺⁺。 -/
def R_C_double_plus (C : Set (Set N)) (s : S) : Set S :=
  { t | Relation.TransGen (G.ClassStepImprove C) s t }

/-! ### 安定性概念 -/

def CNashStableForCoalition (H : Set N) (s : S) : Prop :=
  G.R_H_double_plus H s = ∅

def CNashStableForDM (i : N) (s : S) : Prop :=
  ∀ H : Set N, i ∈ H → G.CNashStableForCoalition H s

def CNashEquilibrium (s : S) : Prop :=
  ∀ i : N, G.CNashStableForDM i s

def CGMRStableForCoalition (H : Set N) (s : S) : Prop :=
  ∀ x ∈ G.R_H_double_plus H s,
    (G.R_C (P_N_minus_H H) x ∩ G.phi_H_u indiff H s).Nonempty

def CGMRStableForDM (i : N) (s : S) : Prop :=
  ∀ H : Set N, i ∈ H → G.CGMRStableForCoalition indiff H s

def CGMREquilibrium (s : S) : Prop :=
  ∀ i : N, G.CGMRStableForDM indiff i s

def CSMRStableForCoalition (H : Set N) (s : S) : Prop :=
  ∀ x ∈ G.R_H_double_plus H s,
    ∃ y ∈ G.R_C (P_N_minus_H H) x ∩ G.phi_H_u indiff H s,
      ∀ z ∈ G.R_H H y, z ∈ G.phi_H_u indiff H s

def CSMRStableForDM (i : N) (s : S) : Prop :=
  ∀ H : Set N, i ∈ H → G.CSMRStableForCoalition indiff H s

def CSMREquilibrium (s : S) : Prop :=
  ∀ i : N, G.CSMRStableForDM indiff i s

def CSEQStableForCoalition (H : Set N) (s : S) : Prop :=
  ∀ x ∈ G.R_H_double_plus H s,
    (G.R_C_double_plus (P_N_minus_H H) x ∩ G.phi_H_u indiff H s).Nonempty

def CSEQStableForDM (i : N) (s : S) : Prop :=
  ∀ H : Set N, i ∈ H → G.CSEQStableForCoalition indiff H s

def CSEQEquilibrium (s : S) : Prop :=
  ∀ i : N, G.CSEQStableForDM indiff i s

/-! ### 補助補題 -/

/-- 推移閉包の連結(mathlib の `Relation.TransGen.trans` 相当; 自己完結版)。 -/
theorem transGen_trans' {α : Sort _} {r : α → α → Prop} {a b c : α}
    (h1 : Relation.TransGen r a b) (h2 : Relation.TransGen r b c) :
    Relation.TransGen r a c := by
  induction h2 with
  | single h => exact Relation.TransGen.tail h1 h
  | tail _ h ih => exact Relation.TransGen.tail ih h

/-- クラス C に属する単一提携 K の到達可能性はクラス到達可能性に埋め込まれる。 -/
theorem coalition_reach_mono {C : Set (Set N)} {K : Set N} (hK : K ∈ C)
    {s t : S} (h : Relation.TransGen (G.jointMove K) s t) :
    Relation.TransGen (G.ClassStepMove C) s t := by
  induction h with
  | single hst => exact Relation.TransGen.single ⟨K, hK, hst⟩
  | tail _ hst ih => exact Relation.TransGen.tail ih ⟨K, hK, hst⟩

/-- クラス改善到達可能性はクラス到達可能性に含まれる:R_C⁺⁺ ⊆ R_C。 -/
theorem R_C_dpp_subset_R_C {C : Set (Set N)} {s : S} :
    G.R_C_double_plus C s ⊆ G.R_C C s := by
  intro t ht
  have h1 : Relation.TransGen (G.ClassStepImprove C) s t := ht
  clear ht
  show Relation.TransGen (G.ClassStepMove C) s t
  induction h1 with
  | single hstep =>
      obtain ⟨K, hK, hmem⟩ := hstep
      exact G.coalition_reach_mono hK hmem.1
  | tail _ hstep ih =>
      obtain ⟨K, hK, hmem⟩ := hstep
      exact transGen_trans' ih (G.coalition_reach_mono hK hmem.1)

/-! ### 包含定理 -/

/-- CNash 安定 ⇒ CSMR 安定(改善移動が存在しないため空虚に真)。 -/
theorem cnash_implies_csmr (s : S) (h : G.CNashEquilibrium s) :
    G.CSMREquilibrium indiff s := by
  intro i H hiH x hx
  have hempty : G.R_H_double_plus H s = ∅ := h i H hiH
  have h_in_empty : x ∈ ∅ := hempty ▸ hx
  exact False.elim h_in_empty



/-- CSMR 安定 ⇒ CGMR 安定(制裁先 y の存在の取り出し)。 -/
theorem csmr_implies_cgmr (s : S) (h : G.CSMREquilibrium indiff s) :
    G.CGMREquilibrium indiff s := by
  intro i H hiH x hx
  obtain ⟨y, hy, -⟩ := h i H hiH x hx
  exact ⟨y, hy⟩

/-- CSEQ 安定 ⇒ CGMR 安定(信憑性のある制裁は通常の制裁でもある)。 -/
theorem cseq_implies_cgmr (s : S) (h : G.CSEQEquilibrium indiff s) :
    G.CGMREquilibrium indiff s := by
  intro i H hiH x hx
  obtain ⟨y, hy⟩ := h i H hiH x hx
  exact ⟨y, ⟨G.R_C_dpp_subset_R_C hy.1, hy.2⟩⟩

/-- CNash 安定 ⇒ CGMR 安定(定理の合成)。 -/
theorem cnash_implies_cgmr (s : S) (h : G.CNashEquilibrium s) :
    G.CGMREquilibrium indiff s :=
  G.csmr_implies_cgmr indiff s (G.cnash_implies_csmr indiff s h)

/-- CNash 安定 ⇒ CSEQ 安定(空虚に真)。 -/
theorem cnash_implies_cseq (s : S) (h : G.CNashEquilibrium s) :
    G.CSEQEquilibrium indiff s := by
  intro i H hiH x hx
  have hempty : G.R_H_double_plus H s = ∅ := h i H hiH
  rw [hempty] at hx
  contradiction


end GraphModel


/-! ## QCW-GMCR & Belnap's Four-Valued Logic -/

inductive Val4
  | N   -- Definite False
  | U   -- Unknown
  | YN  -- Both
  | Y   -- Definite True
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

theorem conj_comm (ϕ ψ : Val4) : conj ϕ ψ = conj ψ ϕ := by
  cases ϕ <;> cases ψ <;> rfl

theorem conj_assoc (ϕ ψ χ : Val4) : conj (conj ϕ ψ) χ = conj ϕ (conj ψ χ) := by
  cases ϕ <;> cases ψ <;> cases χ <;> rfl

theorem conj_N_left (ϕ : Val4) : conj N ϕ = N := by
  cases ϕ <;> rfl

theorem conj_Y_left (ϕ : Val4) : conj Y ϕ = ϕ := by
  cases ϕ <;> rfl

theorem conj_N_right (ϕ : Val4) : conj ϕ N = N := by
  cases ϕ <;> rfl

theorem conj_idem (ϕ : Val4) : conj ϕ ϕ = ϕ := by
  cases ϕ <;> rfl

def le_k : Val4 → Val4 → Prop
  | U,  _   => True
  | _,  YN  => True
  | N,  N   => True
  | Y,  Y   => True
  | _,  _   => False

infix:50 " ≤k " => le_k

def entail : Val4 → Val4 → Val4
  | Y,  Y  => Y
  | Y,  N  => N
  | Y,  YN => YN
  | Y,  U  => U
  | N,  _  => Y
  | YN, Y  => YN
  | YN, N  => N
  | YN, YN => YN
  | YN, U  => U
  | U,  Y  => Y
  | U,  N  => U
  | U,  YN => YN
  | U,  U  => U

end Val4

open Val4

instance : Std.Commutative Val4.conj := ⟨conj_comm⟩
instance : Std.Associative Val4.conj := ⟨conj_assoc⟩

variable {O : Type} [DecidableEq O] [Fintype O]

def QcwState (O : Type) : Type := O → Val4

def conjComposition (s : QcwState O) : Val4 :=
  Finset.univ.fold Val4.conj Val4.Y s

namespace QcwState

/-- 補助:o ∈ t かつ s o = N なら、t 上の畳み込みは N(N の吸収性)。 -/
theorem fold_conj_eq_N {s : QcwState O} {o : O} (h : s o = N) :
    ∀ {t : Finset O}, o ∈ t → t.fold Val4.conj Val4.Y s = N := by
  intro t
  induction t using Finset.induction_on with
  |empty => intro ho; contradiction

  | insert a t' ha ih =>
    intro ho
    erw [Finset.fold_insert ha]
    rcases Finset.mem_insert.mp ho with rfl | ho'
    · rw [h, conj_N_left]
    · rw [ih ho', conj_N_right]

theorem propagation_property_i (s : QcwState O) (o : O) (h_infeasible : s o = N) :
    conjComposition s = N :=
  fold_conj_eq_N h_infeasible (Finset.mem_univ o)

/-- 補助:全オプションが Y なら畳み込みは Y(Y の単位性)。 -/
theorem fold_conj_eq_Y {s : QcwState O} (h_all_Y : ∀ o, s o = Y) (t : Finset O) :
    t.fold Val4.conj Val4.Y s = Val4.Y := by
  induction t using Finset.induction_on with
  | empty => exact Finset.fold_empty
  | @insert a t' ha ih => erw [Finset.fold_insert ha, h_all_Y a, conj_Y_left, ih]

theorem propagation_property_iv (s : QcwState O) (h_all_Y : ∀ o, s o = Y) :
    conjComposition s = Y :=
  fold_conj_eq_Y h_all_Y Finset.univ

end QcwState

namespace Val4

def delta_cons (v : Val4) : Bool :=
  match v with
  | Y => true
  | _ => false

def delta_prec (v : Val4) : Bool :=
  match v with
  | Y  => true
  | YN => true
  | _  => false

def delta_opt (v : Val4) : Bool :=
  match v with
  | N => false
  | _ => true

def delta_cont (v : Val4) : Bool :=
  match v with
  | Y => true
  | U => true
  | _ => false

theorem cons_satisfies_axiom_54 : delta_cons N = false := by rfl
theorem prec_satisfies_axiom_54 : delta_prec N = false := by rfl
theorem opt_satisfies_axiom_54 : delta_opt N = false := by rfl
theorem cont_satisfies_axiom_54 : delta_cont N = false := by rfl


/-! ### 還元演算子の単調性

形式化の過程で、当初の公理 A4(知識順序 ≤k に関する単調性)は
δ_prec を除く3つの正準演算子で「偽」であることが判明した。
反例:Y ≤k YN だが δ_cons Y = true, δ_cons YN = false(δ_cont も同様)、
U ≤k N だが δ_opt U = true, δ_opt N = false。
概念的には、知識順序を上がることは「矛盾証拠の獲得」を含むため、
矛盾への警戒 (A2) を持つ演算子がその際に状態を除外するのはむしろ正しい挙動であり、
知識単調性はそもそも要請すべき公理ではなかった。
正しい公理は真理順序 ≤t に関する単調性であり、これは4演算子すべてが満たす。
以下:(1) 全演算子の真理単調性、(2) δ_prec のみが満たす知識単調性、
(3) 残る3演算子に対する知識単調性の機械検証済み反例。 -/

/-- 真理順序 ≤t:N <t U <t Y, N <t YN <t Y(U と YN は比較不能)。 -/
def le_t : Val4 → Val4 → Prop
  | N,  _  => True
  | _,  Y  => True
  | U,  U  => True
  | YN, YN => True
  | _,  _  => False

infix:50 " ≤t " => le_t

-- (1) 真理単調性(修正版 A4):4演算子すべてが満たす
theorem cons_truth_monotone (v1 v2 : Val4)
    (h_le : v1 ≤t v2) (h_v1 : delta_cons v1 = true) : delta_cons v2 = true := by
  cases v1 <;> cases v2 <;>
    first | rfl | exact False.elim h_le | exact Bool.noConfusion h_v1

theorem prec_truth_monotone (v1 v2 : Val4)
    (h_le : v1 ≤t v2) (h_v1 : delta_prec v1 = true) : delta_prec v2 = true := by
  cases v1 <;> cases v2 <;>
    first | rfl | exact False.elim h_le | exact Bool.noConfusion h_v1

theorem opt_truth_monotone (v1 v2 : Val4)
    (h_le : v1 ≤t v2) (h_v1 : delta_opt v1 = true) : delta_opt v2 = true := by
  cases v1 <;> cases v2 <;>
    first | rfl | exact False.elim h_le | exact Bool.noConfusion h_v1

theorem cont_truth_monotone (v1 v2 : Val4)
    (h_le : v1 ≤t v2) (h_v1 : delta_cont v1 = true) : delta_cont v2 = true := by
  cases v1 <;> cases v2 <;>
    first | rfl | exact False.elim h_le | exact Bool.noConfusion h_v1

-- (2) 知識単調性は δ_prec のみが満たす
theorem prec_satisfies_knowledge_monotonicity (v1 v2 : Val4)
    (h_le : v1 ≤k v2) (h_v1 : delta_prec v1 = true) : delta_prec v2 = true := by
  cases v1 <;> cases v2 <;>
    first | rfl | exact False.elim h_le | exact Bool.noConfusion h_v1

-- (3) 知識単調性の反例(機械検証済みの反証)
theorem cons_not_knowledge_monotone :
    ¬ (∀ v1 v2 : Val4, v1 ≤k v2 → delta_cons v1 = true → delta_cons v2 = true) :=
  fun h => Bool.noConfusion (h Y YN True.intro rfl)

theorem opt_not_knowledge_monotone :
    ¬ (∀ v1 v2 : Val4, v1 ≤k v2 → delta_opt v1 = true → delta_opt v2 = true) :=
  fun h => Bool.noConfusion (h U N True.intro rfl)

theorem cont_not_knowledge_monotone :
    ¬ (∀ v1 v2 : Val4, v1 ≤k v2 → delta_cont v1 = true → delta_cont v2 = true) :=
  fun h => Bool.noConfusion (h Y YN True.intro rfl)

def isDefiniteReach (v_pre v_post : Val4) : Bool :=
  match entail v_pre v_post with
  | Y => true
  | _ => false

def isCredibleReach (v_pre v_post : Val4) : Bool :=
  match entail v_pre v_post with
  | Y  => true
  | YN => true
  | _  => false

def isPossibleReach (v_pre v_post : Val4) : Bool :=
  match entail v_pre v_post with
  | N => false
  | _ => true

theorem definite_imp_credible (v_pre v_post : Val4)
    (h : isDefiniteReach v_pre v_post = true) : isCredibleReach v_pre v_post = true := by
  cases v_pre <;> cases v_post <;> first | rfl | exact Bool.noConfusion h

theorem credible_imp_possible (v_pre v_post : Val4)
    (h : isCredibleReach v_pre v_post = true) : isPossibleReach v_pre v_post = true := by
  cases v_pre <;> cases v_post <;> first | rfl | exact Bool.noConfusion h




end Val4

variable {S : Type} [DecidableEq S] [Fintype S]

def qcwStateSpace (S_reduced : Finset S) (F : Finset S) (B : Finset S) : Finset S :=
  S_reduced \ (F ∪ B)

/-! ## Section 8: 4値ハイパーゲーム -/

variable {N : Type} [DecidableEq N] [Fintype N]

structure QcwHypergame (N : Type) (O : Type) where
  psi : N → N → O → Val4
  pref : N → (O → Val4) → (O → Val4) → Prop

namespace QcwHypergame

def is_in_shared_safe_core (H : QcwHypergame N O) (s : O → Val4)
    (subjective_spaces : N → Finset (O → Val4)) : Prop :=
  ∀ i : N, s ∈ subjective_spaces i

end QcwHypergame
