# Theorem and Exercise Index for JechExercises

This document catalogs all formal definitions, lemmas, theorems, and solved exercises in `/botworkspace/JechExercises`, formalizing selected exercises and foundational lemmas from Thomas Jech's *Set Theory* (3rd Millennium Edition) in Isabelle/ZF and Isabelle/FOL.

## 1. Summary of Theory Files

| File | Logic / Base | Scope and Mathematical Contents | Formal Items |
| :--- | :--- | :--- | :--- |
| [JechExercises.thy](file:///botworkspace/JechExercises/JechExercises.thy) | Isabelle/ZF (`imports trivia filters`) | Inductive sets, Jech Chapter 1 Exercises 1.1 through 1.7 (ordered pairs, Cartesian products, Cantor-Russell diagonal `ex_1_2`, non-existence of universal set, inductive subsets `ex1_3`, transitive elements `ex1_4`, Foundation consequences `no_self_membership` and `no_two_cycle`, transitive set characterizations `Transset_iff_Union` and `Transset_iff_Pow`, natural number class `Nat` and set `Omega`, image of union `image_Union`), and Chapter 2 ordinal properties | 46 |
| [filters.thy](file:///botworkspace/JechExercises/filters.thy) | Isabelle/ZF (`imports ZF`) | Jech Chapter 7: Boolean algebra of $\mathcal{P}(S)$, filters (`is_filter`), ultrafilters (`is_ultrafilter`), ideals (`is_ideal`), principal filters (`principal_filter_is_filter`), and singleton principal ultrafilters (`singleton_principal_is_ultrafilter`) | 23 |
| [classical_axioms.thy](file:///botworkspace/JechExercises/classical_axioms.thy) | Isabelle/FOL (`imports FOL`) | Classical Hilbert-style propositional and first-order axiom schemas (`ax1` through `ax13`) and Bernays quantifier rules (`B1`, `axB1`, `B2`, `axB2`, `rB1`, `rB2`) | 19 |
| [trivia.thy](file:///botworkspace/JechExercises/trivia.thy) | Isabelle/ZF (`imports ZF`) | Foundational set-theoretic warm-up lemmas: extensional membership substitution (`In_sound_right`), binary union elimination (`UnE`), successor elimination (`SuccE`), and $A = \bigcup \mathcal{P}(A)$ (`AeqUPA`) | 4 |
| [notes/completed_exercise_solutions.md](file:///botworkspace/JechExercises/notes/completed_exercise_solutions.md) | Isabelle/ZF & Mathematical Notes | Rigorous completions for Exercise 1.3 Part 2 ($\Omega$ transitivity and $n = \{m \in \Omega : m < n\}$), Exercise 1.6 ordinal synthesis ($\Omega \subseteq \mathrm{Ord}$), and Chapter 7 Filter-Ideal Duality and Ultrafilter Equivalences | 12 |

---

## 2. Detailed Catalog by Theory

### 2.1 Core Set-Theoretic Exercises ([JechExercises.thy](file:///botworkspace/JechExercises/JechExercises.thy))

| Kind | Identifier | Line | Jech Reference / Formal Statement | Status |
| :--- | :--- | :--- | :--- | :--- |
| Definition | `Ind` | [L10](file:///botworkspace/JechExercises/JechExercises.thy#L10-L11) | `Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)` | Verified |
| Lemma | `IndInf` | [L13](file:///botworkspace/JechExercises/JechExercises.thy#L13-L14) | `Ind(Inf)` | Verified (`by`) |
| Lemma | `IndI` | [L16](file:///botworkspace/JechExercises/JechExercises.thy#L16-L31) | `[| 0 \<in> x; !!xa. xa \<in> x ==> succ(xa) \<in> x |] ==> Ind(x)` | Verified (`qed`) |
| Lemma | `IndE1` | [L33](file:///botworkspace/JechExercises/JechExercises.thy#L33-L40) | `Ind(x) ==> 0 \<in> x` | Verified (`qed`) |
| Lemma | `IndE2` | [L42](file:///botworkspace/JechExercises/JechExercises.thy#L42-L50) | `Ind(x) ==> \<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x` | Verified (`qed`) |
| Lemma | `IndE2R` | [L52](file:///botworkspace/JechExercises/JechExercises.thy#L52-L58) | `[| Ind(x); xa \<in> x |] ==> succ(xa) \<in> x` | Verified (`qed`) |
| Theorem | `ex_1_1` | [L62](file:///botworkspace/JechExercises/JechExercises.thy#L62-L63) | **Ex 1.1**: `<a,b> = <c,d> \<longleftrightarrow> a=c & b=d` | Verified (`by`) |
| Lemma | `Pair_fst`, `Pair_snd` | [L65](file:///botworkspace/JechExercises/JechExercises.thy#L65-L69) | `fst(<a,b>) = a` and `snd(<a,b>) = b` | Verified (`by`) |
| Lemma | `prod_Un_distrib1`, `prod_Int_distrib1`, `prod_Diff_distrib1`, `prod_Un_distrib2`, `prod_Int_distrib2`, `prod_Diff_distrib2` | [L71](file:///botworkspace/JechExercises/JechExercises.thy#L71-L87) | Left and right distributivity of $\times$ over $\cup, \cap, \setminus$ | Verified (`by blast`) |
| Lemma | `notWinW` | [L95](file:///botworkspace/JechExercises/JechExercises.thy#L95-L103) | For $W = \{x \in S.\, x \notin x\}$, `W \<in> W ==> False` | Verified (`qed`) |
| Theorem | `ex_1_2` | [L105](file:///botworkspace/JechExercises/JechExercises.thy#L105-L124) | **Ex 1.2**: `\<not> (Pow(S) \<subseteq> S)` | Verified (`qed`) |
| Theorem | `no_universal_set` | [L127](file:///botworkspace/JechExercises/JechExercises.thy#L127-L137) | **Ex 1.2 Cor**: `\<not> (\<exists>V. \<forall>x. x \<in> V)` | Verified (`qed`) |
| Lemma | `subsetsu` | [L145](file:///botworkspace/JechExercises/JechExercises.thy#L145-L170) | Inductive step for $\{y \in x.\, y \subseteq x\}$ | Verified (`qed`) |
| Theorem | `ex1_3` | [L172](file:///botworkspace/JechExercises/JechExercises.thy#L172-L180) | **Ex 1.3**: `Ind(x) ==> Ind({y \<in> x. y \<subseteq> x})` (Part 2 completed in [completed_exercise_solutions.md](file:///botworkspace/JechExercises/notes/completed_exercise_solutions.md)) | Verified (`qed`) |
| Lemma | `trans_empty` | [L186](file:///botworkspace/JechExercises/JechExercises.thy#L186-L187) | `Transset(0)` | Verified (`by auto`) |
| Lemma | `trans_succ` | [L189](file:///botworkspace/JechExercises/JechExercises.thy#L189-L206) | `Transset(y) ==> Transset(succ(y))` | Verified (`qed`) |
| Theorem | `ex1_4` | [L208](file:///botworkspace/JechExercises/JechExercises.thy#L208-L226) | **Ex 1.4**: `Ind(x) ==> Ind({y \<in> x. Transset(y)})` | Verified (`qed`) |
| Lemma | `no_self_membership` | [L230](file:///botworkspace/JechExercises/JechExercises.thy#L230-L240) | **Ex 1.5(a)**: `x \<notin> x` (from Axiom of Foundation) | Verified (`qed`) |
| Lemma | `no_two_cycle` | [L242](file:///botworkspace/JechExercises/JechExercises.thy#L242-L262) | **Ex 1.5(b)**: `\<not> (x \<in> y \<and> y \<in> x)` (from Axiom of Foundation) | Verified (`qed`) |
| Lemma | `Transset_iff_Union` | [L266](file:///botworkspace/JechExercises/JechExercises.thy#L266-L288) | **Ex 1.6(a)**: `Transset(x) \<longleftrightarrow> \<Union>x \<subseteq> x` | Verified (`qed`) |
| Lemma | `Transset_iff_Pow` | [L290](file:///botworkspace/JechExercises/JechExercises.thy#L290-L307) | **Ex 1.6(b)**: `Transset(x) \<longleftrightarrow> x \<subseteq> Pow(x)` | Verified (`qed`) |
| Lemma | `Transset_Pow` | [L309](file:///botworkspace/JechExercises/JechExercises.thy#L309-L322) | **Ex 1.6(c)**: `Transset(x) ==> Transset(Pow(x))` | Verified (`qed`) |
| Lemma | `Transset_Union` | [L324](file:///botworkspace/JechExercises/JechExercises.thy#L324-L334) | **Ex 1.6(d)**: `(\<forall>y\<in>A. Transset(y)) ==> Transset(\<Union>A)` | Verified (`qed`) |
| Definition | `ClassInter`, `Nat`, `IsTransClass`, `IsIndClass`, `Omega` | [L336](file:///botworkspace/JechExercises/JechExercises.thy#L336-L411) | Class intersection of all inductive sets `Nat` and the set `Omega == {y \<in> Inf. Nat(y)}` | Verified |
| Lemma | `NatSubInf`, `NatSubInf'`, `Nat0`, `NatSu`, `NatSucc`, `NatIsInd`, `NatSubOmega` | [L342](file:///botworkspace/JechExercises/JechExercises.thy#L342-L420) | Closure of `Nat` and `Omega` under `0` and `succ`, and inclusion in `Inf` | Verified (`qed`) |
| Lemma | `image_Union` | [L424](file:///botworkspace/JechExercises/JechExercises.thy#L424-L445) | **Ex 1.7**: `r `` (\<Union>A) = (\<Union>x\<in>A. r `` x)` | Verified (`qed`) |
| Lemma | `Ord_0`, `Ord_succ`, `Ord_in_Ord`, `Ord_trichotomy`, `Ord_Union`, `Transset_trans_Memrel`, `transfinite_induction_principle` | [L449](file:///botworkspace/JechExercises/JechExercises.thy#L449-L483) | **Chapter 2**: Ordinal closure under $0$, successor, union, $\in$-heredity, linear trichotomy, transitivity of `Memrel`, and transfinite induction | Verified (`qed` / `by`) |

### 2.2 Filters, Ultrafilters, and Ideals ([filters.thy](file:///botworkspace/JechExercises/filters.thy))

| Kind | Identifier | Line | Formal Statement / Description | Status |
| :--- | :--- | :--- | :--- | :--- |
| Lemma | `Diff_Diff_elem`, `Diff_Diff_elem2`, `Diff_Diff_eq` | [L11](file:///botworkspace/JechExercises/filters.thy#L11-L51) | Double relative complement involution `A \<subseteq> S ==> S - (S - A) = A` | Verified (`qed`) |
| Lemma | `Inter_subset_left`, `Inter_subset_right`, `Union_subset_intro`, `Inter_greatest` | [L53](file:///botworkspace/JechExercises/filters.thy#L53-L67) | Lattice bounds for binary union and intersection | Verified (`by`) |
| Definition | `is_filter`, `is_ultrafilter`, `is_ideal`, `principal_filter` | [L71](file:///botworkspace/JechExercises/filters.thy#L71-L90) | Set-theoretic definitions of filter, ultrafilter, ideal, and principal filter $\{X \in \mathcal{P}(S).\, A \subseteq X\}$ on $S$ | Verified |
| Lemma | `filter_in_Pow`, `filter_nonempty`, `filter_inter_closed`, `filter_upward_closed` | [L92](file:///botworkspace/JechExercises/filters.thy#L92-L129) | Elimination rules for filters on $S$ | Verified (`qed`) |
| Lemma | `principal_filter_subset`, `principal_filter_ground`, `principal_filter_no_zero`, `principal_filter_inter`, `principal_filter_upward` | [L133](file:///botworkspace/JechExercises/filters.thy#L133-L179) | Structural closure properties of `principal_filter(A, S)` | Verified (`qed`) |
| Theorem | `principal_filter_is_filter` | [L181](file:///botworkspace/JechExercises/filters.thy#L181-L196) | `[| A \<subseteq> S; A \<noteq> 0 |] ==> is_filter(principal_filter(A, S), S)` | Verified (`qed`) |
| Theorem | `singleton_principal_is_ultrafilter` | [L200](file:///botworkspace/JechExercises/filters.thy#L200-L231) | `a \<in> S ==> is_ultrafilter(principal_filter({a}, S), S)` | Verified (`qed`) |

### 2.3 Classical First-Order Axiom Schemas ([classical_axioms.thy](file:///botworkspace/JechExercises/classical_axioms.thy))

| Kind | Identifier | Line | Formal Statement | Status |
| :--- | :--- | :--- | :--- | :--- |
| Lemma | `ax1` | [L4](file:///botworkspace/JechExercises/classical_axioms.thy#L4-L8) | `A \<longrightarrow> (B \<longrightarrow> A)` | Verified (`done`) |
| Lemma | `ax2` | [L10](file:///botworkspace/JechExercises/classical_axioms.thy#L10-L21) | `(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> ((A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C))` | Verified (`done`) |
| Lemma | `ax3`, `ax4`, `ax5` | [L23](file:///botworkspace/JechExercises/classical_axioms.thy#L23-L43) | Conjunction elimination and introduction axioms | Verified (`done`) |
| Lemma | `ax6`, `ax7`, `ax8` | [L45](file:///botworkspace/JechExercises/classical_axioms.thy#L45-L74) | Disjunction introduction and case-elimination axioms | Verified (`done` / `qed`) |
| Lemma | `ax9`, `ax10`, `ax11` | [L76](file:///botworkspace/JechExercises/classical_axioms.thy#L76-L102) | Negation introduction, explosion (`A \<longrightarrow> ~A \<longrightarrow> B`), and Excluded Middle (`A \<or> ~A`) | Verified (`done`) |
| Lemma | `ax12`, `ax13` | [L104](file:///botworkspace/JechExercises/classical_axioms.thy#L104-L118) | Universal instantiation `(\<forall>x. A(x)) \<longrightarrow> A(q)` and existential introduction `A(q) \<longrightarrow> (\<exists>x. A(x))` | Verified (`qed` / `done`) |
| Lemma | `B1`, `axB1`, `B2`, `axB2`, `rB1`, `rB2` | [L120](file:///botworkspace/JechExercises/classical_axioms.thy#L120-L170) | Bernays quantifier shifting rules for $\forall$ and $\exists$ | Verified (`done`) |

### 2.4 Foundational Warm-Up Lemmas ([trivia.thy](file:///botworkspace/JechExercises/trivia.thy))

| Kind | Identifier | Line | Formal Statement | Status |
| :--- | :--- | :--- | :--- | :--- |
| Lemma | `In_sound_right` | [L4](file:///botworkspace/JechExercises/trivia.thy#L4-L7) | `[| x \<in> A; A = B |] ==> x \<in> B` | Verified (`done`) |
| Lemma | `UnE` | [L9](file:///botworkspace/JechExercises/trivia.thy#L9-L22) | `x \<in> (a \<union> b) ==> x \<in> a \<or> x \<in> b` | Verified (`qed`) |
| Lemma | `SuccE` | [L24](file:///botworkspace/JechExercises/trivia.thy#L24-L40) | `xa \<in> succ(k) ==> xa = k \<or> xa \<in> k` | Verified (`qed`) |
| Lemma | `AeqUPA` | [L42](file:///botworkspace/JechExercises/trivia.thy#L42-L66) | `A = \<Union>Pow(A)` | Verified (`qed`) |
