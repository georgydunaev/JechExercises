# Completed Exercise Solutions and Isabelle/ZF Proof Notes for JechExercises

This document completes the remaining parts of exercises stated in [JechExercises.thy](file:///botworkspace/JechExercises/JechExercises.thy) and extends the Chapter 7 filter and ultrafilter formalization in [filters.thy](file:///botworkspace/JechExercises/filters.thy).

---

## 1. Completion of Jech Exercise 1.3 (Part 2: Transitivity of $\Omega$ and $n = \{m \in \Omega : m < n\}$)

In [JechExercises.thy](file:///botworkspace/JechExercises/JechExercises.thy#L139-L180), the text states:
> `ex 1.3: If X is inductive, then the set {x \in X : x \subseteq X} is inductive. Hence N is transitive, and for each n, n = {m \in N : m < n}.`

While `ex1_3` proves `Ind(x) ==> Ind({y \<in> x. y \<subseteq> x})`, the deduction that $\Omega = \{y \in \mathrm{Inf} : \mathrm{Nat}(y)\}$ is itself inductive and transitive, and that each $n \in \Omega$ equals $\{m \in \Omega : m \in n\}$, is completed below.

### 1.1 Proof that $\Omega$ is the Least Inductive Set (`Ind(Omega)` and `Omega_least`)
- **Theorem (`Ind_Omega`)**: $\mathrm{Ind}(\Omega)$.
  *Proof*:
  1. By `IndInf`, $0 \in \mathrm{Inf}$, and by `Nat0`, $\mathrm{Nat}(0)$. Thus $0 \in \{y \in \mathrm{Inf} : \mathrm{Nat}(y)\} = \Omega$.
  2. Let $y \in \Omega$. Then $y \in \mathrm{Inf}$ and $\mathrm{Nat}(y)$. By `IndInf` and `IndE2R`, $\mathrm{succ}(y) \in \mathrm{Inf}$. By `NatSucc`, $\mathrm{Nat}(\mathrm{succ}(y))$. Hence $\mathrm{succ}(y) \in \Omega$. By `IndI`, $\mathrm{Ind}(\Omega)$.
- **Theorem (`Omega_least`)**: If $\mathrm{Ind}(X)$, then $\Omega \subseteq X$.
  *Proof*: Let $y \in \Omega$. Then $\mathrm{Nat}(y)$, meaning $\forall Z.\, \mathrm{Ind}(Z) \implies y \in Z$. Instantiating with $Z = X$ yields $y \in X$.

### 1.2 Proof that $\Omega$ is Transitive (`Transset(Omega)`) and $n = \{m \in \Omega : m \in n\}$
- **Theorem (`Transset_Omega`)**: $\mathrm{Transset}(\Omega)$.
  *Proof*: Since $\mathrm{Ind}(\Omega)$, applying `ex1_3` to $x = \Omega$ shows that $T = \{y \in \Omega : y \subseteq \Omega\}$ is inductive (`Ind(T)`). By `Omega_least`, $\Omega \subseteq T$. Thus for every $n \in \Omega$, we have $n \in T$, so $n \subseteq \Omega$. By definition of `Transset`, $\mathrm{Transset}(\Omega)$ holds.
- **Corollary (`nat_eq_less_set`)**: For every $n \in \Omega$, $n = \{m \in \Omega : m \in n\}$.
  *Proof*: Since $\mathrm{Transset}(\Omega)$ and $n \in \Omega$, we have $n \subseteq \Omega$. For any set $n \subseteq \Omega$, $n = n \cap \Omega = \{m \in \Omega : m \in n\}$. Since the natural order $<$ on von Neumann naturals is membership $\in$, we obtain $n = \{m \in \Omega : m < n\}$.

### 1.3 Isabelle/ZF Formalization of Exercise 1.3 Part 2 and Exercise 1.4 Consequence
```isabelle
lemma Ind_Omega: \<open>Ind(Omega)\<close>
proof (rule IndI)
  from IndInf have \<open>0 \<in> Inf\<close> by (rule IndE1)
  with Nat0 have \<open>0 \<in> {y \<in> Inf. Nat(y)}\<close> by (rule CollectI)
  thus \<open>0 \<in> Omega\<close> by (fold Omega_def)
next
  fix xa assume \<open>xa \<in> Omega\<close>
  hence \<open>xa \<in> {y \<in> Inf. Nat(y)}\<close> by (unfold Omega_def)
  hence h1: \<open>xa \<in> Inf\<close> and h2: \<open>Nat(xa)\<close> by (rule CollectD1, rule CollectD2)
  from IndInf and h1 have s1: \<open>succ(xa) \<in> Inf\<close> by (rule IndE2R)
  from NatSucc and h2 have s2: \<open>Nat(succ(xa))\<close> by blast
  from s1 and s2 have \<open>succ(xa) \<in> {y \<in> Inf. Nat(y)}\<close> by (rule CollectI)
  thus \<open>succ(xa) \<in> Omega\<close> by (fold Omega_def)
qed

lemma Omega_least:
  assumes \<open>Ind(X)\<close>
  shows \<open>Omega \<subseteq> X\<close>
proof (rule subsetI)
  fix x assume \<open>x \<in> Omega\<close>
  hence \<open>Nat(x)\<close> unfolding Omega_def by (rule CollectD2)
  hence \<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close> unfolding Nat_def ClassInter_def .
  with assms show \<open>x \<in> X\<close> by blast
qed

theorem Transset_Omega: \<open>Transset(Omega)\<close>
proof (unfold Transset_def, rule ballI)
  fix n assume \<open>n \<in> Omega\<close>
  from Ind_Omega have \<open>Ind({y \<in> Omega. y \<subseteq> Omega})\<close> by (rule ex1_3)
  hence \<open>Omega \<subseteq> {y \<in> Omega. y \<subseteq> Omega}\<close> by (rule Omega_least)
  with \<open>n \<in> Omega\<close> have \<open>n \<in> {y \<in> Omega. y \<subseteq> Omega}\<close> by (rule subsetD)
  thus \<open>n \<subseteq> Omega\<close> by (rule CollectD2)
qed

theorem nat_eq_initial_segment:
  assumes \<open>n \<in> Omega\<close>
  shows \<open>n = {m \<in> Omega. m \<in> n}\<close>
proof (rule equalityI)
  show \<open>n \<subseteq> {m \<in> Omega. m \<in> n}\<close>
  proof (rule subsetI)
    fix m assume \<open>m \<in> n\<close>
    from Transset_Omega and assms have \<open>n \<subseteq> Omega\<close> unfolding Transset_def by blast
    with \<open>m \<in> n\<close> have \<open>m \<in> Omega\<close> by (rule subsetD)
    with \<open>m \<in> n\<close> show \<open>m \<in> {m \<in> Omega. m \<in> n}\<close> by (rule CollectI)
  qed
next
  show \<open>{m \<in> Omega. m \<in> n} \<subseteq> n\<close> by (rule Collect_subset)
qed

theorem every_elem_of_Omega_is_Transset:
  assumes \<open>n \<in> Omega\<close>
  shows \<open>Transset(n)\<close>
proof -
  from Ind_Omega have \<open>Ind({y \<in> Omega. Transset(y)})\<close> by (rule ex1_4)
  hence \<open>Omega \<subseteq> {y \<in> Omega. Transset(y)}\<close> by (rule Omega_least)
  with assms have \<open>n \<in> {y \<in> Omega. Transset(y)}\<close> by (rule subsetD)
  thus \<open>Transset(n)\<close> by (rule CollectD2)
qed
```

---

## 2. Completion of Chapter 7 Filter-Ideal Duality and Ultrafilter Characterizations ([filters.thy](file:///botworkspace/JechExercises/filters.thy))

In [filters.thy](file:///botworkspace/JechExercises/filters.thy), `is_filter`, `is_ultrafilter`, `is_ideal`, and `principal_filter` are defined, and `principal_filter_is_filter` and `singleton_principal_is_ultrafilter` are proved. Below we complete the classical duality and ultrafilter equivalence theorems from Jech Chapter 7 (Pages 73--75).

### 2.1 Filter-Ideal Duality Theorem
For any $F \subseteq \mathcal{P}(S)$, define the dual family:
$$\mathrm{dual\_family}(F, S) = \{S \setminus X : X \in F\} = \{Y \in \mathcal{P}(S) : (S \setminus Y) \in F\}.$$

**Theorem (`filter_iff_dual_ideal`)**: $F$ is a filter on $S$ if and only if $I = \mathrm{dual\_family}(F, S)$ is an ideal on $S$.
*Proof*:
Suppose $\mathrm{is\_filter}(F, S)$:
1. $I \subseteq \mathcal{P}(S)$ by construction.
2. Since $S \in F$ and $S \setminus \emptyset = S$, we have $(S \setminus 0) = S \in F$, so $0 \in I$.
3. Since $0 \notin F$ and $S \setminus S = 0$, we have $(S \setminus S) \notin F$, so $S \notin I$.
4. For $A, B \in I$, we have $(S \setminus A) \in F$ and $(S \setminus B) \in F$. By De Morgan's law in $\mathcal{P}(S)$,
   $$S \setminus (A \cup B) = (S \setminus A) \cap (S \setminus B) \in F,$$
   since $F$ is closed under binary intersection (`filter_inter_closed`). Hence $A \cup B \in I$.
5. For $A \in I$ and $B \in \mathcal{P}(S)$ with $B \subseteq A$, contravariance of complement gives $S \setminus A \subseteq S \setminus B \subseteq S$. Since $(S \setminus A) \in F$ and $F$ is upward closed (`filter_upward_closed`), $(S \setminus B) \in F$, so $B \in I$.
By double complement involution `Diff_Diff_eq` ($S \setminus (S \setminus X) = X$ for $X \subseteq S$), the converse proof is identical.

### 2.2 Prime Property and Maximality of Ultrafilters (Jech Lemma 7.2)
**Theorem (`ultrafilter_union_prime`)**: Let $U$ be an ultrafilter on $S$, and let $A, B \subseteq S$. If $A \cup B \in U$, then $A \in U$ or $B \in U$.
*Proof*: Suppose $A \cup B \in U$ and $A \notin U$. Since $U$ is an ultrafilter on $S$ and $A \in \mathcal{P}(S)$, we have $(S \setminus A) \in U$. Because $U$ is closed under binary intersection,
$$(A \cup B) \cap (S \setminus A) \in U.$$
Observe that $(A \cup B) \cap (S \setminus A) = B \setminus A \subseteq B \subseteq S$. By upward closure of $U$ (`filter_upward_closed`), $B \in U$.

**Theorem (`ultrafilter_iff_maximal_filter`)**: A filter $U$ on $S$ is an ultrafilter if and only if for every filter $F$ on $S$ with $U \subseteq F$, we have $U = F$.
*Proof*:
- ($\implies$): Suppose $U$ is an ultrafilter, $F$ is a filter on $S$, and $U \subseteq F$. Let $A \in F$; then $A \in \mathcal{P}(S)$. If $A \notin U$, then $(S \setminus A) \in U \subseteq F$, so $A \cap (S \setminus A) = \emptyset \in F$, contradicting `filter_nonempty`. Thus $A \in U$, so $F \subseteq U$ and $U = F$.
- ($\impliedby$): Suppose $U$ is a maximal filter on $S$, and let $A \in \mathcal{P}(S)$. If $A \notin U$, then every $X \in U$ satisfies $X \cap (S \setminus A) \neq \emptyset$ (otherwise $X \subseteq A$, which by upward closure of $U$ would force $A \in U$). Then
  $$F_0 = \{Y \in \mathcal{P}(S) : \exists X \in U.\, X \cap (S \setminus A) \subseteq Y\}$$
  is a filter on $S$ extending $U$ and containing $S \setminus A$. By maximality of $U$, $F_0 = U$, so $(S \setminus A) \in U$.

### 2.3 Isabelle/ZF Proof Script for Filter-Ideal Duality and Ultrafilter Primality
```isabelle
definition dual_family :: \<open>[i, i] \<Rightarrow> i\<close> where
  \<open>dual_family(F, S) == {Y \<in> Pow(S). (S - Y) \<in> F}\<close>

lemma de_morgan_Diff_Un:
  assumes \<open>A \<subseteq> S\<close> and \<open>B \<subseteq> S\<close>
  shows \<open>S - (A \<union> B) = (S - A) \<inter> (S - B)\<close>
  by blast

theorem filter_implies_dual_ideal:
  assumes \<open>is_filter(F, S)\<close>
  shows \<open>is_ideal(dual_family(F, S), S)\<close>
proof (unfold is_ideal_def, intro conjI)
  show \<open>dual_family(F, S) \<subseteq> Pow(S)\<close>
    unfolding dual_family_def by (rule Collect_subset)
next
  from assms have \<open>S \<in> F\<close> unfolding is_filter_def by blast
  moreover have \<open>S - 0 = S\<close> by auto
  ultimately have \<open>(S - 0) \<in> F\<close> by auto
  moreover have \<open>0 \<in> Pow(S)\<close> by auto
  ultimately show \<open>0 \<in> dual_family(F, S)\<close>
    unfolding dual_family_def by (rule CollectI)
next
  show \<open>S \<notin> dual_family(F, S)\<close>
  proof (rule notI)
    assume \<open>S \<in> dual_family(F, S)\<close>
    hence \<open>(S - S) \<in> F\<close> unfolding dual_family_def by (rule CollectD2)
    hence \<open>0 \<in> F\<close> by auto
    moreover from assms have \<open>0 \<notin> F\<close> unfolding is_filter_def by blast
    ultimately show False by (rule notE)
  qed
next
  show \<open>\<forall>A\<in>dual_family(F, S). \<forall>B\<in>dual_family(F, S). A \<union> B \<in> dual_family(F, S)\<close>
  proof (intro ballI)
    fix A B assume hA: \<open>A \<in> dual_family(F, S)\<close> and hB: \<open>B \<in> dual_family(F, S)\<close>
    from hA have pA: \<open>A \<in> Pow(S)\<close> and fA: \<open>(S - A) \<in> F\<close>
      unfolding dual_family_def by (rule CollectD1, rule CollectD2)
    from hB have pB: \<open>B \<in> Pow(S)\<close> and fB: \<open>(S - B) \<in> F\<close>
      unfolding dual_family_def by (rule CollectD1, rule CollectD2)
    from assms fA fB have \<open>(S - A) \<inter> (S - B) \<in> F\<close> by (rule filter_inter_closed)
    moreover have \<open>S - (A \<union> B) = (S - A) \<inter> (S - B)\<close> by blast
    ultimately have \<open>S - (A \<union> B) \<in> F\<close> by auto
    moreover from pA pB have \<open>A \<union> B \<in> Pow(S)\<close> by auto
    ultimately show \<open>A \<union> B \<in> dual_family(F, S)\<close>
      unfolding dual_family_def by (rule CollectI)
  qed
next
  show \<open>\<forall>A\<in>dual_family(F, S). \<forall>B\<in>Pow(S). B \<subseteq> A \<longrightarrow> B \<in> dual_family(F, S)\<close>
  proof (intro ballI impI)
    fix A B assume hA: \<open>A \<in> dual_family(F, S)\<close> and pB: \<open>B \<in> Pow(S)\<close> and sub: \<open>B \<subseteq> A\<close>
    from hA have fA: \<open>(S - A) \<in> F\<close> unfolding dual_family_def by (rule CollectD2)
    have \<open>S - B \<subseteq> S\<close> and \<open>S - A \<subseteq> S - B\<close> using sub by blast+
    with assms fA have \<open>(S - B) \<in> F\<close> by (rule filter_upward_closed)
    with pB show \<open>B \<in> dual_family(F, S)\<close>
      unfolding dual_family_def by (rule CollectI)
  qed
qed

theorem ultrafilter_union_prime:
  assumes \<open>is_ultrafilter(U, S)\<close>
      and \<open>A \<in> Pow(S)\<close> and \<open>B \<in> Pow(S)\<close>
      and \<open>A \<union> B \<in> U\<close>
    shows \<open>A \<in> U \<or> B \<in> U\<close>
proof (cases \<open>A \<in> U\<close>)
  case True
  thus ?thesis by (rule disjI1)
next
  case False
  from assms(1) have filt: \<open>is_filter(U, S)\<close>
                 and ultra: \<open>\<forall>X\<in>Pow(S). X \<in> U \<or> (S - X) \<in> U\<close>
    unfolding is_ultrafilter_def by (rule conjunct1, rule conjunct2)
  from ultra assms(2) False have \<open>(S - A) \<in> U\<close> by blast
  with filt assms(4) have inter: \<open>(A \<union> B) \<inter> (S - A) \<in> U\<close>
    by (rule filter_inter_closed)
  have subB: \<open>B \<subseteq> S\<close> using assms(3) by (rule PowD)
  have sub_inter: \<open>(A \<union> B) \<inter> (S - A) \<subseteq> B\<close> by blast
  from filt inter subB sub_inter have \<open>B \<in> U\<close>
    by (rule filter_upward_closed)
  thus ?thesis by (rule disjI2)
qed
```
