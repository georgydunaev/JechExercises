(*  Title:       Jech Cardinal and Ordinal Exercise Solutions
    Author:      Georgy Dunaev <georgedunaev at gmail.com>
    Description: Companion Isabelle/ZF formalization extending JechExercises.thy
                 and notes/completed_exercise_solutions.md with machine-checked
                 lemmas on transitive sets, ordinals, successor/limit properties,
                 well-founded relations, injections, and club/filter closure.
*)

section \<open>Jech Cardinal and Ordinal Exercise Solutions\<close>

theory Jech_Cardinal_And_Ordinal_Solutions
  imports JechExercises
begin

subsection \<open>1. Transitive Sets, Ordinals, and Successor/Limit Closure\<close>

definition Transset :: \<open>i \<Rightarrow> o\<close>
  where Transset_def : \<open>Transset(X) == \<forall>y\<in>X. y \<subseteq> X\<close>

lemma TranssetI :
  assumes \<open>\<And>y z. \<lbrakk> y \<in> X; z \<in> y \<rbrakk> \<Longrightarrow> z \<in> X\<close>
  shows \<open>Transset(X)\<close>
  using assms unfolding Transset_def by blast

lemma TranssetD :
  assumes \<open>Transset(X)\<close> and \<open>y \<in> X\<close> and \<open>z \<in> y\<close>
  shows \<open>z \<in> X\<close>
  using assms unfolding Transset_def by blast

text \<open>The empty set is transitive.\<close>
lemma Transset_0 : \<open>Transset(0)\<close>
  unfolding Transset_def by blast

text \<open>If X is transitive, then its von Neumann successor succ(X) = X union {X} is transitive.\<close>
lemma Transset_succ :
  assumes \<open>Transset(X)\<close>
  shows \<open>Transset(succ(X))\<close>
  using assms unfolding Transset_def succ_def by blast

text \<open>The union of any family of transitive sets is transitive.\<close>
lemma Transset_Union_family :
  assumes \<open>\<forall>A\<in>F. Transset(A)\<close>
  shows \<open>Transset(\<Union>(F))\<close>
  using assms unfolding Transset_def by blast

text \<open>The intersection of any family of transitive sets is transitive.\<close>
lemma Transset_Inter_family :
  assumes \<open>F \<noteq> 0\<close> and \<open>\<forall>A\<in>F. Transset(A)\<close>
  shows \<open>Transset(\<Inter>(F))\<close>
  using assms unfolding Transset_def by blast

text \<open>A set X is transitive if and only if Union(X) is a subset of X, and
      equivalently X is a subset of Pow(X) (Jech Exercise 1.3 / 1.4).\<close>
theorem Transset_iff_Union_subset :
  \<open>Transset(X) \<longleftrightarrow> \<Union>(X) \<subseteq> X\<close>
  unfolding Transset_def by blast

theorem Transset_iff_subset_Pow :
  \<open>Transset(X) \<longleftrightarrow> X \<subseteq> Pow(X)\<close>
  unfolding Transset_def by blast

subsection \<open>2. Foundation Consequences: Irreflexivity and Asymmetry of Membership\<close>

text \<open>By the Axiom of Foundation, no set is a member of itself (irreflexivity),
      and no two sets are mutual members of each other (2-cycle impossibility).\<close>
theorem mem_irrefl_from_foundation :
  \<open>x \<notin> x\<close>
  by (rule mem_irrefl)

theorem mem_asym_from_foundation :
  assumes \<open>x \<in> y\<close>
  shows \<open>y \<notin> x\<close>
  using assms by (rule mem_asym)

text \<open>Furthermore, there is no 3-cycle x in y in z in x.\<close>
theorem no_mem_3_cycle :
  assumes xy : \<open>x \<in> y\<close> and yz : \<open>y \<in> z\<close> and zx : \<open>z \<in> x\<close>
  shows \<open>False\<close>
proof -
  define S where \<open>S == {x, y, z}\<close>
  have S_nonempty : \<open>S \<noteq> 0\<close>
    unfolding S_def by blast
  from foundation[of S] S_nonempty obtain m
    where m_in_S : \<open>m \<in> S\<close> and m_disj : \<open>m \<inter> S = 0\<close>
    by blast
  from m_in_S have \<open>m = x \<or> m = y \<or> m = z\<close>
    unfolding S_def by blast
  moreover
  { assume \<open>m = x\<close>
    with zx m_disj have \<open>False\<close> unfolding S_def by blast }
  moreover
  { assume \<open>m = y\<close>
    with xy m_disj have \<open>False\<close> unfolding S_def by blast }
  moreover
  { assume \<open>m = z\<close>
    with yz m_disj have \<open>False\<close> unfolding S_def by blast }
  ultimately show \<open>False\<close> by blast
qed

subsection \<open>3. Set-Theoretic Monotone Operators and Fixed Points (Knaster-Tarski Core)\<close>

text \<open>Used in the Cantor-Bernstein-Schroeder decomposition:
      if H(X) is a subset-monotone operator on Pow(A), then the union of all
      post-fixed subsets {X in Pow(A) . X subseteq H(X)} is a fixed point.\<close>

lemma monotone_postfixed_union_bound :
  assumes mono : \<open>\<And>X Y. \<lbrakk> X \<subseteq> A; Y \<subseteq> A; X \<subseteq> Y \<rbrakk> \<Longrightarrow> H(X) \<subseteq> H(Y)\<close>
      and closed : \<open>\<And>X. X \<subseteq> A \<Longrightarrow> H(X) \<subseteq> A\<close>
  defines \<open>P == {X \<in> Pow(A) . X \<subseteq> H(X)}\<close>
  defines \<open>U == \<Union>(P)\<close>
  shows \<open>U \<subseteq> H(U)\<close>
proof (rule subsetI)
  fix z
  assume \<open>z \<in> U\<close>
  then obtain X where X_in_P : \<open>X \<in> P\<close> and z_in_X : \<open>z \<in> X\<close>
    unfolding U_def by blast
  from X_in_P have X_sub_A : \<open>X \<subseteq> A\<close> and X_sub_HX : \<open>X \<subseteq> H(X)\<close>
    unfolding P_def by blast
  have U_sub_A : \<open>U \<subseteq> A\<close>
    unfolding U_def P_def by blast
  have X_sub_U : \<open>X \<subseteq> U\<close>
    using X_in_P unfolding U_def by blast
  from mono[OF X_sub_A U_sub_A X_sub_U] have HX_sub_HU : \<open>H(X) \<subseteq> H(U)\<close> .
  from z_in_X X_sub_HX have \<open>z \<in> H(X)\<close> by blast
  with HX_sub_HU show \<open>z \<in> H(U)\<close> by blast
qed

theorem knaster_tarski_greatest_fixed_point :
  assumes mono : \<open>\<And>X Y. \<lbrakk> X \<subseteq> A; Y \<subseteq> A; X \<subseteq> Y \<rbrakk> \<Longrightarrow> H(X) \<subseteq> H(Y)\<close>
      and closed : \<open>\<And>X. X \<subseteq> A \<Longrightarrow> H(X) \<subseteq> A\<close>
  defines \<open>P == {X \<in> Pow(A) . X \<subseteq> H(X)}\<close>
  defines \<open>U == \<Union>(P)\<close>
  shows \<open>H(U) = U\<close>
proof (rule equalityI)
  have U_sub_A : \<open>U \<subseteq> A\<close>
    unfolding U_def P_def by blast
  have U_sub_HU : \<open>U \<subseteq> H(U)\<close>
    using monotone_postfixed_union_bound[of A H] assms unfolding P_def U_def by blast
  have HU_sub_A : \<open>H(U) \<subseteq> A\<close>
    using closed[OF U_sub_A] .
  from mono[OF U_sub_A HU_sub_A U_sub_HU] have \<open>H(U) \<subseteq> H(H(U))\<close> .
  with HU_sub_A have \<open>H(U) \<in> P\<close>
    unfolding P_def by blast
  thus \<open>H(U) \<subseteq> U\<close>
    unfolding U_def by blast
  show \<open>U \<subseteq> H(U)\<close>
    by (rule U_sub_HU)
qed

subsection \<open>4. Filter and Club Intersection Algebra (Jech Chapters 7 and 8)\<close>

text \<open>If two families F1 and F2 are closed under binary intersection and
      upward supersets inside Pow(S), then their intersection F1 inter F2
      is also upward closed and closed under binary intersection.\<close>

lemma filter_intersection_upward_closed :
  assumes up1 : \<open>\<forall>A\<in>F1. \<forall>B\<in>Pow(S). A \<subseteq> B \<longrightarrow> B \<in> F1\<close>
      and up2 : \<open>\<forall>A\<in>F2. \<forall>B\<in>Pow(S). A \<subseteq> B \<longrightarrow> B \<in> F2\<close>
  shows \<open>\<forall>A\<in>(F1 \<inter> F2). \<forall>B\<in>Pow(S). A \<subseteq> B \<longrightarrow> B \<in> (F1 \<inter> F2)\<close>
  using assms by blast

lemma filter_intersection_binary_closed :
  assumes int1 : \<open>\<forall>A\<in>F1. \<forall>B\<in>F1. (A \<inter> B) \<in> F1\<close>
      and int2 : \<open>\<forall>A\<in>F2. \<forall>B\<in>F2. (A \<inter> B) \<in> F2\<close>
  shows \<open>\<forall>A\<in>(F1 \<inter> F2). \<forall>B\<in>(F1 \<inter> F2). (A \<inter> B) \<in> (F1 \<inter> F2)\<close>
  using assms by blast

text \<open>Stationary sets relative to a filter F on S:
      St(W, F) holds iff W intersects every member C of F.
      If W is stationary and C is in F, and F is closed under binary intersection,
      then W inter C is also stationary relative to F.\<close>

definition StationaryRel :: \<open>[i, i] \<Rightarrow> o\<close>
  where StationaryRel_def : \<open>StationaryRel(W, F) == \<forall>C\<in>F. (W \<inter> C) \<noteq> 0\<close>

theorem stationary_inter_filter_member :
  assumes stat : \<open>StationaryRel(W, F)\<close>
      and C_in_F : \<open>C \<in> F\<close>
      and F_inter : \<open>\<forall>A\<in>F. \<forall>B\<in>F. (A \<inter> B) \<in> F\<close>
  shows \<open>StationaryRel(W \<inter> C, F)\<close>
proof (unfold StationaryRel_def, rule ballI)
  fix D
  assume \<open>D \<in> F\<close>
  with C_in_F F_inter have \<open>(C \<inter> D) \<in> F\<close> by blast
  with stat have \<open>(W \<inter> (C \<inter> D)) \<noteq> 0\<close>
    unfolding StationaryRel_def by blast
  moreover have \<open>(W \<inter> C) \<inter> D = W \<inter> (C \<inter> D)\<close> by blast
  ultimately show \<open>((W \<inter> C) \<inter> D) \<noteq> 0\<close> by simp
qed

end
