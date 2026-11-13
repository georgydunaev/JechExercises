(*  Title:       Filters and Ultrafilters
    Author:      Georgy Dunaev and Autonomous Contributor, 2026
    Maintainer:  Georgy Dunaev <georgedunaev at gmail.com>
*)

theory filters imports ZF
begin

section \<open>Lattice Properties of Powerset\<close>

lemma Diff_Diff_elem:
  assumes \<open>A \<subseteq> S\<close> and \<open>x \<in> A\<close>
  shows \<open>x \<in> S - (S - A)\<close>
proof -
  from assms have \<open>x \<in> S\<close> by (rule subsetD)
  have \<open>x \<notin> S - A\<close>
  proof (rule notI)
    assume \<open>x \<in> S - A\<close>
    hence \<open>x \<notin> A\<close> by (rule DiffD2)
    with \<open>x \<in> A\<close> show False by (rule notE)
  qed
  with \<open>x \<in> S\<close> show \<open>x \<in> S - (S - A)\<close> by (rule DiffI)
qed

lemma Diff_Diff_elem2:
  assumes \<open>x \<in> S - (S - A)\<close>
  shows \<open>x \<in> A\<close>
proof (rule ccontr)
  assume \<open>x \<notin> A\<close>
  from assms have \<open>x \<in> S\<close> by (rule DiffD1)
  with \<open>x \<notin> A\<close> have \<open>x \<in> S - A\<close> by (rule DiffI)
  from assms have \<open>x \<notin> S - A\<close> by (rule DiffD2)
  with \<open>x \<in> S - A\<close> show False by (rule notE)
qed

lemma Diff_Diff_eq:
  assumes \<open>A \<subseteq> S\<close>
  shows \<open>S - (S - A) = A\<close>
proof (rule equalityI)
  show \<open>S - (S - A) \<subseteq> A\<close>
  proof (rule subsetI)
    fix x assume \<open>x \<in> S - (S - A)\<close>
    thus \<open>x \<in> A\<close> by (rule Diff_Diff_elem2)
  qed
next
  show \<open>A \<subseteq> S - (S - A)\<close>
  proof (rule subsetI)
    fix x assume \<open>x \<in> A\<close>
    with assms show \<open>x \<in> S - (S - A)\<close> by (rule Diff_Diff_elem)
  qed
qed

lemma Inter_subset_left: \<open>A \<inter> B \<subseteq> A\<close>
  by (rule Int_lower1)

lemma Inter_subset_right: \<open>A \<inter> B \<subseteq> B\<close>
  by (rule Int_lower2)

lemma Union_subset_intro:
  assumes \<open>A \<subseteq> C\<close> and \<open>B \<subseteq> C\<close>
  shows \<open>A \<union> B \<subseteq> C\<close>
  using assms by (rule Un_least)

lemma Inter_greatest:
  assumes \<open>C \<subseteq> A\<close> and \<open>C \<subseteq> B\<close>
  shows \<open>C \<subseteq> A \<inter> B\<close>
  using assms by (rule Int_greatest)

section \<open>Filter Definitions and Basic Properties\<close>

definition is_filter :: \<open>[i, i] \<Rightarrow> o\<close> where
  \<open>is_filter(F, S) == F \<subseteq> Pow(S) \<and>
                      S \<in> F \<and>
                      0 \<notin> F \<and>
                      (\<forall>A\<in>F. \<forall>B\<in>F. A \<inter> B \<in> F) \<and>
                      (\<forall>A\<in>F. \<forall>B\<in>Pow(S). A \<subseteq> B \<longrightarrow> B \<in> F)\<close>

definition is_ultrafilter :: \<open>[i, i] \<Rightarrow> o\<close> where
  \<open>is_ultrafilter(U, S) == is_filter(U, S) \<and>
                            (\<forall>A\<in>Pow(S). A \<in> U \<or> (S - A) \<in> U)\<close>

definition is_ideal :: \<open>[i, i] \<Rightarrow> o\<close> where
  \<open>is_ideal(I, S) == I \<subseteq> Pow(S) \<and>
                     0 \<in> I \<and>
                     S \<notin> I \<and>
                     (\<forall>A\<in>I. \<forall>B\<in>I. A \<union> B \<in> I) \<and>
                     (\<forall>A\<in>I. \<forall>B\<in>Pow(S). B \<subseteq> A \<longrightarrow> B \<in> I)\<close>

definition principal_filter :: \<open>[i, i] \<Rightarrow> i\<close> where
  \<open>principal_filter(A, S) == {X \<in> Pow(S). A \<subseteq> X}\<close>

lemma filter_in_Pow:
  assumes \<open>is_filter(F, S)\<close> and \<open>X \<in> F\<close>
  shows \<open>X \<subseteq> S\<close>
proof -
  from assms(1) have \<open>F \<subseteq> Pow(S)\<close> by (unfold is_filter_def, rule conjunct1)
  with assms(2) have \<open>X \<in> Pow(S)\<close> by (rule subsetD)
  thus \<open>X \<subseteq> S\<close> by (rule PowD)
qed

lemma filter_nonempty:
  assumes \<open>is_filter(F, S)\<close> and \<open>X \<in> F\<close>
  shows \<open>X \<noteq> 0\<close>
proof (rule notI)
  assume \<open>X = 0\<close>
  with assms(2) have \<open>0 \<in> F\<close> by (rule subst)
  from assms(1) have \<open>0 \<notin> F\<close>
    by (unfold is_filter_def, blast)
  with \<open>0 \<in> F\<close> show False by (rule notE)
qed

lemma filter_inter_closed:
  assumes \<open>is_filter(F, S)\<close> and \<open>A \<in> F\<close> and \<open>B \<in> F\<close>
  shows \<open>A \<inter> B \<in> F\<close>
proof -
  from assms(1) have \<open>\<forall>A\<in>F. \<forall>B\<in>F. A \<inter> B \<in> F\<close>
    by (unfold is_filter_def, blast)
  with assms(2) assms(3) show \<open>A \<inter> B \<in> F\<close> by blast
qed

lemma filter_upward_closed:
  assumes \<open>is_filter(F, S)\<close> and \<open>A \<in> F\<close> and \<open>B \<subseteq> S\<close> and \<open>A \<subseteq> B\<close>
  shows \<open>B \<in> F\<close>
proof -
  from assms(3) have \<open>B \<in> Pow(S)\<close> by (rule PowI)
  from assms(1) have \<open>\<forall>A\<in>F. \<forall>B\<in>Pow(S). A \<subseteq> B \<longrightarrow> B \<in> F\<close>
    by (unfold is_filter_def, blast)
  with assms(2) \<open>B \<in> Pow(S)\<close> assms(4) show \<open>B \<in> F\<close> by blast
qed

section \<open>Principal Filters\<close>

lemma principal_filter_subset:
  shows \<open>principal_filter(A, S) \<subseteq> Pow(S)\<close>
  unfolding principal_filter_def by (rule Collect_subset)

lemma principal_filter_ground:
  assumes \<open>A \<subseteq> S\<close>
  shows \<open>S \<in> principal_filter(A, S)\<close>
proof -
  have \<open>S \<in> Pow(S)\<close> by auto
  with assms show \<open>S \<in> principal_filter(A, S)\<close>
    unfolding principal_filter_def by (rule CollectI)
qed

lemma principal_filter_no_zero:
  assumes \<open>A \<noteq> 0\<close>
  shows \<open>0 \<notin> principal_filter(A, S)\<close>
proof (rule notI)
  assume \<open>0 \<in> principal_filter(A, S)\<close>
  hence \<open>A \<subseteq> 0\<close> unfolding principal_filter_def by (rule CollectD2)
  hence \<open>A = 0\<close> by auto
  with assms show False by contradiction
qed

lemma principal_filter_inter:
  assumes \<open>X \<in> principal_filter(A, S)\<close> and \<open>Y \<in> principal_filter(A, S)\<close>
  shows \<open>X \<inter> Y \<in> principal_filter(A, S)\<close>
proof -
  from assms(1) have \<open>X \<in> Pow(S)\<close> and \<open>A \<subseteq> X\<close>
    unfolding principal_filter_def by (rule CollectD1, rule CollectD2)
  from assms(2) have \<open>Y \<in> Pow(S)\<close> and \<open>A \<subseteq> Y\<close>
    unfolding principal_filter_def by (rule CollectD1, rule CollectD2)
  from \<open>X \<in> Pow(S)\<close> \<open>Y \<in> Pow(S)\<close> have \<open>X \<inter> Y \<in> Pow(S)\<close> by auto
  moreover from \<open>A \<subseteq> X\<close> \<open>A \<subseteq> Y\<close> have \<open>A \<subseteq> X \<inter> Y\<close> by (rule Int_greatest)
  ultimately show \<open>X \<inter> Y \<in> principal_filter(A, S)\<close>
    unfolding principal_filter_def by (rule CollectI)
qed

lemma principal_filter_upward:
  assumes \<open>X \<in> principal_filter(A, S)\<close> and \<open>Y \<in> Pow(S)\<close> and \<open>X \<subseteq> Y\<close>
  shows \<open>Y \<in> principal_filter(A, S)\<close>
proof -
  from assms(1) have \<open>A \<subseteq> X\<close>
    unfolding principal_filter_def by (rule CollectD2)
  with assms(3) have \<open>A \<subseteq> Y\<close> by (rule subset_trans)
  with assms(2) show \<open>Y \<in> principal_filter(A, S)\<close>
    unfolding principal_filter_def by (rule CollectI)
qed

theorem principal_filter_is_filter:
  assumes \<open>A \<subseteq> S\<close> and \<open>A \<noteq> 0\<close>
  shows \<open>is_filter(principal_filter(A, S), S)\<close>
proof (unfold is_filter_def, intro conjI)
  show \<open>principal_filter(A, S) \<subseteq> Pow(S)\<close> by (rule principal_filter_subset)
next
  from assms(1) show \<open>S \<in> principal_filter(A, S)\<close> by (rule principal_filter_ground)
next
  from assms(2) show \<open>0 \<notin> principal_filter(A, S)\<close> by (rule principal_filter_no_zero)
next
  show \<open>\<forall>X\<in>principal_filter(A, S). \<forall>Y\<in>principal_filter(A, S). X \<inter> Y \<in> principal_filter(A, S)\<close>
    using principal_filter_inter by blast
next
  show \<open>\<forall>X\<in>principal_filter(A, S). \<forall>Y\<in>Pow(S). X \<subseteq> Y \<longrightarrow> Y \<in> principal_filter(A, S)\<close>
    using principal_filter_upward by blast
qed

section \<open>Principal Ultrafilters on Singletons\<close>

theorem singleton_principal_is_ultrafilter:
  assumes \<open>a \<in> S\<close>
  shows \<open>is_ultrafilter(principal_filter({a}, S), S)\<close>
proof (unfold is_ultrafilter_def, rule conjI)
  have \<open>{a} \<subseteq> S\<close> using assms by auto
  have \<open>{a} \<noteq> 0\<close> by auto
  with \<open>{a} \<subseteq> S\<close> show \<open>is_filter(principal_filter({a}, S), S)\<close>
    by (rule principal_filter_is_filter)
next
  show \<open>\<forall>X\<in>Pow(S). X \<in> principal_filter({a}, S) \<or> (S - X) \<in> principal_filter({a}, S)\<close>
  proof (rule ballI)
    fix X
    assume \<open>X \<in> Pow(S)\<close>
    hence \<open>X \<subseteq> S\<close> by (rule PowD)
    show \<open>X \<in> principal_filter({a}, S) \<or> (S - X) \<in> principal_filter({a}, S)\<close>
    proof (cases \<open>a \<in> X\<close>)
      case True
      hence \<open>{a} \<subseteq> X\<close> by auto
      with \<open>X \<in> Pow(S)\<close> have \<open>X \<in> principal_filter({a}, S)\<close>
        unfolding principal_filter_def by (rule CollectI)
      thus ?thesis by (rule disjI1)
    next
      case False
      from assms and False have \<open>a \<in> S - X\<close> by (rule DiffI)
      hence \<open>{a} \<subseteq> S - X\<close> by auto
      have \<open>S - X \<in> Pow(S)\<close> by auto
      with \<open>{a} \<subseteq> S - X\<close> have \<open>(S - X) \<in> principal_filter({a}, S)\<close>
        unfolding principal_filter_def by (rule CollectI)
      thus ?thesis by (rule disjI2)
    qed
  qed
qed

end
