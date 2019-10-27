theory trivia imports ZF
begin

lemma In_sound_right : \<open>x\<in>A \<Longrightarrow> A=B \<Longrightarrow> x\<in>B\<close>
  apply (erule subst[where b=B])
  apply assumption
  done

lemma UnE :
  assumes \<open>x \<in> (a \<union> b)\<close>
  shows \<open>x \<in> a \<or> x \<in> b\<close>
proof -
  from \<open>x\<in>(a\<union>b)\<close> have \<open>x \<in> \<Union>(Upair(a, b))\<close> by (unfold Un_def)
  from \<open>x \<in> \<Union>(Upair(a, b))\<close> obtain B
    where p1:\<open>x \<in> B\<close> and p2:\<open>B \<in> Upair(a, b)\<close>
    by (erule UnionE)
  from \<open>B \<in> Upair(a, b)\<close> have \<open>B = a \<or> B = b\<close> by (rule UpairE, auto)
  from p1 have l1:\<open>B = a \<Longrightarrow> x \<in> a\<close> by (rule In_sound_right)
  from p1 have l2:\<open>B = b \<Longrightarrow> x \<in> b\<close> by (rule In_sound_right)
  from \<open>B = a \<or> B = b\<close> and l1 and l2
  show \<open>x \<in> a \<or> x \<in> b\<close> by (rule disj_imp_disj)
qed

lemma SuccE :
  fixes xa and k
  assumes \<open>xa \<in> succ(k)\<close>
  shows \<open>xa = k \<or> xa \<in> k\<close>
proof -
  from \<open>xa \<in> succ(k)\<close> have \<open>xa \<in> cons(k, k)\<close> by (unfold succ_def)
  hence \<open>xa \<in> (Upair(k,k) \<union> k)\<close> by (unfold cons_def)
  hence \<open>xa \<in> Upair(k,k) \<or> xa \<in> k\<close> by (rule UnE) 
  thus \<open>xa = k \<or> xa \<in> k\<close>
  proof (rule disjE)
    show \<open>xa \<in> k \<Longrightarrow> xa = k \<or> xa \<in> k\<close> by (rule disjI2)
  next
    assume \<open>xa \<in> Upair(k, k)\<close>
    hence \<open>xa = k\<close> by (rule upair.UpairE)
    thus \<open>xa = k \<or> xa \<in> k\<close> by (rule disjI1)
  qed
qed

lemma AeqUPA:\<open>A = \<Union>Pow(A)\<close>
proof (rule equalityI)
  have \<open>\<And>x. x \<in> \<Union>Pow(A) \<Longrightarrow> x \<in> A\<close>
  proof -
    fix x
    assume \<open>x \<in> \<Union>Pow(A)\<close>
    from \<open>x \<in> \<Union>Pow(A)\<close> obtain B
      where p1:\<open>x \<in> B\<close> and p2:\<open>B \<in> Pow(A)\<close>
      by (erule UnionE)
    from \<open>B \<in> Pow(A)\<close> have \<open>B \<subseteq> A\<close> by (rule PowD)
    from \<open>x \<in> B\<close> and \<open>B \<subseteq> A\<close> show \<open>x \<in> A\<close> by (rule rev_subsetD)
  qed
  then show \<open>\<Union>Pow(A) \<subseteq> A\<close>
    by (rule subsetI)
next
  have \<open>\<And>x. x \<in> A \<Longrightarrow> x \<in> \<Union>Pow(A)\<close>
  proof -
    fix x
    assume \<open>x \<in> A\<close>
    have \<open>A \<in> Pow(A)\<close> by auto
    from \<open>A \<in> Pow(A)\<close> and \<open>x \<in> A\<close>
    show \<open>x \<in> \<Union>Pow(A)\<close> by (rule UnionI)
  qed
  then show \<open>A \<subseteq> \<Union>Pow(A)\<close> by (rule subsetI)
qed

end

