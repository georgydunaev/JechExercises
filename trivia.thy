theory trivia imports ZF
begin

lemma UnE :
  assumes \<open>x \<in> (a \<union> b)\<close>
  shows \<open>x \<in> a \<or> x \<in> b\<close>
proof -
  have f:\<open>x \<in> \<Union>(Upair(a, b)) \<Longrightarrow> x \<in> a \<or> x \<in> b\<close>
    apply(erule UnionE)
    apply(erule UpairE)
    apply(erule subst[where b=a])
     apply(erule disjI1)
    apply(erule subst[where b=b])
     apply(erule disjI2)
    done
  have f:\<open>x \<in> \<Union>(Upair(a, b)) \<Longrightarrow> x \<in> a \<or> x \<in> b\<close>
  proof (erule UnionE)
    fix B
    assume \<open>x \<in> B\<close>
    assume \<open>B \<in> Upair(a, b)\<close> moreover
    (*hence \<open>B = a \<or> B = b\<close> by UpairWE*)
    from \<open>x \<in> B\<close> have \<open>x \<in> B \<or> x \<in> b\<close> by (rule disjI1)
    from \<open>x \<in> B\<close> have \<open>x \<in> a \<or> x \<in> B\<close> by (rule disjI2)
    have \<open>B = a \<Longrightarrow> x \<in> a \<or> x \<in> b\<close>
    proof -
      assume \<open>B = a\<close>
      from this and \<open>x \<in> B \<or> x \<in> b\<close> show \<open>x \<in> a \<or> x \<in> b\<close> by (rule subst[where b=a])
    qed moreover
    have \<open>B = b \<Longrightarrow> x \<in> a \<or> x \<in> b\<close> 
    proof -
      assume \<open>B = b\<close>
      from this and \<open>x \<in> a \<or> x \<in> B\<close> show \<open>x \<in> a \<or> x \<in> b\<close> by (rule subst[where b=b])
    qed
    ultimately show \<open>x \<in> a \<or> x \<in> b\<close> by (rule UpairE) 
  qed
  from \<open>x\<in>(a\<union>b)\<close> have \<open>x \<in> \<Union>(Upair(a, b))\<close> by (unfold Un_def)
  thus \<open>x \<in> a \<or> x \<in> b\<close> by (rule f)
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

