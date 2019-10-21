theory trivia imports ZF
begin

lemma inSing : \<open>xa \<in> Upair(k, k) \<Longrightarrow> xa = k\<close>
proof (erule UpairE)
  assume h:\<open>xa = k\<close> 
  show \<open>xa = k\<close> by (rule h)
next
  assume h:\<open>xa = k\<close> 
  show \<open>xa = k\<close> by (rule h)
qed

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

lemma inSucc :
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
    hence \<open>xa = k\<close> by (rule inSing)
    thus \<open>xa = k \<or> xa \<in> k\<close> by (rule disjI1)
  qed
qed

lemma ww1:
  assumes \<open>k \<in> x\<close>
      and \<open>m \<in> Upair(k, k)\<close>
    shows \<open>m \<in> x\<close>
proof -
  from \<open>m \<in> Upair(k, k)\<close> have \<open>m = k\<close> by (rule inSing) 
  with \<open>k \<in> x\<close> show \<open>m \<in> x\<close> by (rule subst_elem)
qed

lemma ww:
  assumes \<open>k \<in> x\<close>
  and \<open>k \<subseteq> x\<close>
  shows \<open>m \<in> Upair(k, k) \<or> m \<in> k \<Longrightarrow> m \<in> x\<close>
proof(erule disjE)
  from \<open>k \<in> x\<close> show \<open>m \<in> Upair(k, k) \<Longrightarrow> m \<in> x\<close> by (rule ww1)
next
  from \<open>k \<subseteq> x\<close> show \<open>m \<in> k \<Longrightarrow> m \<in> x\<close> by (rule subsetD)
qed

end