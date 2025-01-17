(*  Title:       Jech Exercises
    Author:      Georgy Dunaev <georgedunaev at gmail.com>, 2019
    Maintainer:  Georgy Dunaev <georgedunaev at gmail.com>
*)

section "Jech Exrecises"
theory JechExercises imports trivia
begin

text \<open>preliminaries\<close>
definition Ind :: \<open>i\<Rightarrow>o\<close>
  where Ind_def : \<open>Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close>

lemma IndInf : \<open>Ind(Inf)\<close>
  by(unfold Ind_def, rule infinity)

lemma IndI :
  assumes c0 : \<open>0 \<in> x\<close>
      and cS : \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close>
    shows \<open>Ind(x)\<close>
proof -
  from cS have \<open>\<And>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
    by (rule impI)
  hence \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
    by (rule allI)
  hence \<open>(\<forall>y\<in>x. succ(y) \<in> x)\<close>
    by (fold Ball_def)
  with c0 have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close>
    by (rule conjI)
  thus \<open>Ind(x)\<close> by (fold Ind_def)
qed

lemma IndE1 :
  assumes a:\<open>Ind(x)\<close>
  shows \<open>0 \<in> x\<close>
proof -
  from a
  have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close> by (unfold Ind_def)
  thus \<open>0 \<in> x\<close> by (rule conjunct1)
qed

lemma IndE2 :
  assumes a:\<open>Ind(x)\<close>
  shows \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
proof -
  from a
  have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close> by (unfold Ind_def)
  hence \<open>(\<forall>y\<in>x. succ(y) \<in> x)\<close> by (rule conjunct2)
  thus \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close> by (unfold Ball_def)
qed

lemma IndE2R :
  assumes \<open>Ind(x)\<close>
  shows \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close>
proof -
  from \<open>Ind(x)\<close> have \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close> by (rule IndE2)
  thus \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close> by (rule spec[THEN impE])
qed

text \<open>ex 1.1: Verify (a, b) = (c, d) if and only if a = c and b = d.\<close>

theorem ex_1_1 : \<open><a,b> = <c,d> \<longleftrightarrow> a=c & b=d\<close>
  by (rule pair.Pair_iff)

text \<open>ex 1.2: There is no set X such that $Pow(X)\subseteq X$.\<close>
context
  fixes S
  fixes W defines W_def : \<open>W == {x\<in>S. x\<notin>x}\<close>
begin

lemma notWinW :
  assumes y : \<open>W \<in> W\<close> 
  shows \<open>False\<close>
proof (rule notE[where P=\<open>W \<in> W\<close>])
  from y have \<open>W \<in> {x \<in> S . x \<notin> x}\<close> by (unfold W_def)
  then show \<open>W \<notin> W\<close> by (rule CollectD2)
next
  show \<open>W \<in> W\<close> by (rule y)
qed

theorem ex_1_2 : \<open>\<not> ( Pow(S) \<subseteq> S )\<close>
proof (rule notI)
  assume \<open>Pow(S) \<subseteq> S\<close>
  have \<open>{x \<in> S . x \<notin> x} \<subseteq> S\<close> using CollectD1 by (rule subsetI)
  hence \<open>W \<subseteq> S\<close> by (unfold W_def)
  hence \<open>W \<in> Pow(S)\<close> by (rule PowI)
  with \<open>Pow(S) \<subseteq> S\<close> have \<open>W \<in> S\<close> by (rule subsetD)
  show \<open>False\<close>
  proof (rule case_split[where P=\<open>W \<in> W\<close>])
    show \<open>W \<in> W \<Longrightarrow> False\<close> by (rule notWinW)
  next
    from \<open>W \<in> S\<close> have \<open>{x \<in> S . x \<notin> x} \<in> S\<close> by (unfold W_def) moreover
    assume \<open>W \<notin> W\<close>
    hence \<open>{x \<in> S . x \<notin> x} \<notin> {x \<in> S . x \<notin> x}\<close> by (unfold W_def)
    ultimately have \<open>{x \<in> S . x \<notin> x} \<in> {x \<in> S . x \<notin> x}\<close> by (rule CollectI)
    hence \<open>W \<in> W\<close> by (fold W_def) 
    with \<open>W \<notin> W\<close>
    show \<open>False\<close> by (rule notE)
  qed
qed
end

text \<open>ex 1.3: If X is inductive, then the set $\{x \in X : x \subseteq X\}$ is inductive. Hence N is
transitive, and for each n, $n = \{m \in N : m < n\}$.\<close>
context
  fixes x
  assumes a:\<open>Ind(x)\<close>
begin
lemma subsetsu : \<open>\<And>xa. xa \<in> {y \<in> x . y \<subseteq> x} \<Longrightarrow>
          succ(xa) \<in> {y \<in> x . y \<subseteq> x}\<close> 
proof -
  fix k
  assume h:\<open>k \<in> {y \<in> x . y \<subseteq> x}\<close>
  from h have h1:\<open>k \<in> x\<close> by (rule CollectD1[where A=\<open>x\<close>])
  from h have h2:\<open>k \<subseteq> x\<close> by (rule CollectD2[where P=\<open>\<lambda>w. w\<subseteq>x\<close>])
  from a and h1 have \<open>succ(k) \<in> x\<close> by (rule IndE2R)
  have \<open>\<And>xa. xa \<in> succ(k) \<Longrightarrow> xa \<in> x\<close>
  proof -
    fix xa
    assume \<open>xa \<in> succ(k)\<close>
    hence \<open>xa = k \<or> xa \<in> k\<close> by (rule SuccE)
    thus \<open>xa \<in> x\<close>
    proof (rule disjE)
      assume \<open>xa = k\<close>
      with h1 show \<open>xa \<in> x\<close> by (rule subst_elem)
    next
      assume \<open>xa \<in> k\<close>
      with h2  show \<open>xa \<in> x\<close> by (rule subsetD)
    qed
  qed
  hence \<open>succ(k) \<subseteq> x\<close> by (rule subsetI)
  with \<open>succ(k) \<in> x\<close>
  show \<open>succ(k) \<in> {y \<in> x . y \<subseteq> x}\<close> by (rule CollectI[where P=\<open>\<lambda>y. y\<subseteq>x\<close>])
qed  

theorem ex1_3:
  shows \<open>Ind({y\<in>x. y\<subseteq>x})\<close>
proof -
  from a
  have \<open>0 \<in> x\<close> by (rule IndE1)
  have \<open>0 \<subseteq> x\<close> by (rule empty_subsetI)
  with \<open>0 \<in> x\<close> have d:\<open>0 \<in> {y \<in> x . y \<subseteq> x}\<close> by (rule CollectI)
  from d and subsetsu show \<open>Ind({y\<in>x. y\<subseteq>x})\<close> by (rule IndI)
qed

end

definition ClassInter :: \<open>(i\<Rightarrow>o)\<Rightarrow>(i\<Rightarrow>o)\<close>
  where ClassInter_def : \<open>ClassInter(P,x) == \<forall>y. P(y) \<longrightarrow> x\<in>y\<close>

definition Nat :: \<open>i\<Rightarrow>o\<close>
  where \<open>Nat == ClassInter(Ind)\<close>

lemma NatSubInf : \<open>\<And>x. Nat(x) \<Longrightarrow> x\<in>Inf\<close>
proof (unfold Nat_def)
  fix x
  assume p0:\<open>ClassInter(Ind, x)\<close>
  show \<open>x\<in>Inf\<close>
  proof -
    from p0 have \<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close> by (unfold ClassInter_def)
    hence \<open>Ind(Inf) \<longrightarrow> x \<in> Inf\<close> by (rule spec)
    hence p3:\<open>Ind(Inf) \<Longrightarrow> x \<in> Inf\<close> by (rule mp)
    from IndInf show p4:\<open>x \<in> Inf\<close> by (rule p3)
  qed
qed

lemma NatSubInf' : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
proof (rule allI)
  fix x from NatSubInf show \<open>(Nat(x) \<longrightarrow> x\<in>Inf)\<close> by (rule impI)
qed

definition IsTransClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsTransClass_def : \<open>IsTransClass(P) == \<forall>y. P(y) \<longrightarrow> (\<forall>z. z\<in>y \<longrightarrow> P(z))\<close>

lemma Nat0 : \<open>Nat(0)\<close>
proof -
  have \<open>\<And>y. 0 \<in> y \<and> (\<forall>ya\<in>y. succ(ya) \<in> y) \<Longrightarrow> 0 \<in> y\<close> by (erule conjE)
  hence \<open>\<And>y. Ind(y) \<Longrightarrow> 0 \<in> y\<close> by (unfold Ind_def)
  hence \<open>\<And>y. Ind(y) \<longrightarrow> 0 \<in> y\<close> by (rule impI)
  hence \<open>\<forall>y. Ind(y) \<longrightarrow> 0 \<in> y\<close> by (rule allI)
  hence \<open>ClassInter(Ind, 0)\<close> by (unfold ClassInter_def) 
  thus ?thesis by (unfold Nat_def)
qed

lemma NatSu:
  fixes x w
  assumes a:\<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close>
  assumes b:\<open>Ind(w)\<close>
  shows \<open>succ(x) \<in> w\<close>
proof -
  from b have j:\<open>\<And>xa. xa \<in> w \<Longrightarrow> succ(xa) \<in> w\<close> by (rule IndE2R)
  from a have \<open>Ind(w) \<longrightarrow> x \<in> w\<close> by (rule spec)
  from this and b have \<open>x \<in> w\<close> by (rule mp)
  from \<open>x \<in> w\<close> show \<open>succ(x) \<in> w\<close> by (rule j)
qed

lemma NatSucc : \<open>\<forall>x. Nat(x) \<longrightarrow> Nat(succ(x))\<close>
proof (rule allI[OF impI])
  fix x
  assume \<open>Nat(x)\<close>
  hence \<open>ClassInter(Ind)(x)\<close> by (unfold Nat_def)
  hence \<open>\<forall>y. Ind(y) \<longrightarrow> x\<in>y\<close> by (unfold ClassInter_def)
  have \<open>\<forall>y. Ind(y) \<longrightarrow> succ(x)\<in>y\<close>
  proof (rule allI[OF impI])
    fix y
    assume \<open>Ind(y)\<close>
    with \<open>\<forall>y. Ind(y) \<longrightarrow> x\<in>y\<close> show \<open>succ(x)\<in>y\<close> by (rule NatSu)
  qed
  hence \<open>ClassInter(Ind)(succ(x))\<close> by (fold ClassInter_def)
  then show \<open>Nat(succ(x))\<close> by (fold Nat_def)
qed

definition IsIndClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsIndClass_def : \<open>IsIndClass(P) == P(0) \<and> (\<forall>y. P(y) \<longrightarrow> P(succ(y)))\<close>

lemma NatIsInd : \<open>IsIndClass(Nat)\<close>
proof (unfold IsIndClass_def)
  from Nat0 and NatSucc 
  show \<open>Nat(0) \<and> (\<forall>y. Nat(y) \<longrightarrow> Nat(succ(y)))\<close> by (rule conjI)
qed

definition Omega :: \<open>i\<close>
  where Omega_def : \<open>Omega == { y \<in> Inf . Nat(y) }\<close>

lemma NatSubOmega : \<open>\<And>x. Nat(x) \<Longrightarrow> x \<in> Omega\<close>
proof -
  fix x
  assume \<open>Nat(x)\<close>
  hence \<open>x \<in> Inf\<close> by (rule NatSubInf)
  from \<open>x \<in> Inf\<close> and \<open>Nat(x)\<close> have \<open>x \<in> {x\<in>Inf. Nat(x)}\<close> by (rule CollectI)
  thus \<open>x \<in> Omega\<close> by (fold Omega_def)
qed

notepad
begin
assume a: A and b: B
thm conjI
thm conjI [of A B] (*— instantiation*)
thm conjI [of A B, OF a b] (*— instantiation and composition*)
thm conjI [OF a b] (*— composition via unification (trivial)*)
(*thm conjI [OF "A" "B"]*)
thm conjI [OF disjI1]
end

(* image f of union is the union of images f *)
(* lemma image_UN: "r `` (\<Union>x\<in>A. B(x)) = (\<Union>x\<in>A. r `` B(x))" *)

lemma "r``(\<Union>A) = (\<Union>x\<in>A. r``x)"
  by blast

lemma "r``(\<Union>A) = (\<Union>x\<in>A. r``x)"
proof (rule equalityI)
  have l1:\<open>\<And>x. x \<in> r `` (\<Union>A) \<Longrightarrow>
         x \<in> (\<Union>x\<in>A. r `` x)\<close>
  proof -
    fix x
    assume a1:\<open>x \<in> r `` (\<Union>A)\<close>
    hence a2:\<open>x \<in> {y \<in> range(r) . \<exists>x\<in>\<Union>A. \<langle>x, y\<rangle> \<in> r}\<close> by (unfold image_def)
(*    from a2 have a3:\<open>x \<in> range(r)\<close> by (rule CollectE)*)
    from a2 have a4:\<open>\<exists>xa\<in>\<Union>A. \<langle>xa, x\<rangle> \<in> r\<close> by (rule CollectE)
    from a4 obtain xa where b1:"xa\<in>\<Union>A" and b2:"\<langle>xa, x\<rangle> \<in> r" by (rule bexE)
    from b1 obtain y where q1:\<open>xa\<in>y\<close> and q2:\<open>y\<in>A\<close> by (rule UnionE)
    from b2 and q1 have c1:\<open>x \<in> r `` y\<close>  by (rule imageI)
    from b2 have e1:\<open>x \<in> range(r)\<close> by (rule rangeI)
(*    from q2 and c1 show \<open>x \<in> (\<Union>x\<in>A. r `` x)\<close> by (rule UN_I)*)
    from q2 and c1 have q:\<open>x \<in> (\<Union>x\<in>A. r `` x)\<close> by (rule UN_I)
    show \<open>x \<in> (\<Union>x\<in>A. r `` x)\<close> by (rule q)
  qed
  thus \<open>r `` (\<Union>A) \<subseteq> (\<Union>x\<in>A. r `` x)\<close> by (rule subsetI)
next
  have l2:\<open>\<And>x. x \<in> (\<Union>x\<in>A. r `` x) \<Longrightarrow> x \<in> r `` (\<Union>A)\<close>
  proof -
    fix x
    assume a0:\<open>x \<in> (\<Union>x\<in>A. r `` x)\<close> 
    (*! have \<open>x \<in> (\<Union>x\<in>A. r `` x)\<close> apply standard sorry !*)
    from a0 obtain B where \<open>B \<in> {r `` x . x \<in> A}\<close> and \<open>x \<in> B\<close> by standard
    (*! have \<open>B \<in> {r `` x . x \<in> A}\<close> apply standard sorry !*)
    from \<open>B \<in> {r `` x . x \<in> A}\<close> obtain g where \<open>B = r `` g\<close> and \<open>g \<in> A\<close> by standard
    from \<open>B = r `` g\<close> and \<open>x \<in> B\<close> have \<open>x \<in> r `` g\<close> by (rule subst)
(*    have  \<open>x \<in> r `` g\<close> apply standard *)
    from  \<open>x \<in> r `` g\<close> obtain aa where  "\<langle>aa, x\<rangle> \<in> r" and "aa \<in> g" by standard
    from \<open>g \<in> A\<close> and \<open>aa \<in> g\<close> have \<open>aa \<in> \<Union>A\<close> by (rule UnionI)
    from \<open>\<langle>aa, x\<rangle> \<in> r\<close> and \<open>aa \<in> \<Union>A\<close> show \<open>x \<in> r `` (\<Union>A)\<close> by standard
    (*show \<open>x \<in> r `` (\<Union>A)\<close> sorry*)
  qed
  thus \<open>(\<Union>x\<in>A. r `` x) \<subseteq> r `` (\<Union>A)\<close> by (rule subsetI)
qed

lemma Transset_trans_Memrel:
    "\<forall>j\<in>i. Transset(j) ==> trans(Memrel(i))"
  by (unfold Transset_def trans_def, blast)

(* comments:
(*
    from \<open>x \<in> \<Union>Pow(A)\<close> obtain B 
      where p1:\<open>x \<in> B\<close> and p2:\<open>B \<in> Pow(A)\<close>
      by (erule UnionE)
*)
    have \<open>x \<in> {y \<in> range(r) . \<exists>x\<in>\<Union>A. \<langle>x, y\<rangle> \<in> r}\<close>
      apply (rule CollectI)
      sorry
    
    have \<open>x \<in> r `` (\<Union>A)\<close>
      apply (unfold image_def)
      sorry
...
    show \<open>x \<in> (\<Union>x\<in>A. r `` x)\<close>
      apply (rule UN_I)
       apply (rule q2)
      apply (rule c1)
      apply (unfold image_def)
      apply (rule CollectI)
      apply (unfold range_def)
    (*proof - 
      show ?thesis by blast*)
      sorry
comments*)

(*
lemma
  fixes f A B
(*  assumes a:\<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close> *)
  assumes b:\<open>Ind(w)\<close> 
  shows \<open>succ(x) \<in> w\<close>
*)
(* recursion theorem *)

(*
text\<open>Cantor's theorem revisited\<close>
lemma cantor_surj: "f \<notin> surj(A,Pow(A))"
  apply (unfold surj_def, safe)
  apply (cut_tac cantor)
  apply (best del: subsetI)
  done
*)


axiomatization
  myeq :: \<open>[i\<Rightarrow>o, i\<Rightarrow>o] \<Rightarrow> o\<close>  (infixl \<open>=C\<close> 50)
where
  myrefl: \<open>a =C a\<close> and
  mysubst: \<open>a =C b \<Longrightarrow> P(a) \<Longrightarrow> P(b)\<close>

(*
axiomatization
  eq :: \<open>['a, 'a] \<Rightarrow> o\<close>  (infixl \<open>=\<close> 50)
where
  refl: \<open>a = a\<close> and
  subst: \<open>a = b \<Longrightarrow> P(a) \<Longrightarrow> P(b)\<close>
*)
(*
lemma qu:
  fixes C::\<open>i\<Rightarrow>o\<close>
  shows \<open>(=)(C,C)\<close>
*)
(*"\<lbrakk>C 0;\<And>\<alpha>. \<alpha>\<in>C\<Longrightarrow>\<alpha>+1\<in>C \<rbrakk> \<Longrightarrow> C=Ord"*)
  


lemma transfinite_induction111 : "\<lbrakk>0\<in>C;\<And>\<alpha>. \<alpha>\<in>C\<Longrightarrow>\<alpha>+1\<in>C \<rbrakk> \<Longrightarrow> 0\<in>C"
  apply assumption
  done

lemma transfinite_induction22 : "0\<in>C \<Longrightarrow> 0\<in>C"
  apply assumption
  done

(* untyped lambda calculus *)

(*definition
  POS  :: "[i,[i,i]\<Rightarrow>o]=>o"  where
    "POS(D,\<sqsubseteq>) == (\<forall>x\<in>D.\<sqsubseteq>(x,x))\<and>"*)

context
  fixes D::i
  (*fixes \<sqsubseteq>::[i,i]\<Rightarrow>o*)
  fixes otn::i ("\<sqsubseteq>")
  assumes reflrel:\<open>\<forall>x\<in>D. <x,y>\<in>\<sqsubseteq>\<close>
  assumes antisymrel:\<open>\<forall>x\<in>D. \<forall>y\<in>D. <x,y>\<in>\<sqsubseteq> \<and> <y,x>\<in>\<sqsubseteq> \<longrightarrow> x=y\<close>
  assumes transrel:\<open>\<forall>x\<in>D.\<forall>y\<in>D.\<forall>z\<in>D. <x,y>\<in>\<sqsubseteq> \<and> <y,z>\<in>\<sqsubseteq> \<longrightarrow> <x,z>\<in>\<sqsubseteq>\<close>
  (*assumes dpos:\<open>POS(D,\<sqsubseteq>)\<close>*)
begin
end

definition
  eqc  :: "[(i\<Rightarrow>o),(i\<Rightarrow>o)]=>o" where
    "eqc(A,B) == \<forall>x. A(x) \<longleftrightarrow> B(x)"

(* Transfinite induction. *)
lemma transfinite_induction:
  fixes C::"i\<Rightarrow>o"
  assumes c0:\<open>C(0)\<close>
  assumes cS:\<open>\<forall>x. C(x)\<longrightarrow>C(succ(x))\<close>
  assumes cL:\<open>\<forall>x. C(x)\<longrightarrow>C(succ(x))\<close>
assumes a:\<open>Ind(x)\<close>
  shows \<open>eqc(C,Ord)\<close>

  oops

end
