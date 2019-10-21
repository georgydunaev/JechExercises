(*
(* need: IndClass(Nat) 
0 \in Nat по опред

*)
(* x in Nat \<Rightarrow> x in every y s.t. Ind(y).  
  exists I, Ind(I)
   Ind(I)  Ind({w\in I: w\<subseteq>I})
Need: x \<subseteq> Nat.
{w\in y: w\<subseteq>y} \<subseteq> y

Nat \<subseteq> {w\in I: w\<subseteq>I}

0 \in Nat

*)
(*
lemma TheIs : \<open>......\<Longrightarrow> x=The(P) \<Longrightarrow> P(x)\<close>
  apply(unfold the_def)
  apply(erule equalityE)
  (*apply(rule subsetD)
  apply(erule UnionE)
  apply(erule ReplaceE2)*)
  sorry

lemma TheE : \<open>P(The(P))\<close>
  apply(rule subst)
   prefer 2
  apply(rule TheIs)
   apply(rule refl)
  apply(rule refl)
  done
*)
(*
lemma rty : \<open>\<And>x B. x \<in> B \<Longrightarrow> Nat(B) \<Longrightarrow> Ind(x)\<close>
  apply(unfold Ind_def)
  apply(rule conjI)
*)
(*\<And>x B xa. x \<in> B \<Longrightarrow> xa \<in> {0} \<Longrightarrow> Nat(B) \<Longrightarrow> Nat(x)*)

(* ==== here ==== *)

lemma wer : \<open>The(Nat) \<subseteq> Inf\<close>
  apply(rule subsetI)
  apply(rule mp)
   apply(rule spec[OF lwe])(*or [where P="\<lambda>w. Nat(w) \<longrightarrow> w\<in>Inf"])*)

  apply(unfold the_def)
  apply(erule UnionE)
  apply(erule ReplaceE2)

  apply(unfold Nat_def)

  apply(rule lwe)


lemma lwe : (* \<open>\<forall>x. Nat(x) \<longrightarrow> x\<in>Inf\<close> *)
  fixes x
  assumes a:"Nat(x)"
  shows "x\<in>Inf"
proof -
oops

lemma ex1_4:
  fixes x
  assumes a:"Ind(x)"
  shows "Ind({y\<in>x. y\<subseteq>x})"
proof -
  oops

(*
axiomatization 
 (i\<Rightarrow>o)\<Rightarrow>i 
definition subcl :: \<open>'a \<Rightarrow>'a \<Rightarrow>o\<close>
  where subcl_def : "subcl(a,b) ==  \<forall> z. a(z) \<longrightarrow> b(z)"
*)
  (*from a
  have b: "0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)"
  proof (unfold Ind_def) qed*)

(*lemma \<And>x y. \<forall>y. Ind(y) \<longrightarrow> x \<in> y \<Longrightarrow>
           Ind(y) \<Longrightarrow> succ(x) \<in> y*)
*)



---------------------

(*  apply (rule ex1_equalsE)
    apply assumption 
  apply (rule equalityI)
   prefer 2
proof -
  have "⋀x. ∃!w. P(w) ⟹ P(x) ⟹ The(P) ⊆ x"
    apply (rule subsetI)
    apply (unfold the_def)
    apply(erule UnionE)
   apply(erule ReplaceE)
    
    
    apply(rule mp)
apply(rule spec)

  qed*)

(*  apply (unfold the_def)
  apply(rule UnionI)
   apply(rule ReplaceI)
     apply (rule exE)
      apply (rule ex1ex)
      apply assumption
  oops*)

