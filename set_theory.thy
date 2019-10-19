theory set_theory imports ZFC classical_axioms fol_theorems
begin

(* New words:
cut_tac; with; (best dest: equalityD2);
*)


context
  fixes S
  fixes W defines W_def : "W == {x\<in>S. x\<notin>x}"
begin

lemma WinW :
  assumes y:\<open>W \<in> W\<close> 
  shows \<open>False\<close>
proof (rule notE[where P="W\<in>W"])
  from y have \<open>W \<in> {x \<in> S . x \<notin> x}\<close> by (unfold W_def)
  then show \<open>W \<notin> W\<close> by (rule CollectD2[where A=S])
next
  show \<open>W \<in> W\<close> by (rule y)
qed

lemma ex_1_2 : "\<not> ( Pow(S) \<subseteq> S )"
  apply (rule notI)
  apply (rule case_split[where P="W\<in>W"])
  apply (rule notE[where P="W\<in>W"])
    apply (rule CollectD2[where A=S])
    apply (fold W_def)
    apply assumption
   apply assumption
  apply (rule notE[where P="W\<in>W"])
   apply assumption
  apply (unfold W_def)
   apply (rule CollectI)
   apply (fold W_def)
   prefer 2
  apply assumption
  (*subgoal*)
   apply (unfold subset_def)
   apply (unfold Ball_def)
    apply (rule mp[where P="W\<in>Pow(S)"])
     apply (erule spec[where x=W])
    apply (rule PowI)
    apply (unfold W_def)
    apply (unfold subset_def)
    apply (unfold Ball_def)
    apply (rule allI)
    apply (rule impI)
    apply (erule CollectD1)
  done

lemma ex_1_2' : \<open>\<not> ( Pow(S) \<subseteq> S )\<close>
proof (rule notI)
  assume j:\<open>Pow(S) \<subseteq> S\<close>
  show \<open>False\<close>
  proof (rule case_split[where P="W\<in>W"])
    show \<open>W \<in> W \<Longrightarrow> False\<close> by (rule WinW)
  next
    assume y:\<open>W \<notin> W\<close>
    show \<open>False\<close>
    proof (rule notE[where P="W\<in>W"])
      show \<open>W \<notin> W\<close> by (rule y)(*assumption*)
    next
      show \<open>W \<in> W\<close>
      proof (unfold W_def)          
        show \<open>{x \<in> S . x \<notin> x} \<in> {x \<in> S . x \<notin> x}\<close>
        proof (rule CollectI)
          from \<open>W \<notin> W\<close>
          show \<open>{x \<in> S . x \<notin> x} \<notin> {x \<in> S . x \<notin> x}\<close> by (fold W_def)
        next
          have b0:\<open>\<forall>x. x \<in> Pow(S) \<longrightarrow> x \<in> S \<Longrightarrow> W \<in> Pow(S)\<close>
            apply (rule PowI)
            apply (unfold W_def)
            apply (unfold subset_def)
            apply (unfold Ball_def)
            apply (rule allI)
            apply (rule impI)
            apply (erule CollectD1)
            done
          from j have i:\<open>\<forall>x. x \<in> Pow(S) \<longrightarrow> x \<in> S\<close>
            apply (unfold subset_def)
            apply (unfold Ball_def)
            apply assumption
            done
          from j have \<open>W \<in> S\<close>
            apply (unfold subset_def)
            apply (unfold Ball_def)
            apply (rule mp[where P="W\<in>Pow(S)"])
             apply (erule spec[where x=W])
            apply (erule b0)
            done
          then show \<open>{x \<in> S . x \<notin> x} \<in> S\<close> by (fold W_def)
        qed
      qed
    qed
  qed
qed

(*          next
       prefer 2
       apply (rule y)(*assumption*)
          show \<open>W \<notin> W\<close> by (rule y)

        next
*)

      (*apply (unfold W_def)*)

  (*subgoal*)
(*      have \<open>W \<notin> W \<Longrightarrow> W \<in> S\<close>*)

theorem Drinker's_Principle: "\<exists>x. drunk(x) \<longrightarrow> (\<forall>x. drunk(x))"
proof cases
  assume "\<forall>x. drunk(x)"
  then have "drunk(a) \<longrightarrow> (\<forall>x. drunk(x))" for a ..
  then show ?thesis ..
next
  assume "\<not> (\<forall>x. drunk(x))"
  then have "\<exists>x. \<not> drunk(x)" by (rule de_Morgan)
  then obtain a where "\<not> drunk(a)" ..
  have "drunk(a) \<longrightarrow> (\<forall>x. drunk(x))"
  proof
    assume "drunk(a)"
    with \<open>\<not> drunk(a)\<close> show "\<forall>x. drunk(x)" by contradiction
  qed
  then show ?thesis ..
qed

end

lemma l3: \<open>S \<subseteq> {b . a \<in> S, a = b}\<close>
  apply(rule subsetI)
  apply(rule ReplaceI)
  (*apply(rule iffD2)
  (* apply(unfold Replace_def)
   apply(rule replacement) *)
   apply(rule Replace_iff)*
  apply(unfold Bex_def)
  (* How to specify metavariable with bounded variable?
     apply(rule exI[where x=x])  [of _ x]*)
  apply(rule exI)
  apply(erule conjI)
  (* How to instantiate ?x8(x):=x  ? *)
  apply(rule conjI) (* = split.*)*)
    apply(rule refl)
   apply assumption
  apply(erule sym)
  done

lemma l3': \<open>S \<subseteq> {b . a \<in> S, a = b}\<close>
proof (rule subsetI)
  fix x
  assume p2:\<open>x \<in> S\<close>
  have p1:"x=x" by (rule refl)
  have p3:"\<And>b. x=b \<Longrightarrow> b=x" by (rule sym)
  from p1 and p2 and p3 show \<open>x \<in> {b . a \<in> S, a = b}\<close> by (rule ReplaceI)
qed

(* original theorem has no name, so I had to prove it... *)
lemma l4_1:  \<open>P \<longleftrightarrow> P \<and> True\<close>
  apply auto
  done


lemma l4: \<open>S = {a \<in> S. True}\<close>
  (* apply(rule iffD2)
  apply(rule extension)
  apply(rule conjI) *)
  apply(rule equalityI)
  apply(unfold Collect_def)
   apply(rule subst)
    apply(rule Replace_cong)
     apply(rule refl)
(* how to forget assumption? *)
    apply(rule l4_1)
  apply(rule l3)
  apply(fold Collect_def)
  apply(rule Collect_subset)
  done

definition Ind :: "i\<Rightarrow>o"
  where Ind_def : "Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)"

lemma IndInf : "Ind(Inf)"
  apply(unfold Ind_def, rule infinity)
  done

lemma ex1_3:
  fixes x
  assumes a:"Ind(x)"
  shows "Ind({y\<in>x. y\<subseteq>x})"
proof -
  from a
  have "0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)" by (unfold Ind_def)
  hence c1:"0 \<in> x" and c2:"(\<forall>y\<in>x. succ(y) \<in> x)" by (rule conjunct1, rule conjunct2)
  from c1 have d:"0 \<in> {y \<in> x . y \<subseteq> x}"
    apply(rule CollectI)
    apply(rule empty_subsetI)
    done
  from c1 and c2
  have e:"(\<forall>y\<in>{y \<in> x . y \<subseteq> x}. succ(y) \<in> {y \<in> x . y \<subseteq> x})"
    apply(unfold Ball_def)
  proof(rule allI, rule impI)
    fix k::"i"
    assume f: "0 \<in> x"
     and g:\<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
     and h:\<open>k \<in> {y \<in> x . y \<subseteq> x}\<close>
    show i:"succ(k) \<in> {y \<in> x . y \<subseteq> x}"
    proof -
      from h
      have h1:"k \<in> x" and h2:"k\<subseteq>x"
        apply(rule CollectD1[where A="x"])
        apply(rule CollectD2[where P="\<lambda>w. w\<subseteq>x"])
        apply(rule h)
        done
      from h1 and h2
      show ik:"succ(k) \<in> {y \<in> x . y \<subseteq> x}"
        apply(unfold succ_def)
        apply(fold succ_def)
        apply(rule CollectI[where P="\<lambda>y. y\<subseteq>x"])
         apply(rule mp)
          apply(rule spec[where x="k"])
          apply(rule g)
         apply assumption
        apply(rule subsetI)
      proof -
        fix m::i
        assume ff: "k \<in> x"
        and gg: "k \<subseteq> x"
        and hh: \<open>m \<in> succ(k)\<close>
        show ii:"m \<in> x"
        proof -
          from hh
          have "m \<in> cons(k, k)" by (unfold succ_def)
          hence "m \<in> Upair(k,k) \<union> k" by (unfold cons_def)
          hence hh: "m \<in> Upair(k,k) \<or> m \<in> k"
            apply (unfold Un_def)
            apply (erule UnionE)
            apply (erule UpairE)
             apply(rule disjI1)
             apply(erule subst)
             apply assumption
             apply(rule disjI2)
             apply(erule subst)
            apply assumption
            done
          from ff and gg and hh show "m \<in> x"
          proof -
            show ghj:"k \<in> x \<Longrightarrow> k \<subseteq> x \<Longrightarrow> m \<in> Upair(k, k) \<or> m \<in> k \<Longrightarrow> m \<in> x"
              apply(erule disjE)
               apply (erule UpairE)
              apply(erule subst_elem)
                 apply assumption
               apply(erule subst_elem)
                apply assumption
              apply(erule subsetD)
              apply assumption
              done
          qed
        qed
      qed
    qed
  qed
  show "Ind({y \<in> x . y \<subseteq> x})"
    apply(unfold Ind_def)
    apply(rule conjI)
     apply(rule d)
    apply(rule e)
    done
qed

definition ClassInter :: \<open>(i\<Rightarrow>o)\<Rightarrow>(i\<Rightarrow>o)\<close> (*\<open>[ i \<Rightarrow> o, i ] \<Rightarrow> o\<close>*)
  where ClassInter_def : "ClassInter(P,x) == \<forall>y. P(y) \<longrightarrow> x\<in>y"

definition Nat :: \<open>i\<Rightarrow>o\<close>
  where "Nat == ClassInter(Ind)"

(*lemma IndInf : "Ind(Inf)"
  apply(unfold Ind_def, rule infinity)
  done*)

lemma lwe : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
  apply(unfold Nat_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold ClassInter_def)
  apply(rule mp)
   apply(erule spec)
  apply(rule IndInf)
  done

definition IsTransClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsTransClass_def : "IsTransClass(P) == \<forall>y. P(y) \<longrightarrow> (\<forall>z. z\<in>y \<longrightarrow> P(z))"

definition IsIndClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsIndClass_def : "IsIndClass(P) == P(0) \<and> (\<forall>y. P(y) \<longrightarrow> P(succ(y)))"

definition IsSet :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsSet_def : "IsSet(P) == \<exists> y. \<forall> z. z \<in> y \<longleftrightarrow> P(z)"

lemma Nat0 : "Nat(0)"
  apply(unfold Nat_def)
  apply(unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold Ind_def)
  apply(erule conjE)
  apply assumption
  done

lemma Nat0' : "Nat(0)"
proof (unfold Nat_def) show \<open>ClassInter(Ind, 0)\<close>
  proof (unfold ClassInter_def) show \<open>\<forall>y. Ind(y) \<longrightarrow> 0 \<in> y\<close>
    proof (rule allI) show \<open>\<And>y. Ind(y) \<longrightarrow> 0 \<in> y\<close>
      proof (rule impI) show \<open>\<And>y. Ind(y) \<Longrightarrow> 0 \<in> y\<close>
        proof (unfold Ind_def) show \<open>\<And>y. 0 \<in> y \<and> (\<forall>ya\<in>y. succ(ya) \<in> y) \<Longrightarrow> 0 \<in> y\<close>
          proof (erule conjE) show
                 \<open>\<And>y. 0 \<in> y \<Longrightarrow>
                  \<forall>ya\<in>y. succ(ya) \<in> y \<Longrightarrow>
                  0 \<in> y\<close>
              by assumption
          qed
        qed
      qed
    qed
  qed
qed

lemma zeroisempty : \<open>\<forall>x. \<not> x \<in> 0\<close>
  apply(rule allI)
  apply(rule not_mem_empty)
  done

lemma NatSu:
  fixes x w
  assumes a:"\<forall>y. Ind(y) \<longrightarrow> x \<in> y"
  assumes b:"Ind(w)"
  shows "succ(x) \<in> w"
proof -
  from b
  have b': "\<forall>y. y\<in>w \<longrightarrow> succ(y) \<in> w"
    apply(unfold Ind_def)
    apply(rule allI)
    apply(rule impI)
    apply(rule  bspec[where P="%y. succ(y) \<in> w"])
     apply(erule conjunct2)
    apply(assumption)
    done
  from a b' b
  show c': "succ(x) \<in> w"
    apply(unfold Ind_def)
    apply(rule mp)
     apply(erule spec)
    apply(fold Ind_def)
    apply(rule mp)
     apply(erule spec)
    apply(unfold Ind_def)

    apply(rule conjI)
    prefer 2
     apply(rule ballI)
     apply(rule mp)
      apply(erule spec)
     apply(assumption)
    apply(erule conjunct1)
    done
qed

lemma NatSucc : "\<forall> x. Nat(x) \<longrightarrow> Nat(succ(x))"
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply(rule allI)
  apply(rule impI)
  apply(erule NatSu)
  apply assumption
  done

lemma NatIsInd : \<open>IsIndClass(Nat)\<close>
  apply (unfold IsIndClass_def)
  apply (rule conjI)
   apply (rule Nat0)
  apply (rule NatSucc)
  done

lemma uio : \<open>IsTransClass(Nat)\<close>
  apply (unfold IsTransClass_def)
  apply(rule allI)
  apply(rule impI)
  apply(rule allI)
  apply(rule impI)
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply (unfold Ind_def)
  oops

lemma ex1ex : "(\<exists>!x. P(x)) \<Longrightarrow> (\<exists>x. P(x))"
  apply (erule ex1E)
  apply (erule exI)
  done

lemma TheE : "\<And>x. (\<exists>!w. P(w)) \<Longrightarrow> P(x) \<Longrightarrow> x=The(P)"
  apply (rule sym)
  apply (erule upair.the_equality2)
  apply assumption
  done

(* "is a superset of the natural numbers" predicate *)
definition SuperNatNumb :: \<open>(i\<Rightarrow>o)\<close>
  where SuperNatNumb_def : "SuperNatNumb(x) == \<forall> y. Nat(y) \<longrightarrow> y\<in>x"

lemma NatInInf: "\<And>x. Nat(x) \<Longrightarrow> x \<in> Inf"
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule mp)
   apply(erule spec)
  apply (rule IndInf)
  done

lemma SuperNatNumbInf : "SuperNatNumb(Inf)"
  apply (unfold SuperNatNumb_def)
  apply(rule allI)
  apply(rule impI)
  apply(erule NatInInf)
  done

definition Omega :: \<open>i\<close>
  where Omega_def : "Omega == { y \<in> Inf . Nat(y) }"

lemma NatSubOmega : "\<And>x. Nat(x) \<Longrightarrow> x \<in> Omega"
  apply (unfold Omega_def)
  apply (rule CollectI)
   apply (erule NatInInf)
  apply assumption
  done

lemma ExInf : \<open>\<exists>x. Ind(x)\<close>
  apply(rule exI)
  apply(rule IndInf)
  done

lemma IndOmega : \<open>Ind(Omega)\<close>
  sorry

(* Some facts are about logic, not about ordered pairs.
Some are about relations which are set. 
It would be good to separate these cases.*)
definition ReflRel :: \<open>(i=>i=>o)=>o\<close>
  where ReflRel_def : "ReflRel(P) == \<forall>x. P(x,x)"
definition SymRel :: \<open>(i=>i=>o)=>o\<close>
  where SymRel_def : "SymRel(P) == \<forall>x. \<forall>y. P(x,y) \<longrightarrow> P(y,x)"
definition TransRel :: \<open>(i=>i=>o)=>o\<close>
  where TransRel_def : "TransRel(P) ==
 \<forall>x y z. P(x,y) \<and> P(y, z) \<longrightarrow> P(x,z)"

definition uncarry :: \<open>(i=>i=>o)=>(i=>o)\<close>
  where uncarry_def : "uncarry(P,p) == P(fst(p),snd(p))"
definition carry :: \<open>(i\<Rightarrow>o) \<Rightarrow> (i\<Rightarrow>i\<Rightarrow>o)\<close>
  where carry_def : "carry(P,x,y) == P(<x,y>)"


definition Pres :: \<open>(i\<Rightarrow>i\<Rightarrow>o) \<Rightarrow>(i\<Rightarrow>i\<Rightarrow>o) \<Rightarrow>(i\<Rightarrow>i) \<Rightarrow> o\<close>
  where "Pres(A,B,f) == \<forall>a0 a1. A(a0,a1)\<longrightarrow>B(f(a0),f(a1))"

definition tofun :: \<open>i \<Rightarrow> (i\<Rightarrow>i)\<close>
  where "tofun(f,x) == f`x"


(* transitive closure*)
(*
definition TrCl :: \<open>(i\<Rightarrow>i\<Rightarrow>o) \<Rightarrow> (i\<Rightarrow>i\<Rightarrow>o)\<close>
  where "TrCl(P,a,b) ==
 \<exists>\<alpha>. Ord(\<alpha>) \<and> (\<exists>f. fun(f) & dom(f) = \<alpha> & Pres(mem,P, \<lambda>x. f`x))"
*)
(* todo: translate statement from HOL to ZF *)
(* every proper initial segment of ordinals is a set *)

(* There exists subset-minimal inductive set. *)

definition Irr :: \<open>(i=>i=>o)=>o\<close>
  where Irr_def : "Irr(P) == \<forall>x. \<not>P(x,x)"

definition AntiSym :: \<open>(i=>i=>o)=>o\<close>
  where AntiSym_def : "AntiSym(P) == \<forall>x. \<forall>y. P(x,y) \<and> P(y,x) \<longrightarrow> x=y"

definition SPO :: \<open>(i=>i=>o)=>o\<close>
  where SPO_def : "SPO(R) == Irr(R)\<and>AntiSym(R)\<and>TransRel(R)"

(* partial order *)
definition PO :: \<open>(i=>i=>o)=>o\<close>
  where PO_def : "PO(R) == ReflRel(R)\<and>AntiSym(R)\<and>TransRel(R)"

(* equivalence relation *)
definition ER :: \<open>(i=>i=>o)=>o\<close>
  where ER_def : "ER(R) == ReflRel(R)\<and>SymRel(R)\<and>TransRel(R)"

definition IsWeakMin :: \<open>(i=>i=>o)=>i\<Rightarrow>o\<close>
  where IsWeakMin_def : "IsWeakMin(R,x) == \<forall>y. (R(x,y) \<or> x=y)"

definition IsMin :: \<open>(i=>i=>o)=>i\<Rightarrow>o\<close>
  where IsMin_def : "IsMin(R,x) == \<forall>y. R(x,y)"

lemma WeakMinIsOnlyOne : \<open>AntiSym(R) \<Longrightarrow> \<exists>x. IsWeakMin(R,x) \<Longrightarrow> \<exists>!x. IsWeakMin(R,x)\<close>
  apply(erule ex_ex1I)
  apply(unfold IsWeakMin_def)

  apply(rule disjE)
   apply(erule spec)
  prefer 2 apply assumption

  apply(rule sym)
  apply(rule disjE) (*[where Q="y=x"]*)
    apply(rule spec)
    prefer 3    apply assumption
   apply assumption
  apply(fold IsWeakMin_def)

  apply(unfold AntiSym_def)
  apply(rule mp)
   apply(rule spec)
   apply(rule spec)
   apply assumption
  apply(rule conjI)
   apply assumption
  apply assumption
  done

lemma MinIsOnlyOne : \<open>AntiSym(R) \<Longrightarrow> \<exists>x. IsMin(R,x) \<Longrightarrow> \<exists>!x. IsMin(R,x)\<close>
  apply(erule ex_ex1I)
  apply(unfold IsMin_def)
  apply(unfold AntiSym_def)
  apply(rule mp)
   apply(rule spec)
   apply(rule spec)
   apply assumption
  apply(rule conjI)
  apply(erule spec)
  apply(erule spec)
  done

(*lemma IndPO*)

lemma ExMinInd : \<open>\<exists>!x. ( Ind(x) \<and> (\<forall>y. Ind(y) \<longrightarrow> x\<subseteq>y) )\<close>
  apply(rule ex_ex1I)
   apply(rule exI)
   apply(rule conjI)
    apply(rule IndOmega)
  sorry

(*If there exists two subset-minimal sets  the they are equal.*)


lemma NatI : "\<And>x. Nat(x) \<Longrightarrow> x\<in>The(SuperNatNumb)"
  apply (unfold the_def)
  apply(rule UnionI)
   apply(rule ReplaceI)
  prefer 4
(*     apply(erule NatInInf) wrong!
    apply(rule SuperNatNumbInf)

     apply assumption *)
  oops


lemma NatIsInd2: "omega = nat"
  oops


lemma de_Morgan:
  assumes "\<not> (\<forall>x. P(x))"
  shows "\<exists>x. \<not> P(x)"
proof (rule classical)
  assume "\<not> (\<exists>x. \<not> P(x))"
  have "\<forall>x. P(x)"
  proof
    fix x show "P(x)"
    proof (rule classical)
      assume "\<not> P(x)"
      then have "\<exists>x. \<not> P(x)" ..
      with \<open>\<not>(\<exists>x. \<not> P(x))\<close> show ?thesis by contradiction
    qed
  qed
  with \<open>\<not> (\<forall>x. P(x))\<close> show ?thesis by contradiction
qed

theorem Drinker's_Principle: "\<exists>x. drunk(x) \<longrightarrow> (\<forall>x. drunk(x))"
proof cases
  assume "\<forall>x. drunk(x)"
  then have "drunk(a) \<longrightarrow> (\<forall>x. drunk(x))" for a ..
  then show ?thesis ..
next
  assume "\<not> (\<forall>x. drunk(x))"
  then have "\<exists>x. \<not> drunk(x)" by (rule de_Morgan)
  then obtain a where "\<not> drunk(a)" ..
  have "drunk(a) \<longrightarrow> (\<forall>x. drunk(x))"
  proof
    assume "drunk(a)"
    with \<open>\<not> drunk(a)\<close> show "\<forall>x. drunk(x)" by contradiction
  qed
  then show ?thesis ..
qed

lemma lwe2 : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
  apply(unfold Nat_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold ClassInter_def)
  apply(rule mp)
   apply(erule spec)
  apply(rule IndInf)
  done

lemma lwe3 : \<open>\<And>x. Nat(x) \<Longrightarrow> x\<in>Inf\<close>
proof (unfold Nat_def)
  fix x
  assume p0:\<open>ClassInter(Ind, x)\<close>
  show \<open>x\<in>Inf\<close>
  proof -
    from p0 have "\<forall>y. Ind(y) \<longrightarrow> x \<in> y" by (unfold ClassInter_def)
    then have "Ind(Inf) \<longrightarrow> x \<in> Inf" by (rule spec)
    then have p3:"Ind(Inf) \<Longrightarrow> x \<in> Inf" by (rule mp)
    from IndInf show p4:"x \<in> Inf" by (rule p3)
  qed
qed

lemma lwe4 : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
proof (rule allI)
  fix x
  from lwe3 show \<open>(Nat(x) \<longrightarrow> x\<in>Inf)\<close> by (rule impI)
qed

lemma lwe4' : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
proof 
  fix x
  show \<open>(Nat(x) \<longrightarrow> x\<in>Inf)\<close>
  proof
    assume \<open>Nat(x)\<close>
    hence \<open>ClassInter(Ind, x)\<close> by (unfold Nat_def)
    hence \<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close> by (unfold ClassInter_def)
    hence \<open>Ind(Inf) \<longrightarrow> x \<in> Inf\<close> by (rule spec)
    hence p:\<open>Ind(Inf) \<Longrightarrow> x \<in> Inf\<close> by (rule mp)
    from IndInf show \<open>x \<in> Inf\<close> by (rule p)
  qed
qed

(* how to fold something as ... *)
lemma SPO2PO : \<open>SPO(R) \<Longrightarrow> PO(\<lambda>x y.(R(x,y)\<or>x=y))\<close>
(*(*apply(unfold PO_def)
  apply(rule conjI)*)
proof
assume "SPO(R)"
  have qki:"SPO(R) \<Longrightarrow>ReflRel(\<lambda>x y. R(x, y) \<or> x = y)"
  proof
    apply(unfold ReflRel_def)
    apply auto (*  apply (rule allI) *)
    done
  ..
(* next by qki*)
(*  then have "SPO(R) \<Longrightarrow> ReflRel(\<lambda>x y. R(x, y) \<or> x = y)"*)
    apply(unfold ReflRel_def)
(*  with qki show ?thesis
  from qki show "SPO(R) \<Longrightarrow>ReflRel(\<lambda>x y. R(x, y) \<or> x = y"
from qki show "SPO(R) \<Longrightarrow>ReflRel(\<lambda>x y. R(x, y) \<or> x = y)"
    apply(unfold ReflRel)
    by qki
  apply assumption
  qed*)*)
  oops

(* use of LEM *)
lemma PO2SPO : \<open>PO(R) \<Longrightarrow> SPO(\<lambda>x y.(R(x,y)\<and>x\<noteq>y))\<close>
  oops


end
