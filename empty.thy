theory empty imports Pure
keywords "mytypedecl" :: thy_decl
begin

(*
ML \<open>\<^assert> (not (can ML \<open>open RunCall\<close>))\<close>
ML_file \<open>~~/src/Tools/misc_legacy.ML\<close>
ML_file \<open>~~/src/Provers/splitter.ML\<close>
ML_file \<open>~~/src/Provers/hypsubst.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/zipper.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/isand.ML\<close>
ML_file \<open>~~/src/Tools/IsaPlanner/rw_inst.ML\<close>
ML_file \<open>~~/src/Provers/quantifier1.ML\<close>
ML_file \<open>~~/src/Tools/intuitionistic.ML\<close>
ML_file \<open>~~/src/Tools/project_rule.ML\<close>
ML_file \<open>~~/src/Tools/atomize_elim.ML\<close>
*)

subsection \<open>FOL: Language, axioms and rules\<close>
ML\<open>Typedecl.typedecl {final=true}\<close>
ML\<open>val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>mytypedecl\<close> "my type declaration"
    (Parse.type_args -- Parse.binding -- Parse.opt_mixfix
      >> (fn ((args, a), mx) =>
          Typedecl.typedecl {final = true} (a, map (rpair dummyS) args, mx) #> snd));
\<close>

mytypedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>  (\<open>(_)\<close> 5)

class "term"
default_sort \<open>term\<close>

axiomatization
  False :: \<open>o\<close> and
  conj :: \<open>[o, o] => o\<close>  (infixr \<open>\<and>\<close> 35) and
  disj :: \<open>[o, o] => o\<close>  (infixr \<open>\<or>\<close> 30) and
  imp :: \<open>[o, o] => o\<close>  (infixr \<open>\<longrightarrow>\<close> 25)

definition Not (\<open>\<not> _\<close> [40] 40)
  where not_def: \<open>\<not> P \<equiv> P \<longrightarrow> False\<close>

axiomatization where
  ax1 : \<open>A\<longrightarrow>(B\<longrightarrow>A)\<close> and
  ax2 : \<open>(A\<longrightarrow>(B\<longrightarrow>C))\<longrightarrow>((A\<longrightarrow>B)\<longrightarrow>(A\<longrightarrow>C))\<close> and
  ax3 : \<open>(A\<and>B)\<longrightarrow>A\<close> and
  ax4 : \<open>(A\<and>B)\<longrightarrow>B\<close> and
  ax5 : \<open>A\<longrightarrow>(B\<longrightarrow>(A\<and>B))\<close> and
  ax6 : \<open>A\<longrightarrow>(A\<or>B)\<close> and
  ax7 : \<open>B\<longrightarrow>(A\<or>B)\<close> and
  ax8 : \<open>(A\<longrightarrow>C)\<longrightarrow>(B\<longrightarrow>C)\<longrightarrow>(A\<or>B\<longrightarrow>C)\<close> and
  ax9 : "(A\<longrightarrow>B)\<longrightarrow>(A\<longrightarrow>\<not>B)\<longrightarrow>\<not>A" and
  ax10: "A\<longrightarrow>\<not>A\<longrightarrow>B" and
  ax11: "A\<or>\<not>A"

axiomatization
  All :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>\<forall>\<close> 10) and
  Ex :: \<open>('a \<Rightarrow> o) \<Rightarrow> o\<close>  (binder \<open>\<exists>\<close> 10)
where
  ax12: \<open>(\<forall>x. A(x)) \<longrightarrow> A(q)\<close> and
  ax13: \<open>A(q) \<longrightarrow> (\<exists>x. A(x))\<close> and
(*axB1: \<open>(\<forall>x. (R \<longrightarrow> S(x))) \<longrightarrow> (R \<longrightarrow> (\<forall>x. S(x)))\<close> and
  axB2: \<open>(\<forall>x. (S(x) \<longrightarrow> R)) \<longrightarrow> ((\<exists>x. S(x)) \<longrightarrow> R)\<close>
  gen: \<open>(\<And>x. P(x)) \<Longrightarrow> (\<forall>x. P(x))\<close> *)
  rB1: \<open>(\<And>x. (R \<longrightarrow> S(x))) \<Longrightarrow> (R \<longrightarrow> (\<forall>x. S(x)))\<close> and
  rB2: \<open>(\<And>x. (S(x) \<longrightarrow> R)) \<Longrightarrow> ((\<exists>x. S(x)) \<longrightarrow> R)\<close>

axiomatization where
  mp  : \<open>\<lbrakk>P \<longrightarrow> Q; P\<rbrakk> \<Longrightarrow> Q\<close>

subsubsection \<open>Admissible rules\<close>

axiomatization where
 ded: \<open>(P \<Longrightarrow> Q) \<Longrightarrow> P \<longrightarrow> Q\<close>

subsection \<open>FOL Theorems\<close>

lemma atoa: \<open>A\<longrightarrow>A\<close>
  apply (rule mp)
   apply (rule mp)
  apply (rule ax2)
   apply (rule ax1)
   apply (rule ax1)
  done

definition def_true:\<open>True \<equiv> (False \<longrightarrow> False)\<close>

lemma lemtrue : \<open>True\<close>
  apply(unfold def_true)
  apply(rule atoa)  
  done

lemma gen: \<open>(\<And>x. P(x)) \<Longrightarrow> (\<forall>x. P(x))\<close>
  apply(rule mp)
   apply (rule rB1)
  apply(rule mp)
   apply (rule ax1)
  apply assumption
  apply(rule lemtrue)
  done

lemma spec: \<open>(\<forall>x. P(x)) \<Longrightarrow> P(x)\<close>
  apply(rule mp)
   apply(rule ax12)
   apply assumption
  done

lemma exI: \<open>P(x) \<Longrightarrow> (\<exists>x. P(x))\<close>
  apply(rule mp)
   apply(rule ax13)
   apply assumption
  done

lemma axB1: \<open>(\<forall>x. (R \<longrightarrow> S(x))) \<longrightarrow> (R \<longrightarrow> (\<forall>x. S(x)))\<close>
  apply (rule ded)
  apply (rule ded)
  apply (rule gen)
  apply (rule mp)
  apply (rule spec)
   apply assumption
   apply assumption
  done

lemma axB1': \<open>(\<forall>x. (R \<longrightarrow> S(x))) \<longrightarrow> (R \<longrightarrow> (\<forall>x. S(x)))\<close>
  apply (rule ded)
  apply (rule rB1)
  apply (rule spec)
  apply assumption
  done

lemma axB2: \<open>(\<forall>x. (S(x) \<longrightarrow> R)) \<longrightarrow> ((\<exists>x. S(x)) \<longrightarrow> R)\<close>
  apply (rule ded)
  apply (rule rB2)
  apply (rule spec)
  apply assumption
  done

(*
lemma exE: \<open>\<exists>x. P x \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q \<close>
proof
  assume x:"\<exists>x. P x"
  show "(\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q"
    apply fact
    done
qed*)

context 
  assumes p:"\<exists>x. P x"
  assumes r:"(\<And>x. P x \<Longrightarrow> Q)"
(*  fixes W defines W_def : "W == {x\<in>S. x\<notin>x}"*)
begin
lemma ll : \<open>(\<forall>x. (R(x) \<longrightarrow> Q))\<close>
   apply(rule gen)
   apply(rule ded)
  apply(rule r)
  apply assumption
  done
lemma exE : \<open>Q\<close>
  apply(rule r)

  apply(rule mp)
   apply(rule mp)
  apply(rule axB2)
   apply(rule ll)
   apply(rule p)
  done
(*terrm exE, prop exE*)
end

print_theorems
print_statement exE


subsection \<open>ZFC: Language, axioms and rules\<close>

declare [[eta_contract = false]] (* what for? *)
typedecl i
instance i :: "term" ..

axiomatization mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<in>\<close> 50)  \<comment> \<open>membership relation\<close>
  and zero :: "i"  (\<open>0\<close>)  \<comment> \<open>the empty set\<close>
  and Pow :: "i \<Rightarrow> i"  \<comment> \<open>power sets\<close>
  and Inf :: "i"  \<comment> \<open>infinite set\<close>
  and Union :: "i \<Rightarrow> i"  (\<open>\<Union>_\<close> [90] 90)
  and PrimReplace :: "[i, [i, i] \<Rightarrow> o] \<Rightarrow> i"

abbreviation not_mem :: "[i, i] \<Rightarrow> o"  (infixl \<open>\<notin>\<close> 50)  \<comment> \<open>negated membership relation\<close>
  where "x \<notin> y \<equiv> \<not> (x \<in> y)"

(* Why?
subsection \<open>Bounded Quantifiers\<close>

definition Ball :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Ball(A, P) \<equiv> \<forall>x. x\<in>A \<longrightarrow> P(x)"

definition Bex :: "[i, i \<Rightarrow> o] \<Rightarrow> o"
  where "Bex(A, P) \<equiv> \<exists>x. x\<in>A \<and> P(x)"

syntax
  "_Ball" :: "[pttrn, i, o] \<Rightarrow> o"  (\<open>(3\<forall>_\<in>_./ _)\<close> 10)
  "_Bex" :: "[pttrn, i, o] \<Rightarrow> o"  (\<open>(3\<exists>_\<in>_./ _)\<close> 10)
translations
  "\<forall>x\<in>A. P" \<rightleftharpoons> "CONST Ball(A, \<lambda>x. P)"
  "\<exists>x\<in>A. P" \<rightleftharpoons> "CONST Bex(A, \<lambda>x. P)"
*)

end