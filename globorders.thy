theory globorders imports ZF (* why not FOL? *)
begin

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