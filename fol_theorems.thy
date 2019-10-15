theory fol_theorems imports FOL
begin

axiomatization
  where aax8  : \<open>(A-->C)-->(B-->C)-->(A\<or>B-->C)\<close>
    and aax11 : "A\<or>~A"

lemma ewfw : \<open>\<lbrakk>(A\<longrightarrow>B);\<not>A\<longrightarrow>B\<rbrakk>\<Longrightarrow>B\<close>
  apply(rule mp)
   apply(rule mp)
  apply(rule mp)
     apply(rule aax8)
  apply assumption
   prefer 2
  
  apply(rule impI)

  ???
  done

end