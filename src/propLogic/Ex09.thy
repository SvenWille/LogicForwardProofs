theory Ex09
imports Main 
begin 



lemma " \<not>C \<longrightarrow> A \<or> ((A \<or> C) \<longrightarrow> B)"
proof - 
{
  assume "\<not>C"
  {
    assume "\<not>(A \<or> ((A \<or> C) \<longrightarrow> B))"
    {
      assume "A \<or> C"
      {
        assume A
        hence "A \<or> ((A \<or> C) \<longrightarrow> B)" by (rule disjI1)
        with \<open>\<not>(A \<or> ((A \<or> C) \<longrightarrow> B))\<close> have False by contradiction
        hence B by (rule FalseE)
      }
      {
        assume C
        with \<open>\<not>C\<close> have False by contradiction
        hence B by (rule FalseE)
      }
      with \<open>A \<or> C\<close>  and  \<open>A \<Longrightarrow> B\<close> have B by (rule disjE)
    }
    hence "A \<or> C \<longrightarrow> B" by (rule impI)
    hence "A \<or> (A \<or> C \<longrightarrow> B)" by (rule disjI2)
    with \<open>\<not>(A \<or> ((A \<or> C) \<longrightarrow> B))\<close> have False by contradiction
  }
  hence "\<not>\<not>(A \<or> ((A \<or> C) \<longrightarrow> B))" by (rule notI)
  hence "A \<or> ((A \<or> C) \<longrightarrow> B)" by (rule notnotD)
}
thus ?thesis by (rule impI)
qed

