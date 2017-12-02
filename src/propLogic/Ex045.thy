theory Ex045
  imports Main 
begin 
  
theorem "C \<longrightarrow> \<not>A \<or> ((B \<or> C) \<longrightarrow> A)" 
proof - 
  {

    assume C
    {
      assume "\<not>(\<not>A \<or> ((B \<or> C) \<longrightarrow> A))" 
      {
        assume A 
        {
          assume "B \<or> C"
          from \<open>A\<close> have A by assumption
        }
        hence "(B \<or> C) \<longrightarrow> A" by (rule impI)
        hence "\<not>A \<or> ((B \<or> C) \<longrightarrow> A)" by (rule disjI2)
        with \<open>\<not>(\<not>A \<or> ((B \<or> C) \<longrightarrow> A))\<close> have False by (rule notE)
      }
      hence "\<not>A" by (rule notI)
      hence "\<not>A \<or> ((B \<or> C) \<longrightarrow> A)" by (rule disjI1)
      with \<open>\<not>(\<not>A \<or> ((B \<or> C) \<longrightarrow> A))\<close> have False by contradiction
    }
    hence "\<not>\<not>(\<not>A \<or> ((B \<or> C) \<longrightarrow> A))" by (rule notI)
    hence "\<not>A \<or> ((B \<or> C) \<longrightarrow> A)" by (rule notnotD)
  }
  thus ?thesis by (rule impI)
qed

      