theory Ex040 
  imports Main
begin 
  
lemma "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" 
proof - 
  {
    assume "\<not>((A \<longrightarrow> B) \<or> (B \<longrightarrow> A))"
    {
      assume "\<not>(A \<longrightarrow> B)"
      {
        assume B 
        {
          assume A 
          from \<open>B\<close> have B by assumption
        }
        hence "A \<longrightarrow> B" by (rule impI)
        with \<open>\<not>(A \<longrightarrow> B)\<close> have False by contradiction
        hence A by (rule FalseE)
      }
      hence "B \<longrightarrow> A" by (rule impI)
      hence "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" by (rule disjI2)
      with \<open>\<not>((A \<longrightarrow> B) \<or> (B \<longrightarrow> A))\<close> have False by contradiction
    }
    hence "\<not>\<not>(A \<longrightarrow> B)" by (rule notI)
    hence "A \<longrightarrow> B" by (rule notnotD)
    hence "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" by (rule disjI1)
    with \<open>\<not>((A \<longrightarrow> B) \<or> (B \<longrightarrow> A))\<close> have False by contradiction
  }
  hence "\<not>\<not>((A \<longrightarrow> B) \<or> (B \<longrightarrow> A))" by (rule notI)
  thus "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" by (rule notnotD)
qed
  
      
        
        
      