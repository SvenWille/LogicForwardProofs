theory Ex037
  imports Main 
begin 
  
lemma "\<lbrakk>A \<or> B ; \<not>A \<or> \<not>C\<rbrakk> \<Longrightarrow> C \<longrightarrow> B"
proof - 
  {
    assume "A \<or> B"
    {
      assume "\<not>A \<or> \<not>C" 
      {
        assume "\<not>A"  
        {
          assume A 
          with \<open>\<not>A\<close> have False by contradiction
          hence "C \<longrightarrow> B" by (rule FalseE)     
        }
        note tmp=this 
        {
          assume B 
          {
            assume C
            from \<open>B\<close> have B by assumption
          }
          hence "C \<longrightarrow> B" by (rule impI)
        }
        from \<open>A \<or> B\<close> and tmp and this have "C \<longrightarrow> B" by (rule disjE)
      }
      note tmp=this
      {
        assume "\<not>C"
        {
          assume C 
          with \<open>\<not>C\<close> have False by contradiction
          hence B by (rule FalseE)
        }
        hence "C \<longrightarrow> B" by (rule impI)
      }
      with \<open>\<not>A \<or> \<not>C\<close> and tmp show "C \<longrightarrow> B" by (rule disjE)
    }
  }
qed
  
      
      
          
          
              
              
  