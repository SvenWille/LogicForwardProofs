theory Ex022 
  imports Main 
begin 
  
lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)" 
proof -
  {
    assume "A \<longrightarrow> B"
    {
      assume "A \<longrightarrow> B \<longrightarrow> C"
      {
        assume A 
        with \<open>A \<longrightarrow> B\<close> have B by (rule mp)
        from \<open>A \<longrightarrow> B \<longrightarrow> C\<close> and \<open>A\<close> have "B \<longrightarrow> C" by (rule mp)
        from \<open>B \<longrightarrow> C\<close> and \<open>B\<close> have C by (rule mp)
      }
      hence "A \<longrightarrow> C" by (rule impI)
    }
    hence "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
        
      
    