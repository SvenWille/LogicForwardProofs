theory Ex042
  imports Main 
begin 
  
  
theorem ProofByContradiction: "(\<not>A \<longrightarrow> False) \<longrightarrow> A" 
proof -
  {
    assume "(\<not>A \<longrightarrow> False)"
    {
      assume "\<not>A"
      with \<open>\<not>A \<longrightarrow> False\<close> have False by (rule mp)
      hence A by (rule FalseE)
    }
    hence "A" by (rule classical)
  }
  thus ?thesis by (rule impI)
qed
