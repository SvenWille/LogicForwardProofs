theory Ex022 
  imports Main 
begin 
  
lemma "\<not>A \<longrightarrow> A \<longrightarrow> B" 
proof -
  {
    assume a:"\<not>A"
    {
      assume b:A
      with a have B by contradiction
    }
    hence "A \<longrightarrow> B" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
        
      
    