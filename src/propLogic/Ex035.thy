theory Ex035
  imports Main 
begin 
  
  
lemma "A \<longrightarrow> True" 
proof -
  {
    assume A 
    have True by (rule TrueI)
  }
  thus ?thesis by (rule impI)
qed
  
  
  