theory Ex026 
  imports Main 
begin 
  
  
lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longleftrightarrow> (B \<longrightarrow> (A \<longrightarrow> C))" 
proof -
  {
    assume a:"A \<longrightarrow> (B \<longrightarrow> C)"
    {
      assume b:B
      {
        assume A 
        with a have "B \<longrightarrow> C" by (rule mp)
        from this and b have C by (rule mp)
      }
      hence "A \<longrightarrow> C" by (rule impI)
    }
    hence " B \<longrightarrow> (A \<longrightarrow> C)" by (rule impI)
  }
  moreover
  {
    assume c:"B \<longrightarrow> (A \<longrightarrow> C)" 
    {
      assume d:A 
      {
        assume B 
        with c have  "A \<longrightarrow> C" by (rule mp)
        from this and d have C by (rule mp)
      }
      hence "B \<longrightarrow> C" by (rule impI)
    }
    hence "A \<longrightarrow> (B \<longrightarrow> C)" by (rule impI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
        
  