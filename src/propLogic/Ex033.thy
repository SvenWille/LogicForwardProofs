theory Ex033 
  imports Main 
begin 
  
  
  
lemma "((A \<and> (B \<longrightarrow> C )) \<longrightarrow> A) \<longleftrightarrow> ((A  \<and> (B \<longrightarrow> \<not>C)) \<longrightarrow> A) "
proof -
  {
    assume "(A \<and> (B \<longrightarrow> C )) \<longrightarrow> A" 
    {
      assume "A  \<and> (B \<longrightarrow> \<not>C)"
      hence A by (rule conjE)
    }
    hence "(A \<and> (B \<longrightarrow> \<not>C)) \<longrightarrow> A" by (rule impI)
  }
  moreover
  {
    assume "(A  \<and> (B \<longrightarrow> \<not>C)) \<longrightarrow> A"
    {
      assume "A \<and> (B \<longrightarrow> C )"
      hence  A by (rule conjE)
    }
    hence "(A \<and> (B \<longrightarrow> C )) \<longrightarrow> A" by (rule impI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  

        
        
      