theory Ex038 
  imports Main 
begin 
  
  
lemma "\<not>C \<Longrightarrow> \<not>A  \<or>  ((B \<and> C) \<longrightarrow> A)"
proof -
  {
    assume a:"\<not>C"
    {
      assume b:"\<not>(\<not>A  \<or>  ((B \<and> C) \<longrightarrow> A))"
      {
        assume "B \<and> C"
        hence c:C by (rule conjE)
        {
          assume "\<not>A"
          from a and c have False by contradiction
        }
        hence "\<not>\<not>A" by (rule notI)
        hence A by (rule notnotD)
      }
      hence "B \<and> C \<longrightarrow> A" by (rule impI)
      hence "\<not>A  \<or>  ((B \<and> C) \<longrightarrow> A)" by (rule disjI2)
      with b have False by contradiction
    }
    hence "\<not>\<not>(\<not>A  \<or>  ((B \<and> C) \<longrightarrow> A))" by (rule notI)
    thus "\<not>A  \<or>  ((B \<and> C) \<longrightarrow> A)" by (rule notnotD)
  }
qed
  
    
        