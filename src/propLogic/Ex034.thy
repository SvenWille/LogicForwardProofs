theory Ex034
  imports Main 
begin 
  
lemma "(A \<or> ((B \<longrightarrow> C) \<and> D)) \<longrightarrow> ((B \<or> A) \<or> (\<not>C \<longrightarrow> D))"  
proof -
  {
    assume a:"A \<or> ((B \<longrightarrow> C) \<and> D)"
    {
      assume A 
      hence "B \<or> A" by (rule disjI2)
      hence "(B \<or> A) \<or> (\<not>C \<longrightarrow> D)" by (rule disjI1)
    }
    note b=this
    {
      assume c:"(B \<longrightarrow> C) \<and> D"
      hence d:"B \<longrightarrow> C" by (rule conjE)
      from c have e:D by (rule conjE)
      {
        assume f:"\<not>((B \<or> A) \<or> (\<not>C \<longrightarrow> D))"
        {
          assume g:"\<not>(\<not>C \<longrightarrow> D)"
          {
            assume "\<not>C"
            have D by (rule e)
          }
          hence "\<not>C \<longrightarrow> D" by (rule impI)
          with g have False by contradiction
        }
        hence "\<not>\<not>(\<not>C \<longrightarrow> D)" by (rule notI)
        hence "\<not>C \<longrightarrow> D" by (rule notnotD)
        hence "(B \<or> A) \<or> (\<not>C \<longrightarrow> D)" by (rule disjI2)
        with f have False by contradiction
      }
      hence "\<not>\<not>((B \<or> A) \<or> (\<not>C \<longrightarrow> D))" by (rule notI)
      hence "(B \<or> A) \<or> (\<not>C \<longrightarrow> D)" by (rule notnotD)
    }
    from a and b and this have "(B \<or> A) \<or> (\<not>C \<longrightarrow> D)" by (rule disjE)
  }
  thus ?thesis by (rule impI)
qed
  
        
    
  