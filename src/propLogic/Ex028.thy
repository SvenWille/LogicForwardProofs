theory Ex028
  imports Main 
begin 
  
  
  
lemma "\<not>(A \<and> B) \<longleftrightarrow> (\<not>A \<or> \<not>B)" 
proof -
  {
    
    assume a:"\<not>(A \<and> B)"
    {
      assume b:"\<not>(\<not>A \<or> \<not>B)"
      {
        assume "\<not>A"
        hence "\<not>A \<or> \<not>B" by (rule disjI1)
        with b have False by contradiction
      }
      hence "\<not>\<not>A" by (rule notI)
      hence c:A by (rule notnotD)
      {
        assume "\<not>B"
        hence "\<not>A \<or> \<not>B" by (rule disjI2)
        with b have False by contradiction
      }
      hence "\<not>\<not>B" by (rule notI)
      hence B by (rule notnotD)
      with c have "A \<and> B" by (rule conjI)
      with a have False by contradiction
    }
    hence "\<not>\<not>(\<not>A \<or> \<not>B)" by (rule notI)
    hence "\<not>A \<or> \<not>B" by (rule notnotD)
  }
  moreover
  {
    assume a:"\<not>A \<or> \<not>B"
    {
      assume b:"A \<and> B"
      hence c:A by (rule conjE)
      from b have d:B by (rule conjE)
      {
        assume "\<not>A"
        with c have False by contradiction
      }
      note e=this
      {
        assume "\<not>B"
        with d have False by contradiction
      }
      with a and e have False by (rule disjE)
    }
    hence "\<not>(A \<and> B)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
          
          
  
        