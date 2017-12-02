theory Ex047
  imports Main 
begin
  
theorem "(\<forall>A B . ((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A) \<longleftrightarrow> (\<forall>A. \<not>A \<or> A)" 
proof -
  {
    assume a:"\<forall>A B. ((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A" 
    {
      fix AA B
      {
        assume b:"(AA \<longrightarrow> B)"
          with a have 

      }
    }
  }
    
    
(*simple version*)      
  
theorem "(\<forall>A B . ((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A) \<longleftrightarrow> (\<forall>A. \<not>A \<or> A)" 
proof - 
  {
    assume a:"\<forall>A B. ((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
    {
      fix AA
      {
        assume b:"\<not>(\<not>AA \<or> AA)"
        {
          assume "\<not>AA"
          hence "\<not>AA \<or> AA" by (rule disjI1)
          with b have False by contradiction
        }
        hence "AA" by (rule notI[THEN notnotD])
        hence "\<not>AA \<or> AA" by (rule disjI2)
        with b have False by contradiction
      }
      hence "\<not>AA \<or> AA" by (rule notI[THEN notnotD])
    }
    hence "\<forall>A. \<not>A \<or> A" by (rule allI)
  }
  moreover
  {
    assume "\<forall>A . \<not>A \<or> A"
  }
    
        
            