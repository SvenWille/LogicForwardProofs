theory Ex031 
  imports Main 
begin 
  

 
lemma "(A \<longrightarrow> B) \<or> A \<longleftrightarrow> (B \<longrightarrow> A) \<or> B "  
proof - 
  {
    assume a:"(A \<longrightarrow> B) \<or> A"
    {
      assume b:"\<not>((B \<longrightarrow> A) \<or> B)"
      {
        assume c:A
        {
          assume B 
          have A by (rule c)
        }
        hence "B \<longrightarrow> A" by (rule impI)
        hence "(B \<longrightarrow> A) \<or> B" by (rule disjI1)
        with b have False by contradiction
        hence "(B \<longrightarrow> A) \<or> B" by (rule FalseE)
      }
      note d=this
      {
        assume "A \<longrightarrow> B"
        {
          assume e:B
          {
            assume "\<not>A"
            from e have "(B \<longrightarrow> A) \<or> B" by (rule disjI2)
            with b have False by contradiction
          }
          hence "\<not>\<not>A" by (rule notI)
          hence A by (rule notnotD)
        }
        hence "B \<longrightarrow> A" by (rule impI)
        hence "(B \<longrightarrow> A) \<or> B" by (rule disjI1)
      }
      from a and this and d have "(B \<longrightarrow> A) \<or> B" by (rule disjE)
      with b have False by contradiction
    }
    hence "\<not>\<not>((B \<longrightarrow> A) \<or> B)" by (rule notI)
    hence "(B \<longrightarrow> A) \<or> B" by (rule notnotD)
  }
  moreover
  {
    assume f:"(B \<longrightarrow> A) \<or> B"
    {
      assume g:"\<not>((A \<longrightarrow> B) \<or> A)"
      {
        assume h:B
        {
          assume A 
          have B by (rule h)
        }
        hence "A \<longrightarrow> B" by (rule impI)
        hence "(A \<longrightarrow> B) \<or> A" by (rule disjI1)
      }
      note i=this
      {
        assume "B \<longrightarrow> A"
        {
          assume j:A 
          {
            assume "\<not>B"
            from j have "(A \<longrightarrow> B) \<or> A" by (rule disjI2)
            with g have False by contradiction
          }
          hence "\<not>\<not>B" by (rule notI)
          hence B by (rule notnotD)
        }
        hence "A \<longrightarrow> B" by (rule impI)
        hence "(A \<longrightarrow> B) \<or> A" by (rule disjI1)
      }
      from f and this and i have "(A \<longrightarrow> B) \<or> A" by (rule disjE)
      with g have False by contradiction
    }
    hence "\<not>\<not>((A \<longrightarrow> B) \<or> A)" by (rule notI)
    hence "(A \<longrightarrow> B) \<or> A" by (rule notnotD)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
      
            
        
          
        