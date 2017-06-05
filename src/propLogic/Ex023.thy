theory Ex023
  imports Main 
begin 
     
  
lemma "(A \<longrightarrow> B)  \<longleftrightarrow> (\<not>A \<or> B)" 
proof -
  {
    assume a:"A \<longrightarrow> B"
    {
      assume b:"\<not>(\<not>A \<or> B)"
      {
        assume A 
        with a have B by (rule mp)
        hence "\<not>A \<or> B" by (rule disjI2)
        with b have False by contradiction
      }
      hence "\<not>A" by (rule notI)
      hence "\<not>A \<or> B" by (rule disjI1)
      with b have False by contradiction
    }
    hence "\<not>\<not>(\<not>A \<or> B)" by (rule notI)
    hence "\<not>A \<or> B" by (rule notnotD)
  }
  moreover
  {
    assume c:"\<not>A \<or> B" 
    {
      assume d:"\<not>(A \<longrightarrow> B)"
      {
        assume e:A 
        {
          assume "\<not>A"
          with e have False by contradiction
        }
        note f=this
        {
          assume g:B 
          {
            assume A
            have B by (rule g)
          }
          hence "A \<longrightarrow> B" by (rule impI)
          with d have False by contradiction
        }
        with c and f have False by (rule disjE)
        hence B by (rule FalseE)
      }
      hence "A \<longrightarrow> B" by (rule impI)
      with d have False by contradiction
    }
    hence "\<not>\<not>(A \<longrightarrow> B)" by (rule notI)
    hence "A \<longrightarrow> B" by (rule notnotD)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
        
          
          
          
        

          