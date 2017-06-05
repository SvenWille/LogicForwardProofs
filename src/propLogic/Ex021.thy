theory Ex021
imports Main 
begin 

 
  
lemma "(A \<longleftrightarrow> B)  \<longleftrightarrow> (A \<and> B) \<or> (\<not>A \<and> \<not>B)" 
proof -
  {
    assume a:"A \<longleftrightarrow> B"
    hence b:"A \<longrightarrow> B" by (rule iffE)
    from a have c:"B \<longrightarrow> A" by (rule iffE)
    {
      assume d:"\<not> ((A \<and> B) \<or>  (\<not>A \<and> \<not>B))"
      {
        assume e:A 
        with b have B by (rule mp)
        with e have "A \<and> B" by (rule conjI)
        hence "(A \<and> B) \<or> (\<not>A \<and> \<not>B)" by (rule disjI1)
        with d have False by contradiction
      }
      hence f:"\<not>A" by (rule notI)
      {
        assume g:B 
        with c have A by (rule mp)
        from this and  g have "A \<and> B" by (rule conjI)
        hence "(A \<and> B) \<or> (\<not>A \<and> \<not>B)" by (rule disjI1)
        with d have False by contradiction
      }
      hence h:"\<not>B" by (rule notI)
      from f and h have "\<not>A \<and> \<not>B" by (rule conjI)
      hence "(A \<and> B) \<or>  (\<not>A \<and> \<not>B)" by (rule disjI2)
      with d have False by contradiction
    }
    hence "\<not>\<not> ((A \<and> B) \<or>  (\<not>A \<and> \<not>B))" by (rule notI)
    hence "(A \<and> B) \<or>  (\<not>A \<and> \<not>B)" by (rule notnotD)
  }
  moreover
  {
    assume a:"(A \<and> B) \<or> (\<not>A \<and> \<not>B)" 
    {
      assume b:"A \<and> B"
      hence c:A by (rule conjE)
      from b have d:B by (rule conjE)
      {
        assume A 
        have B by (rule d)
      }
      moreover
      {
        assume B 
        have A by (rule c)
      }
      ultimately have "A \<longleftrightarrow> B" by (rule iffI)
    }
    note d=this 
    {
      assume e:"\<not>A \<and> \<not>B" 
      hence f:"\<not>A" by (rule conjE)
      from e have g:"\<not>B" by (rule conjE)          
      {
        assume h:"\<not>(A \<longrightarrow> B)"
        {
          assume A 
          with f have False by contradiction
          hence B by (rule FalseE)
        }
        hence "A \<longrightarrow> B" by (rule impI)
        with h have False by contradiction
      }
      hence "\<not>\<not>(A \<longrightarrow> B)" by (rule notI)
      hence i:"A \<longrightarrow> B" by (rule notnotD)
      {
        assume A 
        with i have B by(rule mp)
      }
      moreover
      {
        assume j:"\<not>(B \<longrightarrow> A)"
        {
          assume B
          with g have False by contradiction
          hence A by (rule FalseE)
        }
        hence " B \<longrightarrow> A" by (rule impI)
        with j have False by contradiction
      }
      hence "\<not>\<not>(B \<longrightarrow> A)" by (rule notI)
      hence k:"B \<longrightarrow> A" by (rule notnotD)
      {
        assume B 
        with k have A by (rule mp)
      }
        ultimately have "A \<longleftrightarrow> B" by (rule iffI)
    }
    from a and d and this have "A \<longleftrightarrow> B" by (rule disjE)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
            
        
            
      
          
          
        