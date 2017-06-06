theory Ex032
  imports Main 
begin 
  
  
lemma "((A \<and> B ) \<longrightarrow> C) \<longleftrightarrow> ((A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B)) "    
proof -
  {
    assume a:"(A \<and> B ) \<longrightarrow> C"
    {
      assume b:"\<not> ((A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B))"
      {
        assume c:A 
        {
          assume d:"\<not>C"
          {
            assume B
            with c have "A \<and> B" by (rule conjI)
            with a have e:C by (rule mp)
            {
              assume A 
              have C by (rule e)
            }
            hence "A \<longrightarrow> C" by (rule impI)
            hence "(A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B)" by (rule disjI1) 
            with b have False by contradiction
          }
          hence "\<not>B" by (rule notI)
        }
        hence "\<not>C \<longrightarrow> \<not>B" by (rule impI)
        hence "(A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B)" by (rule disjI2)
        with b have False by contradiction
        hence C by (rule FalseE)
      }
      hence "A \<longrightarrow> C" by (rule impI)
      hence "(A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B)" by (rule disjI1)
      with  b have False by contradiction
    }
    hence "\<not>\<not>((A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B))" by (rule notI)
    hence "(A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B)" by (rule notnotD)
  }
  moreover
  {
    assume e:"(A \<longrightarrow> C) \<or> (\<not>C \<longrightarrow> \<not>B)" 
    {
      assume f:"A \<longrightarrow> C"
      {
        assume g:"\<not>((A \<and> B ) \<longrightarrow> C)"
        {
          assume "A \<and> B"
          hence A by (rule conjE)
          with f have C by (rule mp)
        }
        hence "A \<and> B \<longrightarrow> C" by (rule impI)
        with g have False by contradiction
      }
      hence "\<not>\<not>(A \<and> B \<longrightarrow> C)" by (rule notI)
      hence "A \<and> B \<longrightarrow> C" by (rule notnotD)
    }
    note h=this
    {
      assume i:"\<not>C \<longrightarrow> \<not>B"
      {
        assume j:"\<not>((A \<and> B ) \<longrightarrow> C)"
        {
          assume k:"A \<and> B" 
          {
            assume "\<not>C"
            with i have l:"\<not>B" by (rule mp)
            from k have B by (rule conjE)
            with l have False by contradiction
          }
          hence "\<not>\<not>C" by (rule notI)
          hence C by (rule notnotD)
        }
        hence "(A \<and> B ) \<longrightarrow> C" by (rule impI)
        with j have False by contradiction
      }
      hence "\<not>\<not>((A \<and> B ) \<longrightarrow> C)" by (rule notI)
      hence "(A \<and> B ) \<longrightarrow> C" by (rule notnotD)
    }
    with e and h  have "(A \<and> B ) \<longrightarrow> C" by (rule disjE)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
            
        
           
          
          
          