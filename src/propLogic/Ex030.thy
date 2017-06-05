theory Ex030
  imports Main 
begin 
  
  
lemma "(A \<longrightarrow> B \<longrightarrow> C)  \<longleftrightarrow> (\<not>C \<longrightarrow> A \<longrightarrow> \<not>B)" 
proof -
  {
    assume a:"A \<longrightarrow> B \<longrightarrow> C"
    {
      assume b:"\<not>C"
      {
        assume A 
        with a have c:"B \<longrightarrow> C" by (rule mp)
        {
          assume B 
          with c have C by (rule mp)
          with b have False by contradiction
        }
        hence "\<not>B" by (rule notI)
      }
      hence "A \<longrightarrow> \<not>B" by (rule impI)
    }
    hence "\<not>C \<longrightarrow> A \<longrightarrow> \<not>B" by (rule impI)
  }
  moreover
  {
    assume d:"\<not>C \<longrightarrow> A \<longrightarrow> \<not>B"
    {
      assume e:A 
      {
        assume f:B 
        {
          assume "\<not>C"
          with d have "A \<longrightarrow> \<not>B" by (rule mp)
          from this and e have "\<not>B" by (rule mp)
          with f have False by contradiction
        }
        hence "\<not>\<not>C" by (rule notI)
        hence C by (rule notnotD)
      }
      hence "B \<longrightarrow> C" by (rule impI)
    }
    hence "A \<longrightarrow> B \<longrightarrow> C" by (rule impI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
            
          