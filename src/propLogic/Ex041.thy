theory Ex041
  imports Main 
begin 
  
  
lemma "B \<and> B \<longrightarrow> A \<longrightarrow> ((C \<or> \<not>B) \<or> A \<longleftrightarrow> A \<and> \<not>(B \<longrightarrow> \<not>A))"
proof - 
  {
    assume a:"B \<and> B"
    hence b:B by (rule conjE)
    {
      assume c:A 
      {
        assume "(C \<or> \<not>B) \<or> A"
        {
          assume "B \<longrightarrow> \<not>A"
          from this and  b have "\<not>A" by (rule mp)
          with c have False by contradiction
        }
        hence "\<not>(B \<longrightarrow> \<not>A)" by (rule notI)
            with c have "A \<and> \<not>(B \<longrightarrow> \<not>A)" by (rule conjI)
      }
      moreover
      {
        assume d:"A \<and> \<not>(B \<longrightarrow> \<not>A)"
        hence A by (rule conjE)
        hence "(C \<or> \<not>B) \<or> A" by (rule disjI2)
      }
      ultimately have "(C \<or> \<not>B) \<or> A \<longleftrightarrow> A \<and> \<not>(B \<longrightarrow> \<not>A)" by (rule iffI)
    }
    hence " A \<longrightarrow> ((C \<or> \<not>B) \<or> A \<longleftrightarrow> A \<and> \<not>(B \<longrightarrow> \<not>A))" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
        
          
              