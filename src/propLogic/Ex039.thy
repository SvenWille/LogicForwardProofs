theory Ex039
  imports Main 
begin 
  
  
lemma "\<not>(((A \<longrightarrow> B)  \<and>  A) \<and> (B \<longrightarrow> \<not>C \<and> \<not>C \<longrightarrow> B)) \<longrightarrow> ((\<not>D \<longrightarrow> B) \<or> (B \<longrightarrow> (\<not>B \<longrightarrow> \<not>A)))"  
proof -
  {
    assume "\<not>(((A \<longrightarrow> B)  \<and>  A) \<and> (B \<longrightarrow> \<not>C \<and> \<not>C \<longrightarrow> B))"
    {
      assume a:"B"
      {
        assume b:"\<not>B"
        from a and b have False by contradiction
        hence "\<not>A" by (rule FalseE)
      }
      hence "\<not>B \<longrightarrow> \<not>A" by (rule impI)
    }
    hence "B \<longrightarrow> \<not>B \<longrightarrow> \<not>A" by (rule impI)
    hence "(\<not>D \<longrightarrow> B) \<or> (B \<longrightarrow> (\<not>B \<longrightarrow> \<not>A))" by (rule disjI2)
  }
  thus ?thesis by (rule impI)
qed
  