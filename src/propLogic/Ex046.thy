theory Ex046
  imports Main 
begin 
  
theorem "(A \<and> (A \<longrightarrow> \<not>A)) \<Longrightarrow> (A \<and> (B \<longrightarrow> \<not>A))"  
proof -
  assume a:"A \<and> (A \<longrightarrow> \<not>A)"
  hence b:"A \<longrightarrow> \<not>A" by (rule conjE)
  from a have c:A by (rule conjE)
  with b have "\<not>A" by (rule impE)
  with c have False by contradiction
  thus ?thesis by (rule FalseE)
qed
  