theory Ex011
imports Main
begin 


lemma "(A \<and> \<not>A) \<longrightarrow> B" 
proof - 
{
  assume "A \<and> \<not>A"
  hence A by (rule conjE)
  from \<open>A \<and> \<not>A\<close> have "\<not>A" by (rule conjE)
  with \<open>A\<close> have B by contradiction
}
thus ?thesis by (rule impI)
qed