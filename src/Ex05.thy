theory Ex05
imports Main 
begin 


lemma "(A \<and> (B \<longrightarrow> \<not>A)) \<longrightarrow> (A \<and> \<not>B)"
proof -
{
  assume "A \<and> (B \<longrightarrow> \<not>A)"
  hence "B \<longrightarrow> \<not>A" by (rule conjE)
  from \<open>A \<and> (B \<longrightarrow> \<not>A)\<close> have A by (rule conjE)
  {
    assume B
    with \<open>B \<longrightarrow> \<not>A\<close> have "\<not>A" by (rule impE)
    with \<open>A\<close>  have False by contradiction
  }
  hence "\<not>B" by (rule notI)
  with \<open>A\<close> have "A \<and> \<not>B" by (rule conjI)
}
thus ?thesis by (rule impI)
qed
