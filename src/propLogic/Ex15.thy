theory Ex15 
imports Main 
begin


(*Proof (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> A \<and> B*)


lemma "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> A \<and> B"
proof -
{
  assume "A \<longrightarrow> B"
  {
    assume A 
    with \<open>A \<longrightarrow> B\<close> have B by (rule impE)
    with \<open>A\<close> have "A \<and> B" by (rule conjI)
  }
  hence "A \<longrightarrow> A \<and> B" by (rule impI)
}
thus ?thesis by (rule impI)
qed