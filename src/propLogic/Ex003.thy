theory Ex003 
imports Main 
begin 



lemma "\<not>A \<longrightarrow> A \<longrightarrow> B"
proof - 
{
  assume "\<not>A"
  {
    assume A
    with \<open>\<not>A\<close> have B by (rule notE)
  }
  hence "A \<longrightarrow> B" by (rule impI)
}
thus ?thesis by (rule impI)
qed