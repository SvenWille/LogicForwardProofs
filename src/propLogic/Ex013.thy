theory Ex013
imports Main 
begin 


lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not>B \<longrightarrow> \<not>A)"
proof - 
{
  assume "A \<longrightarrow> B"
  {
    assume "\<not>B"
    {
      assume A 
      with \<open>A \<longrightarrow> B\<close> have B by (rule impE)
      with \<open>\<not>B\<close> have False by contradiction
    }
    hence "\<not>A" by (rule notI)
  }
  hence "\<not>B \<longrightarrow> \<not>A" by (rule impI)
}
thus ?thesis by (rule impI)
qed

