theory Ex04
imports Main 
begin 


lemma  "(A \<longrightarrow> (B \<and> C)) \<longrightarrow> (A \<longrightarrow> B)"
proof - 
{
  assume "A \<longrightarrow> (B \<and> C)"
  {
    assume "A"
    with \<open>A \<longrightarrow> (B \<and> C)\<close> have "B \<and> C" by (rule impE)
    hence B by (rule conjE)
  }
  hence "A \<longrightarrow> B" by (rule impI)
}
thus ?thesis by (rule impI)
qed