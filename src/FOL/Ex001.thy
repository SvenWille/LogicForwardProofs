theory Ex001 
imports Main 
begin 


lemma "\<lbrakk> P a ; Q a \<rbrakk> \<Longrightarrow> \<exists>x. P x \<and> Q x"
proof - 
assume "P a"
assume "Q a"
with \<open>P a\<close> have "P a \<and> Q a" by (rule conjI)
thus ?thesis by (rule exI)
qed