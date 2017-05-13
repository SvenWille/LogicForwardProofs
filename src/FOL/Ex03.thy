theory Ex03
imports Main 
begin 


lemma "(\<forall>x. P x \<longrightarrow> P(Q x)) \<and> P a \<longrightarrow> P (Q (Q a))" 
proof - 
{
  assume "(\<forall>x. P x \<longrightarrow> P(Q x)) \<and> P a"
  hence "\<forall>x. P x \<longrightarrow> P(Q x)" by (rule conjE)
  from \<open>(\<forall>x. P x \<longrightarrow> P(Q x)) \<and> P a\<close> have "P a" by (rule conjE)
  from  \<open>(\<forall>x. P x \<longrightarrow> P(Q x))\<close> have "P a \<longrightarrow> P(Q a)" by (rule allE)
  from this and \<open>P a\<close> have "P (Q a)" by (rule impE)
  from  \<open>(\<forall>x. P x \<longrightarrow> P(Q x))\<close> have "P (Q a) \<longrightarrow> P (Q (Q a))" by (rule allE)
  from this and \<open>P (Q a)\<close> have " P (Q (Q a))" by (rule impE)
}
thus ?thesis by (rule impI)
qed