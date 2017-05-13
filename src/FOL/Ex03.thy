theory Ex03
imports Main 
begin 


lemma "(\<forall>x. P x \<longrightarrow> P(Q x)) \<and> P a \<longrightarrow> P (Q (Q a))" 
proof - 
{
  assume "(\<forall>x. P x \<longrightarrow> P(Q x)) \<and> P a"
  hence "\<forall>x. P x \<longrightarrow> P(Q x)" by (rule conjE)
  from \<open>(\<forall>x. P x \<longrightarrow> P(Q x)) \<and> P a\<close> have "P a" by (rule conjE)
  