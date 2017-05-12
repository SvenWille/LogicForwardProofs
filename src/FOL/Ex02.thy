theory Ex02
imports Main 
begin 

thm impE
lemma "\<lbrakk> \<forall>x.(P x \<longrightarrow> Q x) ; P a \<rbrakk> \<Longrightarrow> Q a"
proof - 
assume "\<forall>x.(P x \<longrightarrow> Q x)"
assume "P a"
from \<open>\<forall>x.(P x \<longrightarrow> Q x)\<close> have "P a \<longrightarrow> Q a" by (rule allE)
from this and  \<open>P a\<close> show ?thesis by (rule impE) 
qed
