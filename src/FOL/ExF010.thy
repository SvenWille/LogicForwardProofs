theory ExF010
  imports Main 
begin 
  
  
lemma "(\<forall>x. (P x \<longrightarrow> Q x)) \<longrightarrow> ((\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x))"
proof - 
  assume "(\<forall>x. (P x \<longrightarrow> Q x))"
    