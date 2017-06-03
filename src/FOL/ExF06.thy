theory ExF06
  imports Main
begin
  
lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)" 
proof -
  {
    assume "\<exists>x. \<forall>y. P x y" 
      
      