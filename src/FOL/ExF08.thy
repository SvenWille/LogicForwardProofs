theory ExF08
  imports Main 
begin 
  
  
lemma "(\<not> (\<exists>x. \<forall>y. P x y)) \<longleftrightarrow> (\<forall>x. \<exists>y. \<not>P x y)" 
proof-
  {
    assume "\<not> (\<exists>x. \<forall>y. P x y)"
    {
      