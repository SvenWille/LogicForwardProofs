theory ExF008
  imports Main 
begin 
 
  

  
lemma "(\<not> (\<exists>x. \<forall>y. P x y)) \<longleftrightarrow> (\<forall>x. \<exists>y. \<not>P x y)" 
proof-
  {
    assume a:"\<not> (\<exists>x. \<forall>y. P x y)"
    {
      assume b:"\<not>(\<forall>x. \<exists>y. \<not>P x y)" 
        