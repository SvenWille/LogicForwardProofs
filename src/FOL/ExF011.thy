theory ExF011
  imports Main
begin 
  
  
lemma "(\<not> (\<exists>x. \<forall>y. P x y)) \<longrightarrow> \<not>(\<exists>x. \<exists>y .  \<not>P x y) \<longrightarrow> False " 
proof -
  assume "(\<not> (\<exists>x. \<forall>y. P x y))"
  {
    assume "\<not>(\<exists>x. \<exists>y .  \<not>P x y)"
    {
      fix aa 
      {
        assume 