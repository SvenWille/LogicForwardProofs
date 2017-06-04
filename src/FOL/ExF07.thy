theory ExF07
  imports Main 
begin 
  
  
thm exE
  thm allI
lemma "(\<not> (\<forall>x. \<exists>y. P x y)) \<longleftrightarrow> (\<exists>x. \<forall>y. \<not>P x y)"  
proof -
  {
    fix a b
    assume a:"\<not> (\<forall>x. \<exists>y. P x y)"
    {
      assume "P a b"
      hence "\<exists>y . P a y " ..
      hence "\<exists>x. \<exists>y . P x y" ..
      {
        assume "\<forall>x. P x b"
        {
          fix c
          {
            fix d
            
lemma "(\<not> (\<forall>x. \<exists>y. P x y)) \<longleftrightarrow> (\<exists>x. \<forall>y. \<not>P x y)"  
proof -
  {
    fix a b
    assume a:"\<not> (\<forall>x. \<exists>y. P x y)"
    {
      assume "\<not> (\<forall>x. \<exists>y. P x y) "