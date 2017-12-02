theory ExF005
  imports Main 
begin
  

lemma "(\<forall>x . (P x \<and> Q x)) \<longrightarrow> ((\<forall>x . P x) \<and> (\<forall> x . Q x))"
proof - 
  {    
    assume "\<forall>x . (P x \<and> Q x)"
    {
      fix a
      from \<open>\<forall>x . (P x \<and> Q x)\<close> have "P a \<and> Q a" by (rule allE)
      hence "P a" by (rule conjE)
    }
    hence "\<forall>x . P x" by (rule allI)
    {    
      fix a
      from \<open>\<forall>x . (P x \<and> Q x)\<close> have "P a \<and> Q a" by (rule allE)
      hence "Q a" by (rule conjE)
    }
    hence "\<forall>x . Q x" by (rule allI)
    with \<open>\<forall>x . P x\<close> have "(\<forall>x . P x) \<and> (\<forall> x . Q x)" by (rule conjI)
  }
  thus ?thesis by (rule impI)
qed
  
      