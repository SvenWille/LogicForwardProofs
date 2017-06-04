theory ExF010
  imports Main 
begin 
  

lemma "(\<forall>x. (P x \<longrightarrow> Q x)) \<longrightarrow> ((\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x))"
proof -
  {
    assume a:"\<forall>x. (P x \<longrightarrow> Q x)"
    {
      assume b:"\<forall>x. P x"
      {
        fix aa 
        from a have c:"P aa \<longrightarrow> Q aa" by (rule allE)
        from b have "P aa" by (rule allE)
        with c have "Q aa" by (rule mp)
      }
      hence "\<forall>x. Q x" by (rule allI)
    }
    hence "(\<forall>x. P x) \<longrightarrow> (\<forall>x. Q x)" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
  
      
    