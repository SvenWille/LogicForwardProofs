theory ExF012
  imports Main 
begin 
  
  
lemma "(\<forall>x. (P x \<longrightarrow> Q x)) \<longrightarrow> (\<forall>x. (Q x \<longrightarrow> R x)) \<longrightarrow> (\<forall>x .(P x \<longrightarrow> R x))"  
proof - 
  {
    assume a:"\<forall>x. (P x \<longrightarrow> Q x)"
    {
      assume b:"\<forall>x. (Q x \<longrightarrow> R x)"
      {
        fix aa 
        {
          assume c:"P aa"
          from b have e:"Q aa \<longrightarrow> R aa" by (rule allE)
          from a have d:"P aa \<longrightarrow> Q aa" by (rule allE)
          from this and c have "Q aa" by (rule mp)
          with e have "R aa" by (rule mp)
        }
        hence "P aa \<longrightarrow> R aa" by (rule impI)
      }
      hence "\<forall>x. (P x \<longrightarrow> R x)" by (rule allI)
    }
    hence "(\<forall>x. (Q x \<longrightarrow> R x)) \<longrightarrow>(\<forall>x. (P x \<longrightarrow> R x))" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
  
              