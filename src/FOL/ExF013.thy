theory ExF013
  imports Main
begin
  

  
lemma "\<And>aa. ((\<forall>x. (P x \<longrightarrow> Q x)) \<and> P aa  \<longrightarrow> Q aa)" 
proof -
  {
    fix aa
    assume a:"(\<forall>x. (P x \<longrightarrow> Q x)) \<and> P aa"
    hence b:"P aa" by (rule conjE)
    from a have "\<forall>x. (P x \<longrightarrow> Q x)" by (rule conjE)
    hence "P aa \<longrightarrow> Q aa" by (rule allE)
    from this and b have "Q aa" by (rule mp)
  }
  thus "\<And>aa. ((\<forall>x. (P x \<longrightarrow> Q x)) \<and> P aa  \<longrightarrow> Q aa)"  by (rule impI)  
qed
    
  
   

        