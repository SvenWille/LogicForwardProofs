theory ExF06
  imports Main
begin
  
  
lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)" 
proof -
  {
    assume "\<exists>x. \<forall>y. P x y" 
    { 
      fix b
      {
        fix a           
        assume "\<forall>y .P a y"
        hence "P a b" by (rule allE)
        hence "\<exists>x. P x b" by (rule exI)
      } 
      with  \<open>\<exists>x. \<forall>y. P x y\<close> have "\<exists>x. P x b" by (rule exE)
    }
    hence "\<forall>y. \<exists>x. P x y" by (rule allI)
  }
  thus ?thesis by (rule impI)
qed
  
          
        
      
      