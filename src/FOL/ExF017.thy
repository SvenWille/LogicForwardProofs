theory ExF017
  imports Main 
begin 

   
lemma "P a (Q (Q a))  \<longrightarrow> (\<forall>x. \<forall>y. P x (Q y) \<longrightarrow> (\<exists>z. P (Q z) y)) \<longrightarrow> (\<exists>z. P z a)" 
proof -
  {
    assume a:"P a (Q (Q a))"
    hence b:"\<exists>z. P z (Q (Q a))" by (rule exI)
    {
      assume c:"(\<forall>x. \<forall>y. P x (Q y) \<longrightarrow> (\<exists>z. P (Q z) y))"
      hence "(\<forall>y. P a (Q y) \<longrightarrow> (\<exists>z. P (Q z) y))"  ..
      hence "(P a (Q (Q a)) \<longrightarrow> (\<exists>z. P (Q z) (Q a)))" ..
      from this a have d:"(\<exists>z. P (Q z) (Q a))" by (rule mp)
      {
        assume e:"(\<forall>z . \<not>P z a)" 
        {
          fix b     
          assume f:"P (Q b) (Q a)"
          from c have "(\<forall>y. P (Q b) (Q y) \<longrightarrow> (\<exists>z. P (Q z) y))" by (rule allE)
          hence "P (Q b) (Q a) \<longrightarrow> (\<exists>z. P (Q z) a)" by (rule allE)
          from this and  f have g:"\<exists>z. P (Q z) a" by (rule mp)
          {
            fix c 
            assume h:"P (Q c) a" 
            from e have "\<not>P (Q c) a" by (rule allE)
            with h have False by contradiction
          }
          with g have False by (rule exE)
        }
        with d have False by (rule exE)
      }
      hence e:"\<not>(\<forall>z . \<not>P z a)" by (rule notI)
      have f:"(\<exists>z. P z a)"
      proof -
        {
          assume g:"\<not>(\<exists>z. P z a)"
          have h:"\<forall>z. \<not>P z a"
          proof -
            {
              assume i:"\<not>(\<forall>z . \<not>P z a)"
              {
                fix b 
                {
                  assume "P b a"
                  hence "\<exists>z. P z a" by (rule exI)
                  with g have False by contradiction
                }
                hence "\<not>P b a" by (rule notI)
              }
              hence "\<forall>z. \<not>P z a" by (rule allI)
              with i have False by contradiction
            }
            hence "\<not>\<not>(\<forall>z . \<not>P z a)" by (rule notI)
            thus "\<forall>z . \<not>P z a" by (rule notnotD)
          qed
          from h and e have False by contradiction  
        }
        hence "\<not>\<not>(\<exists>z. P z a)" by (rule notI)
        thus "\<exists>z. P z a" by (rule notnotD)
      qed  
    }
    hence "((\<forall>x. \<forall>y. P x (Q y) \<longrightarrow> (\<exists>z. P (Q z) y))) \<longrightarrow> (\<exists>z. P z a)" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
      

          