theory ExF011
  imports Main
begin 
  
   
  
lemma "(\<not> (\<exists>x. \<forall>y. P x y)) \<longrightarrow> \<not>(\<exists>x. \<exists>y .  \<not>P x y) \<longrightarrow> False " 
proof -
  {
    assume a:"(\<not> (\<exists>x. \<forall>y. P x y))"
    {
      fix aa
      assume b:"\<not>(\<exists>x. \<exists>y .  \<not>P x y)"
      {
        fix bb
        {
          assume "\<not>P aa bb"
          hence "\<exists>y. \<not>P aa y" by (rule exI)
          hence "\<exists>x. \<exists>y. \<not>P x y" by (rule exI)
          with b have False by contradiction
        }
        hence "\<not>\<not>P aa bb" by (rule notI)
        hence "P aa bb" by (rule notnotD)
      }
      hence "\<forall>y. P aa y" by (rule allI)
      hence "\<exists>x. \<forall>y. P x y" by (rule exI)
      with a have False by contradiction
    }
    hence "\<not>(\<exists>x. \<exists>y .  \<not>P x y) \<longrightarrow> False " by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
      
      
        