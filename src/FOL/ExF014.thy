theory ExF014
  imports Main 
begin 
  
  
lemma "\<not>(\<exists>x. P x) \<longleftrightarrow> (\<forall>x. \<not>P x)"  
proof -
  {
    assume "\<not>(\<exists>x. P x)"
    {
      assume "\<not>(\<forall>x. \<not>P x)"
      {
        fix aa 
        {
          assume "P aa"
          hence "\<exists>x. P x" by (rule exI)
          with \<open>\<not>(\<exists>x. P x )\<close> have False by contradiction
        }
        hence "\<not>P aa" by (rule notI)
      }
      hence "\<forall>x. \<not>P x" by (rule allI)
      with \<open>\<not>(\<forall>x. \<not>P x)\<close> have False by contradiction
    }
    hence "\<not>\<not>(\<forall>x. \<not>P x)" by (rule notI)
    hence "\<forall>x. \<not>P x" by (rule notnotD)
  }
    
  moreover
  {
    assume a:"\<forall>x. \<not>P x"
    {
      assume "\<exists>x. P x"
      {
        fix aa 
        assume "P aa"
        from \<open>\<forall>x. \<not>P x\<close> have "\<not>P aa" by (rule allE)
        with \<open>P aa\<close> have False by contradiction
      }
      with \<open>\<exists>x. P x\<close> have False by (rule exE)
    }
    hence "\<not>(\<exists>x. P x)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)    
qed