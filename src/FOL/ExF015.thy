theory ExF015
  imports Main 
begin
  
lemma "\<not>(\<forall>x. P x) \<longleftrightarrow> (\<exists>x. \<not>P x)" 
proof -
  {
    assume a:"\<not>(\<forall>x. P x)" 
    {
      assume b:"\<not>(\<exists>x. \<not>P x)"
      {
        fix aa 
        {
          assume "\<not>P aa"
          hence "\<exists>x. \<not>P x" by (rule exI)
          with b have False by contradiction
        }
        hence "\<not>\<not>P aa" by (rule notI)
        hence "P aa" by (rule notnotD)
      }
      hence "\<forall>x. P x" by (rule allI)
      with a have False by contradiction
    }
    hence "\<not>\<not>(\<exists>x. \<not>P x)" by (rule notI)
    hence "\<exists>x. \<not>P x" by (rule notnotD)
  }
  moreover
  {
    assume a:"\<exists>x. \<not>P x"
    {
      assume b:"\<forall>x. P x" 
      {
        fix aa
        assume c:"\<not>P aa"
        from b have "P aa" by (rule allE)
        with c have False by contradiction
      }
      with a have False by (rule exE)
    }
    hence "\<not>(\<forall>x. P x)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
    