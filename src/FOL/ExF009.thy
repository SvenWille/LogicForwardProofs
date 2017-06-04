theory ExF009
  imports Main 
begin 
  

lemma "(\<exists>x. P x) =  (\<not>(\<forall>x. \<not>P x))" 
proof -
  {
    assume a:"\<exists>x. P x"
    {
      assume b:"\<forall>x. \<not>P x"
      {
        fix aa
        assume c:"P aa"
        from b have "\<not>P aa" by (rule allE)
        with c have False by contradiction
      }
      with a have False by (rule exE)
    }
    hence "\<not>(\<forall>x. \<not>P x)" by (rule notI)
  }
  moreover
  {
    assume d:"\<not>(\<forall>x. \<not>P x)"
    {
      assume e:"\<not>(\<exists>x. P x)"
      {
        fix aa
        {
          assume "P aa"
          hence "\<exists>x. P x" by (rule exI)
          with e have False by contradiction
        }   
        hence "\<not>P aa" by (rule notI)
      }
      hence "\<forall>x. \<not>P x" by (rule allI)
      with d have False by contradiction
    }
    hence "\<not>\<not>(\<exists>x. P x)" by (rule notI)
    hence "(\<exists>x. P x)" by (rule notnotD)
  }
  ultimately show ?thesis by (rule iffI)
qed