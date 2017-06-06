theory ExF007
  imports Main 
begin 


lemma "(\<not>(\<forall>x. \<exists>y. P x y)) \<longleftrightarrow> (\<exists>x. \<forall>y. \<not>P x y)"  
proof -
  {
    assume a:"\<not> (\<forall>x. \<exists>y. P x y)"
    {
      assume b:"\<not>(\<exists>x. \<forall>y. \<not>P x y)"
      {
        fix aa
        {
          assume c:"\<not>(\<exists>y. P aa y)"
          {
            fix bb
            {
              assume "P aa bb"
              hence "\<exists>y. P aa y" by (rule exI)
              with c have False by contradiction
            }
            hence "\<not>P aa bb" by (rule notI)    
          }
          hence "\<forall>y. \<not>P aa y" by (rule allI)
          hence "\<exists>x. \<forall>y. \<not>P x y" by (rule exI)
          with b have False by contradiction
        }   
        hence "\<not>\<not>(\<exists>y. P aa y)" by (rule notI)  
        hence "\<exists>y. P aa y" by (rule notnotD)  
      }
      hence "\<forall>x. \<exists>y. P x y" by (rule allI)
      with a have False by contradiction
    }
    hence "\<not>\<not>(\<exists>x. \<forall>y. \<not>P x y)" by (rule notI)
    hence "\<exists>x. \<forall>y. \<not>P x y" by (rule notnotD)
  }  
  moreover
  {
    assume a:"\<exists>x. \<forall>y. \<not>P x y"
    {
      assume b:"\<forall>x. \<exists>y. P x y" 
      {
        fix aa 
        assume c:"\<forall>y. \<not>P aa y"
        from b have d:"\<exists>y. P aa y" by (rule allE)
        {
          fix bb
          assume d:"P aa bb" 
          from c have "\<not>P aa bb" by (rule allE)
          with d have False by contradiction
        }
        with d have False by (rule exE)
      }
      with a have False by (rule exE)
    }
    hence "\<not>(\<forall>x. \<exists>y. P x y)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
              