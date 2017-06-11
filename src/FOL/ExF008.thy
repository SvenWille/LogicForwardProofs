theory ExF008
  imports Main 
begin 
 

  
lemma "(\<not> (\<exists>x. \<forall>y. P x y)) \<longleftrightarrow> (\<forall>x. \<exists>y. \<not>P x y)" 
proof-
  {
    assume a:"\<not> (\<exists>x. \<forall>y. P x y)"
    {
      assume b:"\<not>(\<forall>x. \<exists>y. \<not>P x y)" 
      {
        fix aa 
        {
          assume c:"\<not>(\<exists>y. \<not>P aa y)"
          {
            fix bb
            {
              assume "\<not>P aa bb" 
              hence "\<exists>y. \<not>P aa y" by (rule exI)
              with c have False by contradiction
            }
            hence "\<not>\<not>P aa bb" by (rule notI)
            hence "P aa bb" by (rule notnotD)
          }
          hence "\<forall>y. P aa y" by (rule allI)
          hence "\<exists>x. \<forall>y. P x y" by (rule exI)
          with a have False by contradiction
        }
        hence "\<not>\<not>(\<exists>y. \<not>P aa y)" by (rule notI)
        hence "\<exists>y. \<not>P aa y" by (rule notnotD)
      }
      hence "\<forall>x. \<exists>y. \<not>P x y" by (rule allI)
      with b have False by contradiction
    }
    hence "\<not>\<not>(\<forall>x. \<exists>y. \<not>P x y)" by (rule notI)
    hence "\<forall>x. \<exists>y. \<not>P x y" by (rule notnotD)
  }
  moreover
  {
    assume a:"\<forall>x. \<exists>y. \<not>P x y"
    {
      assume b:"\<exists>x. \<forall>y. P x y" 
      {
        fix aa
        assume c:"\<forall>y. P aa y"
        from a have d:"\<exists>y. \<not>P aa y" by (rule allE)
        {
          fix bb 
          assume d:" \<not>P aa bb" 
          from c have "P aa bb" by (rule allE)
          with d have False by contradiction
        }
        with d have False by (rule exE)
      }
      with b have False by (rule exE)
    }
    hence "\<not>(\<exists>x. \<forall>y. P x y)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  

          
          
              