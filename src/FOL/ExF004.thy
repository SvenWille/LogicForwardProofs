theory ExF004
imports Main 
begin 


  
theorem "(\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y)" 
proof - 
  {
    assume a:"\<not>((\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y) )"
    {
      assume "\<forall>x. \<exists>y. P x y"
      hence "(\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y)" ..
      with a have False ..
    }
    hence  b:"\<not>(\<forall>x. \<exists>y. P x y)" by (rule notI)
    {
      assume c:"\<not>(\<exists>x. \<forall>y. \<not>P x y)"
      {
        fix aa
        {
          assume d:"\<not>(\<exists>y. P aa y)"    
          {
            fix bb 
            {
              assume "P aa bb"
              hence "\<exists>y. P aa y" by (rule exI)
              with d have False by contradiction
            }
            hence "\<not>P aa bb" by (rule notI)
          }
          hence "\<forall>y. \<not>P aa y" by (rule allI)
          hence "\<exists>x. \<forall>y. \<not>P x y" by (rule exI)
          with c have False by contradiction
        }
        hence "\<not>\<not>(\<exists>y. P aa y)" by (rule notI)
        hence "\<exists>y. P aa y" by (rule notnotD)
      }
      hence "\<forall>x. \<exists>y. P x y" by (rule allI)
      with b have False by contradiction
    }
    hence "\<not>\<not>(\<exists>x. \<forall>y. \<not>P x y)" by (rule notI)
    hence "\<exists>x. \<forall>y. \<not>P x y" by (rule notnotD)
    hence "(\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y)"  by (rule disjI2)
    with a have False by contradiction
  }
  hence "\<not>\<not>((\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y))" by (rule notI)
  thus ?thesis by (rule notnotD)
qed
  
      
      
          
      
          
          
              
                
            