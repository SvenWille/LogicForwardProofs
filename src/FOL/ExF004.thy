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
    hence  "\<not>(\<forall>x. \<exists>y. P x y)" by (rule notI)
    {
      assume "\<not>(\<exists>x. \<forall>y. \<not>P x y)"
      {
        
        {
          fix aa 
          assume b:"\<exists>y. \<not>P aa y"