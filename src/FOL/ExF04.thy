theory ExF04
imports Main 
begin 
thm allI
thm exE
  thm exI
  thm allI
  thm notI
lemma "(\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y)" 
proof - 
  {
    fix a b 
    assume "\<not>((\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y) )"
    {
      assume "(\<forall>x. \<exists>y. P x y)"
        hence "(\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y)" ..
        with \<open>\<not>((\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y) )\<close> have False ..
            
    }
        
    
  
  
  