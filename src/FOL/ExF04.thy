theory ExF04
imports Main 
begin 
thm allI
thm exI
lemma "(\<forall>x. \<exists>y. P x y) \<or> (\<exists>x. \<forall>y. \<not>P x y)" 
proof - 
  {
    
  
  
  