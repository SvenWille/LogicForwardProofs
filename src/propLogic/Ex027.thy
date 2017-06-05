theory Ex027
  imports Main 
begin 
  
(*law of excluded middle*)
lemma "P \<or> \<not>P"
proof -
  {
    assume a:"\<not>(P \<or> \<not>P)"
    {
      assume b:P
      hence "P \<or> \<not>P" by (rule disjI1)
      with a have False by contradiction
    }
    hence "\<not>P" by (rule notI)
    hence "P \<or> \<not>P" by (rule disjI2)
    with a have False by contradiction
  }
  hence "\<not>\<not>(P \<or> \<not>P)" by (rule notI)
  thus ?thesis by (rule notnotD)
qed
  
    
        
        
      