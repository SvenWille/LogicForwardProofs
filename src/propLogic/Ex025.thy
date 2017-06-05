theory Ex025
  imports Main 
begin 
  
  
lemma "A \<longleftrightarrow> \<not>\<not>A" 
proof -
  {
    assume a:A 
    {
      assume "\<not>A"
      with a have False by contradiction
    }
    hence "\<not>\<not>A" by (rule notI)
  }
  moreover 
  {
    assume "\<not>\<not>A"
    hence A by (rule notnotD)     
  }    
  ultimately show ?thesis by (rule iffI)    
qed
  
    
 
        
  