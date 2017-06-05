theory Ex029 
  imports Main 
begin 
  
(*since implication has right associativity this is the same as (A \<longrightarrow> B) \<longrightarrow> (C \<longrightarrow> \<not>B) \<longrightarrow> A \<longrightarrow> \<not>C*)
lemma "(A \<longrightarrow> B) \<longrightarrow> (C \<longrightarrow> \<not>B) \<longrightarrow> (A \<longrightarrow> \<not>C)"
proof -
  {
    assume a:"A \<longrightarrow> B"
    {
      assume b:"C \<longrightarrow> \<not>B"
      {
        assume A
        with a have c:B by (rule mp)
        {
          assume C 
          with b have "\<not>B" by (rule mp)
          with c have False by contradiction
        }
        hence "\<not>C" by (rule notI)
      }
      hence "A \<longrightarrow> \<not>C" by (rule impI)
    }
    hence "(C \<longrightarrow> \<not>B) \<longrightarrow> A \<longrightarrow> \<not>C" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
  
      
          
        