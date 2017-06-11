theory Ex036
  imports Main 
begin 
  
  
lemma "(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"  
  using [[simp_trace_new mode=full]]
proof -
  {
    assume a:"A \<Longrightarrow> B" 
    hence b:"A \<longrightarrow> B" by (rule impI)
    {
      assume A
      with b show B by (rule mp)
    }
  }
qed
  
(*just another way to I like to represent this proof*)
lemma "(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"
proof -
  assume a:"A \<Longrightarrow> B"
  hence b:"A \<longrightarrow> B" by (rule impI)
  assume A
  with b show B by (rule mp)
qed

(*proving with meta implication*)  
lemma "(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"
proof -
  assume a:"A \<Longrightarrow> B"
  assume A 
  with a have B by (rule meta_mp)
qed
  
      
   