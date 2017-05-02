theory Ex12
imports Main 
begin 


lemma "A \<longrightarrow> (A \<or> B)"
proof -
{
  assume A
  hence "A \<or> B" by (rule disjI1)
}
thus ?thesis by (rule impI)
qed