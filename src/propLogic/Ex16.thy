theory Ex16 
imports Main
begin 


(*Proof A \<or> B \<longleftrightarrow> B \<or> A, commutativity of or*) 


lemma "A \<or> B \<longleftrightarrow> B \<or> A"
proof -
{
  assume "A \<or> B"
  moreover
  { 
    assume A 
    hence "B \<or> A" by (rule disjI2)
  }
  moreover
  {
    assume B
    hence "B \<or> A" by (rule disjI1)
  }
  ultimately have "B \<or> A" by (rule disjE)
}
moreover
{
  assume "B \<or> A"
  moreover
  {
    assume B
    hence "A \<or> B" by (rule disjI2)
  }
  moreover
  { 
    assume A 
    hence "A \<or> B" by (rule disjI1)
  }
  ultimately have "A \<or> B" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed