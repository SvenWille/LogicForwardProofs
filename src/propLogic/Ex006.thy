theory Ex006 
imports Main 
begin 


lemma "\<lbrakk> A \<or> B ; A \<or> C\<rbrakk> \<Longrightarrow> A \<or> (B \<and> C)"
proof -
assume "A \<or> B"
assume "A \<or> C"
{
  assume A
  from this have  "A \<or> (B \<and> C)" by (rule disjI1 )
}
moreover
{
  assume B
  {
    assume A
    from this have "A \<or> (B \<and> C)" by (rule disjI1)
  }
  moreover
  {
    assume C
    from  \<open>B\<close> and this  have "B \<and> C" by (rule conjI)
    from this have " A\<or>  (B \<and> C )" by (rule disjI2)
  }
  from  \<open>A \<or> C\<close> and calculation and this  have "A \<or> (B \<and> C)" by (rule disjE)
}
from \<open>A \<or> B\<close> and calculation and this show " A \<or> (B \<and> C)" by (rule disjE)
qed

(*prettified*) 

lemma assumes "A \<or> B" and "A \<or> C" shows "A \<or> (B \<and> C)"   
proof - 
{
  assume A
  hence "A \<or> (B \<and> C)" ..
}
moreover
{
  assume B
  {
    assume A
    hence "A \<or> (B \<and> C)" ..
  }
  moreover
  {
    assume C
    with  \<open>B\<close> have "B \<and> C" ..
    from this have " A\<or>  (B \<and> C )" ..
  }
  with  \<open>A \<or> C\<close> and calculation   have "A \<or> (B \<and> C)" ..
}
with \<open>A \<or> B\<close> and calculation  show " A \<or> (B \<and> C)" ..
qed