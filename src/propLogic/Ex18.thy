theory Ex18
imports Main 
begin 

(*associativity of or*)
lemma "(A \<or> B) \<or> C \<longleftrightarrow> A \<or> (B \<or> C)"
proof -
{
  assume "(A \<or> B) \<or> C"
  {
    assume "A \<or> B"
    {
      assume A 
      hence "A \<or> (B \<or> C)" by (rule disjI1)
    }
    moreover 
    {
      assume B
      hence "B \<or> C" by (rule disjI1)
      hence "A \<or> (B \<or> C)" by (rule disjI2)
    }
    from \<open>A \<or> B\<close> and calculation and this  have "A \<or> (B \<or> C)" by (rule disjE)
  }
  moreover
  {
    assume C 
    hence "B \<or> C" by (rule disjI2)
    hence "A \<or> (B \<or> C)" by (rule disjI2)
  }
  from \<open>(A \<or> B) \<or> C\<close> and calculation and this  have "A \<or> (B \<or> C)" by (rule disjE)
}
moreover
{
  assume "A \<or> (B \<or> C)"
  {
    assume A 
    hence "A \<or> B" by (rule disjI1)
    hence "(A \<or> B) \<or> C" by (rule disjI1)
  }
  moreover 
  {
    assume "B \<or> C"
    {
      assume B
      hence "A \<or> B" by (rule disjI2)
      hence "(A \<or> B) \<or> C" by (rule disjI1)
    }
    moreover
    {
      assume C
      hence "(A \<or> B) \<or> C" by (rule disjI2)
    }
    from \<open>B \<or> C\<close> and calculation and this have "(A \<or> B) \<or> C" by (rule disjE)
  }
  from \<open>A \<or> (B \<or> C)\<close> and calculation and this have "(A \<or> B) \<or> C" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed