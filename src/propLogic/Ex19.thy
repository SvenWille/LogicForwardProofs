theory Ex19 
imports Main 
begin 

(*distributivity of "and" over "or"*)
lemma "A \<and> (B \<or> C) \<longleftrightarrow> (A \<and> B) \<or> (A \<and> C)"
proof - 
{
  assume "A \<and> (B \<or> C)"
  hence A by (rule conjE)
  from \<open>A \<and> (B \<or> C)\<close> have "B \<or> C" by (rule conjE)
  {
    assume B
    with  \<open>A\<close> have "A \<and> B" by (rule conjI)
    hence "(A \<and> B) \<or> (A \<and> C)" by (rule disjI1)
  }
  moreover
  {
    assume C
    with \<open>A\<close> have "A \<and> C" by (rule conjI)
    hence "(A \<and> B) \<or> (A \<and> C)" by (rule disjI2)
  }
  from \<open>B \<or> C\<close> and calculation and this have "(A \<and> B) \<or> (A \<and> C)" by (rule disjE)
}
moreover
{
  assume "(A \<and> B) \<or> (A \<and> C)"
  {
    assume "A \<and> B"
    hence A by (rule conjE)
    from \<open>A \<and> B\<close> have B by (rule conjE)
    hence "B \<or> C" by (rule disjI1)
    with \<open>A\<close> have "A \<and> (B \<or> C)" by (rule conjI)
  }
  moreover 
  {
    assume "A \<and> C"
    hence A by (rule conjE)
    from \<open>A \<and> C\<close> have C by (rule conjE)
    hence "B \<or> C" by (rule disjI2)
    with \<open>A\<close> have "A \<and> (B \<or> C)" by (rule conjI)
  }
  from \<open>(A \<and> B) \<or> (A \<and> C)\<close> and calculation and this have "A \<and> (B \<or> C)" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed