theory Ex20 
imports Main 
begin 

(*distributivity of "or" over "and"*)
lemma "A \<or> (B \<and> C) \<longleftrightarrow> (A \<or> B) \<and> (A \<or> C)"
proof - 
{
  assume "A \<or> (B \<and> C)"
  {
    assume A 
    hence "A \<or> B" by (rule disjI1)
    from \<open>A\<close> have "A \<or> C" by (rule disjI1)
    with \<open>A \<or> B\<close> have "(A \<or> B) \<and> (A \<or> C)" by (rule conjI)
  }
  moreover 
  {
    assume "B \<and> C"
    hence C by (rule conjE)
    from \<open>B \<and> C\<close> have B by (rule conjE)
    hence "A \<or> B" by (rule disjI2)
    from \<open>C\<close> have "A \<or> C" by (rule disjI2)
    with \<open>A \<or> B\<close> have "(A \<or> B) \<and> (A \<or> C)" by (rule conjI)
  }
  from \<open>A \<or> (B \<and> C)\<close> and  calculation and this have " (A \<or> B) \<and> (A \<or> C)" by (rule disjE)
}
moreover
{
  assume "(A \<or> B) \<and> (A \<or> C)"
  hence "(A \<or> B)" by (rule conjE)
  from \<open>(A \<or> B) \<and> (A \<or> C)\<close> have "(A \<or> C)" by (rule conjE)
  {
    assume A 
    hence "A \<or> (B \<and> C)" by (rule disjI1)
  }
  moreover
  {
    assume C
    {
      assume A 
      hence "A \<or> (B \<and> C)" by (rule disjI1)
    }
    moreover
    {
      assume B
      from this and  \<open>C\<close> have "B \<and> C" by (rule conjI)
      hence  "A \<or> (B \<and> C)" by (rule disjI2)
    }
    from \<open>A \<or> B\<close> and  calculation and this  have "A \<or> (B \<and> C)" by (rule disjE)
  }
  from \<open>A \<or> C\<close> and calculation and this  have  "A \<or> (B \<and> C)" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed
