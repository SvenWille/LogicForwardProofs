theory Ex17 
imports Main 
begin 


(*associativity of and *)
lemma "(A \<and> B)\<and> C \<longleftrightarrow> A \<and> (B \<and> C)"
proof - 
{ 
  assume "(A \<and> B) \<and> C"
  hence "A \<and> B" by (rule conjE)
  hence A by (rule conjE)
  from \<open>A \<and> B\<close> have B by (rule conjE)
  from \<open>(A \<and> B) \<and> C\<close> have C by (rule conjE)
  with \<open>B\<close> have "B \<and> C" by (rule conjI)
  with \<open>A\<close> have "A \<and> (B \<and> C)" by (rule conjI)
}
moreover  
{
  assume " A \<and> (B \<and> C)"
  hence "B \<and> C" by (rule conjE)
  hence B by (rule conjE)
  from \<open>B \<and> C\<close> have C by (rule conjE)
  from \<open>A \<and> (B \<and> C)\<close> have A by (rule conjE)
  from \<open>A\<close> and \<open>B\<close> have "A \<and> B" by (rule conjI)
  from this and \<open>C\<close> have "(A \<and> B) \<and> C" by (rule conjI)
}

thm iffI
ultimately show ?thesis by (rule iffI) 
qed 