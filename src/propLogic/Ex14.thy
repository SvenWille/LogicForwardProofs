theory Ex14
imports Main 
begin 

(*commutativity of "and"*)



lemma "A \<and> B \<longleftrightarrow> B \<and> A" 
proof - 
{
  assume "A \<and> B"
  hence A by (rule conjE)
  from \<open>A \<and> B\<close> have B  by (rule conjE)
  from this and  \<open>A\<close> have "B \<and> A" by (rule conjI) 
} (*A \<and> B \<Longrightarrow> B \<and> A*)
{
  assume "B \<and> A"
  hence A by (rule conjE)
  from \<open>B \<and> A\<close> have B  by (rule conjE)
  with  \<open>A\<close> have "A \<and> B" by (rule conjI) 
}
from  \<open>A \<and> B \<Longrightarrow> B \<and> A\<close> and this show ?thesis by (rule iffI)
qed


(*using moreover and ultimately to collect facts*)

lemma "A \<and> B \<longleftrightarrow> B \<and> A" 
proof - 
{
  assume "A \<and> B"
  hence A by (rule conjE)
  from \<open>A \<and> B\<close> have B  by (rule conjE)
  from this and  \<open>A\<close> have "B \<and> A" by (rule conjI) 
} (*A \<and> B \<Longrightarrow> B \<and> A*)
moreover
{
  assume "B \<and> A"
  hence A by (rule conjE)
  from \<open>B \<and> A\<close> have B  by (rule conjE)
  with  \<open>A\<close> have "A \<and> B" by (rule conjI) 
}
ultimately show ?thesis by (rule iffI)
qed

