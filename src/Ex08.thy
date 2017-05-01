theory Ex08
imports Main 
begin 




lemma "\<not>(A \<and> B) \<longrightarrow> (\<not>A \<or> \<not>B)"
proof -
{
  assume "\<not>(A \<and> B)"
  {
    assume "\<not>(\<not>A \<or> \<not>B)"
    {
      assume "\<not>A"
    }