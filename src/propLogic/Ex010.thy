theory Ex010 
imports Main 
begin 


lemma "A \<or> \<not>False"
proof -
{
  assume False
}
hence "\<not>False" by (rule notI)
thus "A \<or> \<not>False" by (rule disjI2)
qed

(*prettified*)

lemma "A \<or> \<not>False"
proof -
{
  assume False
}
hence "\<not>False" ..
thus "A \<or> \<not>False" ..
qed