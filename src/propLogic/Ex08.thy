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
      hence "\<not>A \<or> \<not>B" by (rule disjI1)
      with \<open>\<not>(\<not>A \<or> \<not>B)\<close> have  False by contradiction
    }
    hence "\<not>\<not>A" by (rule notI)
    hence A by (rule notnotD)
    {
      assume "\<not>B"
      hence "\<not>A \<or> \<not>B" by (rule disjI2)
      with  \<open>\<not>(\<not>A \<or> \<not>B)\<close> have False by contradiction
    }
    hence "\<not>\<not>B" by (rule notI)
    hence B by (rule notnotD)
    with \<open>A\<close> have "A \<and> B" by (rule conjI)
    with \<open>\<not>(A \<and> B)\<close> have False by contradiction
  }
  hence " \<not>\<not> (\<not> A \<or> \<not> B)" by (rule notI)
  hence  "\<not> A \<or> \<not> B" by (rule notnotD)
}
thus ?thesis by (rule impI)
qed


(*prettified*)
 

lemma "\<not>(A \<and> B) \<longrightarrow> (\<not>A \<or> \<not>B)"
proof -
{
  assume "\<not>(A \<and> B)"
  {
    assume "\<not>(\<not>A \<or> \<not>B)"
    {
      assume "\<not>A"
      hence "\<not>A \<or> \<not>B" ..
      with \<open>\<not>(\<not>A \<or> \<not>B)\<close> have  False ..
    }
    hence "\<not>\<not>A" ..
    hence A by (rule notnotD)
    {
      assume "\<not>B"
      hence "\<not>A \<or> \<not>B" ..
      with  \<open>\<not>(\<not>A \<or> \<not>B)\<close> have False ..
    }
    hence "\<not>\<not>B" ..
    hence B by (rule notnotD)
    with \<open>A\<close> have "A \<and> B" ..
    with \<open>\<not>(A \<and> B)\<close> have False ..
  }
  hence " \<not>\<not> (\<not> A \<or> \<not> B)"..
  hence  "\<not> A \<or> \<not> B" by (rule notnotD)
}
thus ?thesis ..
qed