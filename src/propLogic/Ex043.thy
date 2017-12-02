theory Ex043 
  imports Main 
begin 
  
  
theorem "\<lbrakk>A \<and> B ; \<not>A \<or> C \<rbrakk> \<Longrightarrow> \<not>((A \<and> B) \<longrightarrow> \<not>C)" 
proof -
  assume a:"A \<and> B"
  and b:"\<not>A \<or> C"
  from a have A by (rule conjE)
  from a have B by (rule conjE)
  {
    assume "(A \<and> B) \<longrightarrow> \<not>C"
    from this and a have "\<not>C" by (rule mp)
    {
      assume "\<not>A" 
      with \<open>A\<close> have False by contradiction
    }
    note tmp=this
    {
      assume C
      with \<open>\<not>C\<close> have False by contradiction
    }
    from b and tmp and this have False by (rule disjE)
  }
  thus ?thesis by (rule notI)
qed