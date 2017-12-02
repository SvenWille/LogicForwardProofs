theory Ex044 
  imports Main 
begin 
  
theorem "\<lbrakk>\<not>(\<not>(A \<longrightarrow> B) \<and> \<not>B) ; \<not>C \<longrightarrow> A \<rbrakk> \<Longrightarrow> C \<or> B" 
proof - 
  assume a:"\<not>(\<not>(A \<longrightarrow> B) \<and> \<not>B)"
  and b:"\<not>C \<longrightarrow> A"
  {
    assume c:"\<not>(C \<or> B)"
    {
      assume d:"\<not>C"
      {
        assume e:"\<not>B"
        {
          assume f:"A \<longrightarrow> B"
          from b d have A by (rule mp)
          with f have B by (rule mp)
          with e have False by contradiction
        }
        hence "\<not>(A \<longrightarrow> B)" by (rule notI)
        from this e have "\<not>(A \<longrightarrow> B) \<and> \<not>B" by (rule conjI)
        with a have False by (rule notE)
      }
      hence "\<not>\<not>B" by (rule notI)
      hence B by (rule notnotD)
      hence "C \<or> B" by (rule disjI2)
      with c have False by (rule notE)
    }
    hence "\<not>\<not>C" by (rule notI)
    hence C by (rule notnotD)
    hence "C \<or> B" by (rule disjI1)
    with c have False by (rule notE)
  }
  hence "\<not>\<not> (C \<or> B)" by (rule notI)
  thus "C \<or> B" by (rule notnotD)
qed

