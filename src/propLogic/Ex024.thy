theory Ex024 
  imports Main 
begin 
  

  
  
lemma "(A \<longleftrightarrow> B) \<longleftrightarrow> (\<not>A \<longleftrightarrow> \<not>B)"
proof -
  {
    assume a:"A \<longleftrightarrow> B"
    hence b:"A \<longrightarrow> B" by (rule iffE)
    from a have c:"B \<longrightarrow> A" by (rule iffE)
    {
      assume d:"\<not>A"
      {
        assume B
        with c have A by (rule mp)
        with d have False by contradiction
      }
      hence "\<not>B" by (rule notI)
    }
    moreover
    {
      assume e:"\<not>B"
      {
        assume A
        with b have B by (rule mp)
        with e have False by contradiction
      }
      hence "\<not>A" by (rule notI)
    }
    ultimately have "\<not>A \<longleftrightarrow> \<not>B" by (rule iffI)
  }
  moreover
  {
    assume f:"\<not>A \<longleftrightarrow> \<not>B"
    hence g:"\<not>A \<longrightarrow> \<not>B" by (rule iffE)
    from f have h:"\<not>B \<longrightarrow> \<not>A" by (rule iffE)
    {
      assume i:A 
      {
        assume "\<not>B"
        with h have "\<not>A" by (rule mp)
        with i have False by contradiction
      }
      hence "\<not>\<not>B" by (rule notI)
      hence B by (rule notnotD)
    }
    moreover
    {
      assume j:B
      {
        assume "\<not>A"
        with g have "\<not>B" by (rule mp)
        with j have False by contradiction
      }
      hence "\<not>\<not>A" by (rule notI)
      hence A by (rule notnotD)
    }
    ultimately have "A \<longleftrightarrow> B" by (rule iffI)
  }
  ultimately show ?thesis by (rule iffI)
qed
  
          
     
          