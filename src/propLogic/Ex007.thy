theory Ex007 
imports Main
begin 

(*Peirce's Law*)


lemma "(( A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A" 
proof - 
{
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  {
    assume a:"\<not>A"
    {
      assume A
      with a have B by contradiction
    }
    hence "A \<longrightarrow> B" by (rule impI)
    with \<open>(A \<longrightarrow> B) \<longrightarrow> A\<close> have A by (rule impE)
    with \<open>\<not>A\<close> have False by contradiction
  }
  hence "\<not>\<not>A" by (rule notI)
  hence A by (rule notnotD)
}
thus ?thesis by (rule impI)
qed


(*slightly prettified*)


lemma "(( A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A" 
proof - 
{
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  {
    assume a:"\<not>A"
    {
      assume A
      with a have B ..
    }
    hence "A \<longrightarrow> B" ..
    with \<open>(A \<longrightarrow> B) \<longrightarrow> A\<close> have A ..
    with \<open>\<not>A\<close> have False ..
  }
  hence "\<not>\<not>A" ..
  hence A by (rule notnotD)
}
thus ?thesis ..
qed

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof -
  {
    assume a:"((A \<longrightarrow> B) \<longrightarrow> A)"
    {
      assume b:"\<not>A"
      {
        assume c:A
        {
          assume "\<not>B"
          from b and c have False by contradiction
        }
        hence "\<not>\<not>B" by (rule notI)
        hence B by (rule notnotD)
      }
      hence "A \<longrightarrow> B" by (rule impI)
      with a have A by (rule mp)
      with b have False by contradiction
    }
    hence "\<not>\<not>A" by (rule notI)
    hence A by (rule notnotD)
  }
  thus "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A" by (rule impI)
qed