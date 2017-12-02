theory ExF016
  imports Main 
begin 
  
lemma "(\<exists>x. (P x \<longrightarrow> \<not>P(F x))) \<longrightarrow> (\<exists>x. \<not>P x)" 
proof -
  {
    assume a:"\<exists>x. (P x \<longrightarrow> \<not>P(F x))"
    {
      assume b:"\<not>(\<exists>x . \<not>P x )"
      {
        fix aa
        assume c:"P aa \<longrightarrow> \<not>P(F aa)"
        {
          assume "P aa"
          with c have "\<not>P (F aa)" by (rule mp)
          hence "\<exists>x. \<not>P (x)" by (rule exI)
          with b have False by contradiction
        }
        hence "\<not>P aa" by (rule notI)
        hence "\<exists>x. \<not>P x" by (rule exI)
        with b have False by contradiction
      }
      with a have False by (rule exE)
    }
    hence "\<not>\<not>(\<exists>x . \<not>P x )" by (rule notI)
    hence "\<exists>x . \<not>P x " by (rule notnotD)
  }
  thus ?thesis by (rule impI)
qed
  