theory ExF018 
  imports Main 
begin 
  
lemma "(\<forall>x. \<forall>y. (P x \<longleftrightarrow> P y)  \<longrightarrow> (x \<longleftrightarrow> y)) \<Longrightarrow> (\<forall>x. \<forall>y. (x \<longleftrightarrow> y) \<longrightarrow> (P x \<longleftrightarrow> P y)) \<Longrightarrow> (\<forall>x. P (P x) \<longleftrightarrow> x)" 
proof -
  {
    assume "(\<forall>x. \<forall>y. (P x \<longleftrightarrow> P y)  \<longrightarrow> (x \<longleftrightarrow> y))"
    {
      assume "(\<forall>x. \<forall>y. (x \<longleftrightarrow> y) \<longrightarrow> (P x \<longleftrightarrow> P y))" 
      {
        assume "\<forall>x. P (P x)" 
        {
          