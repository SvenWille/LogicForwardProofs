theory Ex02
imports Main 
begin

lemma "A \<Longrightarrow> B \<Longrightarrow> A" by assumption


lemma "A \<Longrightarrow> B \<Longrightarrow> A" 
proof -
assume A
then show A by assumption (*then = from this*)
qed  


lemma "A \<longrightarrow> B \<longrightarrow> A" 
proof - 
{
  assume A 
  {
    assume B 
    from \<open>A\<close> have A by assumption (*the brackets \<open> (\open) \<close> (\close) make it possible to reference a fact without giving it a name prior*)
  }
  hence "B \<longrightarrow> A" by (rule impI) (*hence = from this have*)
}
thus ?thesis ..
qed 
(*thus = from this show*)(*?thesis refers to the lemma we want to proof*)(*the two dots mean "by rule", 
Isabelle often pics the right rule*)