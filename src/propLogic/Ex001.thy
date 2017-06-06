theory Ex001
imports Main 
begin


(*for forward proofs you (usually) add a "-" after "proof"*)


lemma  "A \<Longrightarrow> A" 
proof -
assume A
from this show A by assumption
qed


lemma assumes A shows A 
proof - 
from assms show A by assumption 
qed


(*or short version*)
lemma "A \<Longrightarrow> A" by assumption


(*using automation*)
lemma "A \<Longrightarrow> A" by auto 


lemma "A \<longrightarrow> A"
proof -
{ (*the brackets work like a "level" in a Fitch-style proof*)
  assume A
  from this have A  .(*the dot means: "by this"*)(*this actually isn't needed*)
} 
from this show ?thesis by (rule impI) (*?thesis is "the top level lemma"(what stands after "lemma") you want to proof: "A \<longrightarrow> A"*) 
qed


(*same as before but without the not needed line*)
lemma "A \<longrightarrow> A"
proof -
{ (*the brackets work like a "level" in a Fitch-style proof*)
  assume A
} 
from this show ?thesis by (rule impI) 
qed


lemma shows "A \<longrightarrow> A" 
proof - 
{ (*the brackets work like a "level" in a Fitch-style proof*)
  assume A
} 
from this show ?thesis by (rule impI) 
qed


(*using automation*)
lemma "A \<longrightarrow> A" by auto


