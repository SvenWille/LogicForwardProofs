theory Ex01
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
  assume a:A
  from this have A by assumption (*this actually isn't needed*)
} 
from this show ?thesis by (rule impI) (*?thesis is whats you want to proof: "A \<longrightarrow> A"*) 
qed


(*same as before but without the not needed line*)
lemma "A \<longrightarrow> A"
proof -
{ (*the brackets work like a "level" in a Fitch-style proof*)
  assume a:A
} 
from this show ?thesis by (rule impI) (*?thesis is whats you want to proof: "A \<longrightarrow> A"*) 
qed


lemma shows "A \<longrightarrow> A" 
proof - 
{ (*the brackets work like a "level" in a Fitch-style proof*)
  assume a:A
} 
from this show ?thesis by (rule impI) (*?thesis is whats you want to proof: "A \<longrightarrow> A"*) 
qed


(*using automation*)
lemma "A \<longrightarrow> A" by auto


