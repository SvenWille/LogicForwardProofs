# LogicForwardProofs

- scroll down for exercises in FOL (first order logic)  
- for original source code (using plain ascii instead of unicode) and alternative/other solutions have a look at the "src" folder  

##Propositional Logic

Proof the following theorems

**Exercise 1_1: A ⟹ A**
```Isabelle
lemma  "A ⟹ A" 
proof -
assume A
from this show A by assumption
qed
```
**Exercise 1_2: A ⟶ A**
```isabelle
lemma "A ⟶ A"
proof -
{ (*the brackets work like a "level" in a Fitch-style proof*)
  assume A
} 
from this show ?thesis by (rule impI) (*?thesis is the "top level lemma" you want to proof: "A ⟶ A"*) 
qed
```
**Exercise 2_1: A ⟹ B ⟹ A**

```isabelle 
lemma "A ⟹ B ⟹ A" 
proof -
assume A
then show A by assumption (*then = from this*)
qed  
```

**Exercise 2_2: A ⟶ B ⟶ A**

```isabelle 
lemma "A ⟶ B ⟶ A" 
proof - 
{
  assume A 
  {
    assume B 
    from ‹A› have A by assumption (*the brackets ‹ (\open) › (\close) make it possible to reference a fact without giving it a name prior*)
  }
  hence "B ⟶ A" by (rule impI) (*hence = from this have*)
}
thus ?thesis ..
qed 
(*thus = from this show*)(*?thesis refers to the lemma we want to proof*)
(*the two dots mean "by rule", Isabelle often pics the right rule*)
```

**Exercise 3: ¬A ⟶ A ⟶ B**

```isabelle 
lemma "¬A ⟶ A ⟶ B"
proof - 
{
  assume "¬A"
  {
    assume A
    with ‹¬A› have B by (rule notE)
  }
  hence "A ⟶ B" by (rule impI)
}
thus ?thesis by (rule impI)
qed
```

##First Order Logic

**Exercise 1: ⟦ P a ; Q a ⟧ ⟹ ∃x. P x ∧ Q x**

```Isabelle
lemma "⟦ P a ; Q a ⟧ ⟹ ∃x. P x ∧ Q x"
proof - 
assume "P a"
assume "Q a"
with ‹P a› have "P a ∧ Q a" by (rule conjI)
thus ?thesis by (rule exI)
qed
```