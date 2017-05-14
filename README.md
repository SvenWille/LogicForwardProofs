# LogicForwardProofs

- scroll down for exercises in FOL (first order logic)  
- for original source code (using plain ascii instead of unicode) and alternative/other solutions have a look at the "src" folder  

## Propositional Logic

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

**Exercise 4: (A ⟶ (B ∧ C)) ⟶ (A ⟶ B)**
```isabelle
lemma  "(A ⟶ (B ∧ C)) ⟶ (A ⟶ B)"
proof - 
{
  assume "A ⟶ (B ∧ C)"
  {
    assume "A"
    with ‹A ⟶ (B ∧ C)› have "B ∧ C" by (rule impE)
    hence B by (rule conjE)
  }
  hence "A ⟶ B" by (rule impI)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 5: (A ∧ (B ⟶ ¬A)) ⟶ (A ∧ ¬B)**

```isabelle
lemma "(A ∧ (B ⟶ ¬A)) ⟶ (A ∧ ¬B)"
proof -
{
  assume "A ∧ (B ⟶ ¬A)"
  hence "B ⟶ ¬A" by (rule conjE)
  from ‹A ∧ (B ⟶ ¬A)› have A by (rule conjE)
  {
    assume B
    with ‹B ⟶ ¬A› have "¬A" by (rule impE)
    with ‹A›  have False by contradiction
  }
  hence "¬B" by (rule notI)
  with ‹A› have "A ∧ ¬B" by (rule conjI)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 6: ⟦ A ∨ B ; A ∨ C⟧ ⟹ A ∨ (B ∧ C)**

```isabelle
lemma "⟦ A ∨ B ; A ∨ C⟧ ⟹ A ∨ (B ∧ C)"
proof -
assume "A ∨ B"
assume "A ∨ C"
{
  assume A
  from this have  "A ∨ (B ∧ C)" by (rule disjI1 )
}
moreover
{
  assume B
  {
    assume A
    from this have "A ∨ (B ∧ C)" by (rule disjI1)
  }
  moreover
  {
    assume C
    from  ‹B› and this  have "B ∧ C" by (rule conjI)
    from this have " A∨  (B ∧ C )" by (rule disjI2)
  }
  from  ‹A ∨ C› and calculation and this  have "A ∨ (B ∧ C)" by (rule disjE)
}
from ‹A ∨ B› and calculation and this show " A ∨ (B ∧ C)" by (rule disjE)
qed
```

**Exercise 7: (( A ⟶ B) ⟶ A) ⟶ A**

```isabelle
lemma "(( A ⟶ B) ⟶ A) ⟶ A" 
proof - 
{
  assume "(A ⟶ B) ⟶ A"
  {
    assume a:"¬A"
    {
      assume A
      with a have B by contradiction
    }
    hence "A ⟶ B" by (rule impI)
    with ‹(A ⟶ B) ⟶ A› have A by (rule impE)
    with ‹¬A› have False by contradiction
  }
  hence "¬¬A" by (rule notI)
  hence A by (rule notnotD)
}
thus ?thesis by (rule impI)
qed
```

## First Order Logic

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

**Exercise 2:  ⟦ ∀x.(P x ⟶ Q x) ; P a ⟧ ⟹ Q a**
```isabelle
lemma "⟦ ∀x.(P x ⟶ Q x) ; P a ⟧ ⟹ Q a"
proof - 
assume "∀x.(P x ⟶ Q x)"
assume "P a"
from ‹∀x.(P x ⟶ Q x)› have "P a ⟶ Q a" by (rule allE)
from this and  ‹P a› show ?thesis by (rule impE) 
qed
```

**Exercise 3: (∀x. P x ⟶ P(Q x)) ∧ P a ⟶ P (Q (Q a))**

```isabelle
lemma "(∀x. P x ⟶ P(Q x)) ∧ P a ⟶ P (Q (Q a))" 
proof - 
{
  assume "(∀x. P x ⟶ P(Q x)) ∧ P a"
  hence "∀x. P x ⟶ P(Q x)" by (rule conjE)
  from ‹(∀x. P x ⟶ P(Q x)) ∧ P a› have "P a" by (rule conjE)
  from  ‹(∀x. P x ⟶ P(Q x))› have "P a ⟶ P(Q a)" by (rule allE)
  from this and ‹P a› have "P (Q a)" by (rule impE)
  from  ‹(∀x. P x ⟶ P(Q x))› have "P (Q a) ⟶ P (Q (Q a))" by (rule allE)
  from this and ‹P (Q a)› have " P (Q (Q a))" by (rule impE)
}
thus ?thesis by (rule impI)
qed
```