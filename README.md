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

**Exercise 8: ¬(A ∧ B) ⟶ (¬A ∨ ¬B)**

```isabelle
lemma "¬(A ∧ B) ⟶ (¬A ∨ ¬B)"
proof -
{
  assume "¬(A ∧ B)"
  {
    assume "¬(¬A ∨ ¬B)"
    {
      assume "¬A"
      hence "¬A ∨ ¬B" by (rule disjI1)
      with ‹¬(¬A ∨ ¬B)› have  False by contradiction
    }
    hence "¬¬A" by (rule notI)
    hence A by (rule notnotD)
    {
      assume "¬B"
      hence "¬A ∨ ¬B" by (rule disjI2)
      with  ‹¬(¬A ∨ ¬B)› have False by contradiction
    }
    hence "¬¬B" by (rule notI)
    hence B by (rule notnotD)
    with ‹A› have "A ∧ B" by (rule conjI)
    with ‹¬(A ∧ B)› have False by contradiction
  }
  hence " ¬¬ (¬ A ∨ ¬ B)" by (rule notI)
  hence  "¬ A ∨ ¬ B" by (rule notnotD)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 9: ¬C ⟶ A ∨ ((A ∨ C) ⟶ B)**

```isabelle
lemma " ¬C ⟶ A ∨ ((A ∨ C) ⟶ B)"
proof - 
{
  assume "¬C"
  {
    assume "¬(A ∨ ((A ∨ C) ⟶ B))"
    {
      assume "A ∨ C"
      {
        assume A
        hence "A ∨ ((A ∨ C) ⟶ B)" by (rule disjI1)
        with ‹¬(A ∨ ((A ∨ C) ⟶ B))› have False by contradiction
        hence B by (rule FalseE)
      }
      {
        assume C
        with ‹¬C› have False by contradiction
        hence B by (rule FalseE)
      }
      with ‹A ∨ C›  and  ‹A ⟹ B› have B by (rule disjE)
    }
    hence "A ∨ C ⟶ B" by (rule impI)
    hence "A ∨ (A ∨ C ⟶ B)" by (rule disjI2)
    with ‹¬(A ∨ ((A ∨ C) ⟶ B))› have False by contradiction
  }
  hence "¬¬(A ∨ ((A ∨ C) ⟶ B))" by (rule notI)
  hence "A ∨ ((A ∨ C) ⟶ B)" by (rule notnotD)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 10: A ∨ ¬False**

```isabelle
lemma "A ∨ ¬False"
proof -
{
  assume False
}
hence "¬False" by (rule notI)
thus "A ∨ ¬False" by (rule disjI2)
qed

(*prettified*)

lemma "A ∨ ¬False"
proof -
{
  assume False
}
hence "¬False" ..
thus "A ∨ ¬False" ..
qed
```

**Exercise 11: (A ∧ ¬A) ⟶ B**

```isabelle
lemma "(A ∧ ¬A) ⟶ B" 
proof - 
{
  assume "A ∧ ¬A"
  hence A by (rule conjE)
  from ‹A ∧ ¬A› have "¬A" by (rule conjE)
  with ‹A› have B by contradiction
}
thus ?thesis by (rule impI)
qed
```

**Exercise 12: A ⟶ (A ∨ B)**

```isabelle
lemma "A ⟶ (A ∨ B)"
proof -
{
  assume A
  hence "A ∨ B" by (rule disjI1)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 13: (A ⟶ B) ⟶ (¬B ⟶ ¬A)**

```isabelle
lemma "(A ⟶ B) ⟶ (¬B ⟶ ¬A)"
proof - 
{
  assume "A ⟶ B"
  {
    assume "¬B"
    {
      assume A 
      with ‹A ⟶ B› have B by (rule impE)
      with ‹¬B› have False by contradiction
    }
    hence "¬A" by (rule notI)
  }
  hence "¬B ⟶ ¬A" by (rule impI)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 14: A ∧ B ⟷ B ∧ A**

```isabelle
(*using moreover and ultimately to collect facts*)

lemma "A ∧ B ⟷ B ∧ A" 
proof - 
{
  assume "A ∧ B"
  hence A by (rule conjE)
  from ‹A ∧ B› have B  by (rule conjE)
  from this and  ‹A› have "B ∧ A" by (rule conjI) 
} (*A ∧ B ⟹ B ∧ A*)
moreover
{
  assume "B ∧ A"
  hence A by (rule conjE)
  from ‹B ∧ A› have B  by (rule conjE)
  with  ‹A› have "A ∧ B" by (rule conjI) 
}
ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 15: (A ⟶ B) ⟶ A ⟶ A ∧ B**

```isabelle
lemma "(A ⟶ B) ⟶ A ⟶ A ∧ B"
proof -
{
  assume "A ⟶ B"
  {
    assume A 
    with ‹A ⟶ B› have B by (rule impE)
    with ‹A› have "A ∧ B" by (rule conjI)
  }
  hence "A ⟶ A ∧ B" by (rule impI)
}
thus ?thesis by (rule impI)
qed
```

**Exercise 16: A ∨ B ⟷ B ∨ A**

```isabelle 
lemma "A ∨ B ⟷ B ∨ A"
proof -
{
  assume "A ∨ B"
  moreover
  { 
    assume A 
    hence "B ∨ A" by (rule disjI2)
  }
  moreover
  {
    assume B
    hence "B ∨ A" by (rule disjI1)
  }
  ultimately have "B ∨ A" by (rule disjE)
}
moreover
{
  assume "B ∨ A"
  moreover
  {
    assume B
    hence "A ∨ B" by (rule disjI2)
  }
  moreover
  { 
    assume A 
    hence "A ∨ B" by (rule disjI1)
  }
  ultimately have "A ∨ B" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 17: (A ∧ B)∧ C ⟷ A ∧ (B ∧ C)**

```isabelle
lemma "(A ∧ B)∧ C ⟷ A ∧ (B ∧ C)"
proof - 
{ 
  assume "(A ∧ B) ∧ C"
  hence "A ∧ B" by (rule conjE)
  hence A by (rule conjE)
  from ‹A ∧ B› have B by (rule conjE)
  from ‹(A ∧ B) ∧ C› have C by (rule conjE)
  with ‹B› have "B ∧ C" by (rule conjI)
  with ‹A› have "A ∧ (B ∧ C)" by (rule conjI)
}
moreover  
{
  assume " A ∧ (B ∧ C)"
  hence "B ∧ C" by (rule conjE)
  hence B by (rule conjE)
  from ‹B ∧ C› have C by (rule conjE)
  from ‹A ∧ (B ∧ C)› have A by (rule conjE)
  from ‹A› and ‹B› have "A ∧ B" by (rule conjI)
  from this and ‹C› have "(A ∧ B) ∧ C" by (rule conjI)
}

thm iffI
ultimately show ?thesis by (rule iffI) 
qed 
```

**Exercise 18: (A ∨ B) ∨ C ⟷ A ∨ (B ∨ C)**

```isabelle
lemma "(A ∨ B) ∨ C ⟷ A ∨ (B ∨ C)"
proof -
{
  assume "(A ∨ B) ∨ C"
  {
    assume "A ∨ B"
    {
      assume A 
      hence "A ∨ (B ∨ C)" by (rule disjI1)
    }
    moreover 
    {
      assume B
      hence "B ∨ C" by (rule disjI1)
      hence "A ∨ (B ∨ C)" by (rule disjI2)
    }
    from ‹A ∨ B› and calculation and this  have "A ∨ (B ∨ C)" by (rule disjE)
  }
  moreover
  {
    assume C 
    hence "B ∨ C" by (rule disjI2)
    hence "A ∨ (B ∨ C)" by (rule disjI2)
  }
  from ‹(A ∨ B) ∨ C› and calculation and this  have "A ∨ (B ∨ C)" by (rule disjE)
}
moreover
{
  assume "A ∨ (B ∨ C)"
  {
    assume A 
    hence "A ∨ B" by (rule disjI1)
    hence "(A ∨ B) ∨ C" by (rule disjI1)
  }
  moreover 
  {
    assume "B ∨ C"
    {
      assume B
      hence "A ∨ B" by (rule disjI2)
      hence "(A ∨ B) ∨ C" by (rule disjI1)
    }
    moreover
    {
      assume C
      hence "(A ∨ B) ∨ C" by (rule disjI2)
    }
    from ‹B ∨ C› and calculation and this have "(A ∨ B) ∨ C" by (rule disjE)
  }
  from ‹A ∨ (B ∨ C)› and calculation and this have "(A ∨ B) ∨ C" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed
``` 

**Exercise 19: A ∧ (B ∨ C) ⟷ (A ∧ B) ∨ (A ∧ C)**

```isabelle
lemma "A ∧ (B ∨ C) ⟷ (A ∧ B) ∨ (A ∧ C)"
proof - 
{
  assume "A ∧ (B ∨ C)"
  hence A by (rule conjE)
  from ‹A ∧ (B ∨ C)› have "B ∨ C" by (rule conjE)
  {
    assume B
    with  ‹A› have "A ∧ B" by (rule conjI)
    hence "(A ∧ B) ∨ (A ∧ C)" by (rule disjI1)
  }
  moreover
  {
    assume C
    with ‹A› have "A ∧ C" by (rule conjI)
    hence "(A ∧ B) ∨ (A ∧ C)" by (rule disjI2)
  }
  from ‹B ∨ C› and calculation and this have "(A ∧ B) ∨ (A ∧ C)" by (rule disjE)
}
moreover
{
  assume "(A ∧ B) ∨ (A ∧ C)"
  {
    assume "A ∧ B"
    hence A by (rule conjE)
    from ‹A ∧ B› have B by (rule conjE)
    hence "B ∨ C" by (rule disjI1)
    with ‹A› have "A ∧ (B ∨ C)" by (rule conjI)
  }
  moreover 
  {
    assume "A ∧ C"
    hence A by (rule conjE)
    from ‹A ∧ C› have C by (rule conjE)
    hence "B ∨ C" by (rule disjI2)
    with ‹A› have "A ∧ (B ∨ C)" by (rule conjI)
  }
  from ‹(A ∧ B) ∨ (A ∧ C)› and calculation and this have "A ∧ (B ∨ C)" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 20: A ∨ (B ∧ C) ⟷ (A ∨ B) ∧ (A ∨ C)**

```isabelle
lemma "A ∨ (B ∧ C) ⟷ (A ∨ B) ∧ (A ∨ C)"
proof - 
{
  assume "A ∨ (B ∧ C)"
  {
    assume A 
    hence "A ∨ B" by (rule disjI1)
    from ‹A› have "A ∨ C" by (rule disjI1)
    with ‹A ∨ B› have "(A ∨ B) ∧ (A ∨ C)" by (rule conjI)
  }
  moreover 
  {
    assume "B ∧ C"
    hence C by (rule conjE)
    from ‹B ∧ C› have B by (rule conjE)
    hence "A ∨ B" by (rule disjI2)
    from ‹C› have "A ∨ C" by (rule disjI2)
    with ‹A ∨ B› have "(A ∨ B) ∧ (A ∨ C)" by (rule conjI)
  }
  from ‹A ∨ (B ∧ C)› and  calculation and this have " (A ∨ B) ∧ (A ∨ C)" by (rule disjE)
}
moreover
{
  assume "(A ∨ B) ∧ (A ∨ C)"
  hence "(A ∨ B)" by (rule conjE)
  from ‹(A ∨ B) ∧ (A ∨ C)› have "(A ∨ C)" by (rule conjE)
  {
    assume A 
    hence "A ∨ (B ∧ C)" by (rule disjI1)
  }
  moreover
  {
    assume C
    {
      assume A 
      hence "A ∨ (B ∧ C)" by (rule disjI1)
    }
    moreover
    {
      assume B
      from this and  ‹C› have "B ∧ C" by (rule conjI)
      hence  "A ∨ (B ∧ C)" by (rule disjI2)
    }
    from ‹A ∨ B› and  calculation and this  have "A ∨ (B ∧ C)" by (rule disjE)
  }
  from ‹A ∨ C› and calculation and this  have  "A ∨ (B ∧ C)" by (rule disjE)
}
ultimately show ?thesis by (rule iffI)
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

**Exercise 4: (∀x. ∃y. P x y) ∨ (∃x. ∀y. ¬P x y)**

```isabelle
```

**Exercise 5: (∀x . (P x ∧ Q x)) ⟶ ((∀x . P x) ∧ (∀ x . Q x))**

```isabelle
lemma "(∀x . (P x ∧ Q x)) ⟶ ((∀x . P x) ∧ (∀ x . Q x))"
proof - 
  {    
    assume "∀x . (P x ∧ Q x)"
    {
      fix a
      from ‹∀x . (P x ∧ Q x)› have "P a ∧ Q a" by (rule allE)
      hence "P a" by (rule conjE)
    }
    hence "∀x . P x" by (rule allI)
    {    
      fix a
      from ‹∀x . (P x ∧ Q x)› have "P a ∧ Q a" by (rule allE)
      hence "Q a" by (rule conjE)
    }
    hence "∀x . Q x" by (rule allI)
    with ‹∀x . P x› have "(∀x . P x) ∧ (∀ x . Q x)" by (rule conjI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 6: (∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)**

```isabelle

```