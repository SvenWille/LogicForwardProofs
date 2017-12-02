# LogicForwardProofs

- scroll down for exercises in FOL (first order logic)  
- for original source code (using plain ascii instead of unicode) and alternative/other solutions have a look at the "src" folder 

#### Number of exercises

Propositional logic: 46  
First order logic: 17
 
#### Important Rules and Proof-Methods

impI = implication introduction  
mp = modus ponens (also implication elimination)  
impE = implication elimination  
conjI = conjunction/and introduction  
conjE =conjunction/and elimination  
disjI1 =disjunction/or introduction (where a new the right side or "or" is added: A => A \/ B)  
disjI2 = like disjI1 but positions swapped  
disjE = disjunction/or elimination  
exI = existential introduction  
exE = existential elimination  
allI = all introduction  
allE = all elimination  
assumption = uses a hypothesis to proof the goal
FalseE = false elemination, i.e. from false one can conclude anything
notE = proof by contradiction

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

**Exercise 21: (A ⟷ B)  ⟷ (A ∧ B) ∨ (¬A ∧ ¬B)**

```isabelle
lemma "(A ⟷ B)  ⟷ (A ∧ B) ∨ (¬A ∧ ¬B)" 
proof -
  {
    assume a:"A ⟷ B"
    hence b:"A ⟶ B" by (rule iffE)
    from a have c:"B ⟶ A" by (rule iffE)
    {
      assume d:"¬ ((A ∧ B) ∨  (¬A ∧ ¬B))"
      {
        assume e:A 
        with b have B by (rule mp)
        with e have "A ∧ B" by (rule conjI)
        hence "(A ∧ B) ∨ (¬A ∧ ¬B)" by (rule disjI1)
        with d have False by contradiction
      }
      hence f:"¬A" by (rule notI)
      {
        assume g:B 
        with c have A by (rule mp)
        from this and  g have "A ∧ B" by (rule conjI)
        hence "(A ∧ B) ∨ (¬A ∧ ¬B)" by (rule disjI1)
        with d have False by contradiction
      }
      hence h:"¬B" by (rule notI)
      from f and h have "¬A ∧ ¬B" by (rule conjI)
      hence "(A ∧ B) ∨  (¬A ∧ ¬B)" by (rule disjI2)
      with d have False by contradiction
    }
    hence "¬¬ ((A ∧ B) ∨  (¬A ∧ ¬B))" by (rule notI)
    hence "(A ∧ B) ∨  (¬A ∧ ¬B)" by (rule notnotD)
  }
  moreover
  {
    assume a:"(A ∧ B) ∨ (¬A ∧ ¬B)" 
    {
      assume b:"A ∧ B"
      hence c:A by (rule conjE)
      from b have d:B by (rule conjE)
      {
        assume A 
        have B by (rule d)
      }
      moreover
      {
        assume B 
        have A by (rule c)
      }
      ultimately have "A ⟷ B" by (rule iffI)
    }
    note d=this 
    {
      assume e:"¬A ∧ ¬B" 
      hence f:"¬A" by (rule conjE)
      from e have g:"¬B" by (rule conjE)          
      {
        assume h:"¬(A ⟶ B)"
        {
          assume A 
          with f have False by contradiction
          hence B by (rule FalseE)
        }
        hence "A ⟶ B" by (rule impI)
        with h have False by contradiction
      }
      hence "¬¬(A ⟶ B)" by (rule notI)
      hence i:"A ⟶ B" by (rule notnotD)
      {
        assume A 
        with i have B by(rule mp)
      }
      moreover
      {
        assume j:"¬(B ⟶ A)"
        {
          assume B
          with g have False by contradiction
          hence A by (rule FalseE)
        }
        hence " B ⟶ A" by (rule impI)
        with j have False by contradiction
      }
      hence "¬¬(B ⟶ A)" by (rule notI)
      hence k:"B ⟶ A" by (rule notnotD)
      {
        assume B 
        with k have A by (rule mp)
      }
        ultimately have "A ⟷ B" by (rule iffI)
    }
    from a and d and this have "A ⟷ B" by (rule disjE)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 22: (A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C)**

```isabelle
lemma "(A ⟶ B) ⟶ (A ⟶ B ⟶ C) ⟶ (A ⟶ C)" 
proof -
  {
    assume "A ⟶ B"
    {
      assume "A ⟶ B ⟶ C"
      {
        assume A 
        with ‹A ⟶ B› have B by (rule mp)
        from ‹A ⟶ B ⟶ C› and ‹A› have "B ⟶ C" by (rule mp)
        from ‹B ⟶ C› and ‹B› have C by (rule mp)
      }
      hence "A ⟶ C" by (rule impI)
    }
    hence "(A ⟶ B ⟶ C) ⟶ A ⟶ C" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```
**Exercise 23: (A ⟶ B)  ⟷ (¬A ∨ B)**

```isabelle
lemma "(A ⟶ B)  ⟷ (¬A ∨ B)" 
proof -
  {
    assume a:"A ⟶ B"
    {
      assume b:"¬(¬A ∨ B)"
      {
        assume A 
        with a have B by (rule mp)
        hence "¬A ∨ B" by (rule disjI2)
        with b have False by contradiction
      }
      hence "¬A" by (rule notI)
      hence "¬A ∨ B" by (rule disjI1)
      with b have False by contradiction
    }
    hence "¬¬(¬A ∨ B)" by (rule notI)
    hence "¬A ∨ B" by (rule notnotD)
  }
  moreover
  {
    assume c:"¬A ∨ B" 
    {
      assume d:"¬(A ⟶ B)"
      {
        assume e:A 
        {
          assume "¬A"
          with e have False by contradiction
        }
        note f=this
        {
          assume g:B 
          {
            assume A
            have B by (rule g)
          }
          hence "A ⟶ B" by (rule impI)
          with d have False by contradiction
        }
        with c and f have False by (rule disjE)
        hence B by (rule FalseE)
      }
      hence "A ⟶ B" by (rule impI)
      with d have False by contradiction
    }
    hence "¬¬(A ⟶ B)" by (rule notI)
    hence "A ⟶ B" by (rule notnotD)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 24: (A ⟷ B) ⟷ (¬A ⟷ ¬B)**

```isabelle
lemma "(A ⟷ B) ⟷ (¬A ⟷ ¬B)"
proof -
  {
    assume a:"A ⟷ B"
    hence b:"A ⟶ B" by (rule iffE)
    from a have c:"B ⟶ A" by (rule iffE)
    {
      assume d:"¬A"
      {
        assume B
        with c have A by (rule mp)
        with d have False by contradiction
      }
      hence "¬B" by (rule notI)
    }
    moreover
    {
      assume e:"¬B"
      {
        assume A
        with b have B by (rule mp)
        with e have False by contradiction
      }
      hence "¬A" by (rule notI)
    }
    ultimately have "¬A ⟷ ¬B" by (rule iffI)
  }
  moreover
  {
    assume f:"¬A ⟷ ¬B"
    hence g:"¬A ⟶ ¬B" by (rule iffE)
    from f have h:"¬B ⟶ ¬A" by (rule iffE)
    {
      assume i:A 
      {
        assume "¬B"
        with h have "¬A" by (rule mp)
        with i have False by contradiction
      }
      hence "¬¬B" by (rule notI)
      hence B by (rule notnotD)
    }
    moreover
    {
      assume j:B
      {
        assume "¬A"
        with g have "¬B" by (rule mp)
        with j have False by contradiction
      }
      hence "¬¬A" by (rule notI)
      hence A by (rule notnotD)
    }
    ultimately have "A ⟷ B" by (rule iffI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 25: A ⟷ ¬¬A**

```isabelle
lemma "A ⟷ ¬¬A" 
proof -
  {
    assume a:A 
    {
      assume "¬A"
      with a have False by contradiction
    }
    hence "¬¬A" by (rule notI)
  }
  moreover 
  {
    assume "¬¬A"
    hence A by (rule notnotD)     
  }    
  ultimately show ?thesis by (rule iffI)    
qed

(*without notnotD*)

theorem "A ⟷ ¬¬A"
proof -
 {
    assume a:A 
    {
      assume "¬A"
      with a have False by contradiction
    }
    hence "¬¬A" by (rule notI)
  }
  moreover 
  {
    assume "¬¬A"
    {
      assume "¬A"
      with ‹¬¬A› have False by (rule notE)
      hence A by (rule FalseE)
    }
    hence A by (rule classical)
  }    
  ultimately show ?thesis by (rule iffI)    
qed  
```

**Exercise 26: (A ⟶ (B ⟶ C)) ⟷ (B ⟶ (A ⟶ C))**

```isabelle
lemma "(A ⟶ (B ⟶ C)) ⟷ (B ⟶ (A ⟶ C))" 
proof -
  {
    assume a:"A ⟶ (B ⟶ C)"
    {
      assume b:B
      {
        assume A 
        with a have "B ⟶ C" by (rule mp)
        from this and b have C by (rule mp)
      }
      hence "A ⟶ C" by (rule impI)
    }
    hence " B ⟶ (A ⟶ C)" by (rule impI)
  }
  moreover
  {
    assume c:"B ⟶ (A ⟶ C)" 
    {
      assume d:A 
      {
        assume B 
        with c have  "A ⟶ C" by (rule mp)
        from this and d have C by (rule mp)
      }
      hence "B ⟶ C" by (rule impI)
    }
    hence "A ⟶ (B ⟶ C)" by (rule impI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 27: P ∨ ¬P**

```isabelle
(*law of excluded middle*)
lemma "P ∨ ¬P"
proof -
  {
    assume a:"¬(P ∨ ¬P)"
    {
      assume b:P
      hence "P ∨ ¬P" by (rule disjI1)
      with a have False by contradiction
    }
    hence "¬P" by (rule notI)
    hence "P ∨ ¬P" by (rule disjI2)
    with a have False by contradiction
  }
  hence "¬¬(P ∨ ¬P)" by (rule notI)
  thus ?thesis by (rule notnotD)
qed
```

**Exercise 28: ¬(A ∧ B) ⟷ (¬A ∨ ¬B)**

```isabelle
lemma "¬(A ∧ B) ⟷ (¬A ∨ ¬B)" 
proof -
  {
    
    assume a:"¬(A ∧ B)"
    {
      assume b:"¬(¬A ∨ ¬B)"
      {
        assume "¬A"
        hence "¬A ∨ ¬B" by (rule disjI1)
        with b have False by contradiction
      }
      hence "¬¬A" by (rule notI)
      hence c:A by (rule notnotD)
      {
        assume "¬B"
        hence "¬A ∨ ¬B" by (rule disjI2)
        with b have False by contradiction
      }
      hence "¬¬B" by (rule notI)
      hence B by (rule notnotD)
      with c have "A ∧ B" by (rule conjI)
      with a have False by contradiction
    }
    hence "¬¬(¬A ∨ ¬B)" by (rule notI)
    hence "¬A ∨ ¬B" by (rule notnotD)
  }
  moreover
  {
    assume a:"¬A ∨ ¬B"
    {
      assume b:"A ∧ B"
      hence c:A by (rule conjE)
      from b have d:B by (rule conjE)
      {
        assume "¬A"
        with c have False by contradiction
      }
      note e=this
      {
        assume "¬B"
        with d have False by contradiction
      }
      with a and e have False by (rule disjE)
    }
    hence "¬(A ∧ B)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 29: (A ⟶ B) ⟶ (C ⟶ ¬B) ⟶ (A ⟶ ¬C)**

```isabelle
(*since implication has right associativity this is the same as (A ⟶ B) ⟶ (C ⟶ ¬B) ⟶ A ⟶ ¬C*)
lemma "(A ⟶ B) ⟶ (C ⟶ ¬B) ⟶ (A ⟶ ¬C)"
proof -
  {
    assume a:"A ⟶ B"
    {
      assume b:"C ⟶ ¬B"
      {
        assume A
        with a have c:B by (rule mp)
        {
          assume C 
          with b have "¬B" by (rule mp)
          with c have False by contradiction
        }
        hence "¬C" by (rule notI)
      }
      hence "A ⟶ ¬C" by (rule impI)
    }
    hence "(C ⟶ ¬B) ⟶ A ⟶ ¬C" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 30: (A ⟶ B ⟶ C)  ⟷ (¬C ⟶ A ⟶ ¬B)**

```isabelle
lemma "(A ⟶ B ⟶ C)  ⟷ (¬C ⟶ A ⟶ ¬B)" 
proof -
  {
    assume a:"A ⟶ B ⟶ C"
    {
      assume b:"¬C"
      {
        assume A 
        with a have c:"B ⟶ C" by (rule mp)
        {
          assume B 
          with c have C by (rule mp)
          with b have False by contradiction
        }
        hence "¬B" by (rule notI)
      }
      hence "A ⟶ ¬B" by (rule impI)
    }
    hence "¬C ⟶ A ⟶ ¬B" by (rule impI)
  }
  moreover
  {
    assume d:"¬C ⟶ A ⟶ ¬B"
    {
      assume e:A 
      {
        assume f:B 
        {
          assume "¬C"
          with d have "A ⟶ ¬B" by (rule mp)
          from this and e have "¬B" by (rule mp)
          with f have False by contradiction
        }
        hence "¬¬C" by (rule notI)
        hence C by (rule notnotD)
      }
      hence "B ⟶ C" by (rule impI)
    }
    hence "A ⟶ B ⟶ C" by (rule impI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 31: (A ⟶ B) ∨ A ⟷ (B ⟶ A) ∨ B**

```isabelle
lemma "(A ⟶ B) ∨ A ⟷ (B ⟶ A) ∨ B "  
proof - 
  {
    assume a:"(A ⟶ B) ∨ A"
    {
      assume b:"¬((B ⟶ A) ∨ B)"
      {
        assume c:A
        {
          assume B 
          have A by (rule c)
        }
        hence "B ⟶ A" by (rule impI)
        hence "(B ⟶ A) ∨ B" by (rule disjI1)
        with b have False by contradiction
        hence "(B ⟶ A) ∨ B" by (rule FalseE)
      }
      note d=this
      {
        assume "A ⟶ B"
        {
          assume e:B
          {
            assume "¬A"
            from e have "(B ⟶ A) ∨ B" by (rule disjI2)
            with b have False by contradiction
          }
          hence "¬¬A" by (rule notI)
          hence A by (rule notnotD)
        }
        hence "B ⟶ A" by (rule impI)
        hence "(B ⟶ A) ∨ B" by (rule disjI1)
      }
      from a and this and d have "(B ⟶ A) ∨ B" by (rule disjE)
      with b have False by contradiction
    }
    hence "¬¬((B ⟶ A) ∨ B)" by (rule notI)
    hence "(B ⟶ A) ∨ B" by (rule notnotD)
  }
  moreover
  {
    assume f:"(B ⟶ A) ∨ B"
    {
      assume g:"¬((A ⟶ B) ∨ A)"
      {
        assume h:B
        {
          assume A 
          have B by (rule h)
        }
        hence "A ⟶ B" by (rule impI)
        hence "(A ⟶ B) ∨ A" by (rule disjI1)
      }
      note i=this
      {
        assume "B ⟶ A"
        {
          assume j:A 
          {
            assume "¬B"
            from j have "(A ⟶ B) ∨ A" by (rule disjI2)
            with g have False by contradiction
          }
          hence "¬¬B" by (rule notI)
          hence B by (rule notnotD)
        }
        hence "A ⟶ B" by (rule impI)
        hence "(A ⟶ B) ∨ A" by (rule disjI1)
      }
      from f and this and i have "(A ⟶ B) ∨ A" by (rule disjE)
      with g have False by contradiction
    }
    hence "¬¬((A ⟶ B) ∨ A)" by (rule notI)
    hence "(A ⟶ B) ∨ A" by (rule notnotD)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 32: ((A ∧ B ) ⟶ C) ⟷ ((A ⟶ C) ∨ (¬C ⟶ ¬B))**

```isabelle
lemma "((A ∧ B ) ⟶ C) ⟷ ((A ⟶ C) ∨ (¬C ⟶ ¬B)) "    
proof -
  {
    assume a:"(A ∧ B ) ⟶ C"
    {
      assume b:"¬ ((A ⟶ C) ∨ (¬C ⟶ ¬B))"
      {
        assume c:A 
        {
          assume d:"¬C"
          {
            assume B
            with c have "A ∧ B" by (rule conjI)
            with a have e:C by (rule mp)
            {
              assume A 
              have C by (rule e)
            }
            hence "A ⟶ C" by (rule impI)
            hence "(A ⟶ C) ∨ (¬C ⟶ ¬B)" by (rule disjI1) 
            with b have False by contradiction
          }
          hence "¬B" by (rule notI)
        }
        hence "¬C ⟶ ¬B" by (rule impI)
        hence "(A ⟶ C) ∨ (¬C ⟶ ¬B)" by (rule disjI2)
        with b have False by contradiction
        hence C by (rule FalseE)
      }
      hence "A ⟶ C" by (rule impI)
      hence "(A ⟶ C) ∨ (¬C ⟶ ¬B)" by (rule disjI1)
      with  b have False by contradiction
    }
    hence "¬¬((A ⟶ C) ∨ (¬C ⟶ ¬B))" by (rule notI)
    hence "(A ⟶ C) ∨ (¬C ⟶ ¬B)" by (rule notnotD)
  }
  moreover
  {
    assume e:"(A ⟶ C) ∨ (¬C ⟶ ¬B)" 
    {
      assume f:"A ⟶ C"
      {
        assume g:"¬((A ∧ B ) ⟶ C)"
        {
          assume "A ∧ B"
          hence A by (rule conjE)
          with f have C by (rule mp)
        }
        hence "A ∧ B ⟶ C" by (rule impI)
        with g have False by contradiction
      }
      hence "¬¬(A ∧ B ⟶ C)" by (rule notI)
      hence "A ∧ B ⟶ C" by (rule notnotD)
    }
    note h=this
    {
      assume i:"¬C ⟶ ¬B"
      {
        assume j:"¬((A ∧ B ) ⟶ C)"
        {
          assume k:"A ∧ B" 
          {
            assume "¬C"
            with i have l:"¬B" by (rule mp)
            from k have B by (rule conjE)
            with l have False by contradiction
          }
          hence "¬¬C" by (rule notI)
          hence C by (rule notnotD)
        }
        hence "(A ∧ B ) ⟶ C" by (rule impI)
        with j have False by contradiction
      }
      hence "¬¬((A ∧ B ) ⟶ C)" by (rule notI)
      hence "(A ∧ B ) ⟶ C" by (rule notnotD)
    }
    with e and h  have "(A ∧ B ) ⟶ C" by (rule disjE)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 33: ((A ∧ (B ⟶ C )) ⟶ A) ⟷ ((A  ∧ (B ⟶ ¬C)) ⟶ A)**

```isabelle
lemma "((A ∧ (B ⟶ C )) ⟶ A) ⟷ ((A  ∧ (B ⟶ ¬C)) ⟶ A) "
proof -
  {
    assume "(A ∧ (B ⟶ C )) ⟶ A" 
    {
      assume "A  ∧ (B ⟶ ¬C)"
      hence A by (rule conjE)
    }
    hence "(A ∧ (B ⟶ ¬C)) ⟶ A" by (rule impI)
  }
  moreover
  {
    assume "(A  ∧ (B ⟶ ¬C)) ⟶ A"
    {
      assume "A ∧ (B ⟶ C )"
      hence  A by (rule conjE)
    }
    hence "(A ∧ (B ⟶ C )) ⟶ A" by (rule impI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 34: (A ∨ ((B ⟶ C) ∧ D)) ⟶ ((B ∨ A) ∨ (¬C ⟶ D))**

```isabelle
lemma "(A ∨ ((B ⟶ C) ∧ D)) ⟶ ((B ∨ A) ∨ (¬C ⟶ D))"  
proof -
  {
    assume a:"A ∨ ((B ⟶ C) ∧ D)"
    {
      assume A 
      hence "B ∨ A" by (rule disjI2)
      hence "(B ∨ A) ∨ (¬C ⟶ D)" by (rule disjI1)
    }
    note b=this
    {
      assume c:"(B ⟶ C) ∧ D"
      hence d:"B ⟶ C" by (rule conjE)
      from c have e:D by (rule conjE)
      {
        assume f:"¬((B ∨ A) ∨ (¬C ⟶ D))"
        {
          assume g:"¬(¬C ⟶ D)"
          {
            assume "¬C"
            have D by (rule e)
          }
          hence "¬C ⟶ D" by (rule impI)
          with g have False by contradiction
        }
        hence "¬¬(¬C ⟶ D)" by (rule notI)
        hence "¬C ⟶ D" by (rule notnotD)
        hence "(B ∨ A) ∨ (¬C ⟶ D)" by (rule disjI2)
        with f have False by contradiction
      }
      hence "¬¬((B ∨ A) ∨ (¬C ⟶ D))" by (rule notI)
      hence "(B ∨ A) ∨ (¬C ⟶ D)" by (rule notnotD)
    }
    from a and b and this have "(B ∨ A) ∨ (¬C ⟶ D)" by (rule disjE)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 35: A ⟶ True**

```isabelle
lemma "A ⟶ True" 
proof -
  {
    assume A 
    have True by (rule TrueI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 36: (A ⟹ B) ⟹ A ⟹ B**

```isabelle
lemma "(A ⟹ B) ⟹ A ⟹ B"  
  using [[simp_trace_new mode=full]]
proof -
  {
    assume a:"A ⟹ B" 
    hence b:"A ⟶ B" by (rule impI)
    {
      assume A
      with b show B by (rule mp)
    }
  }
qed
  
(*just another way to I like to represent this proof*)
lemma "(A ⟹ B) ⟹ A ⟹ B"
proof -
  assume a:"A ⟹ B"
  hence b:"A ⟶ B" by (rule impI)
  assume A
  with b show B by (rule mp)
qed

(*proving with meta implication*)  
lemma "(A ⟹ B) ⟹ A ⟹ B"
proof -
  assume a:"A ⟹ B"
  assume A 
  with a have B by (rule meta_mp)
qed
```
**Exercise 37: ⟦A ∨ B ; ¬A ∨ ¬C⟧ ⟹ C ⟶ B**

```isabelle
lemma "⟦A ∨ B ; ¬A ∨ ¬C⟧ ⟹ C ⟶ B"
proof - 
  {
    assume "A ∨ B"
    {
      assume "¬A ∨ ¬C" 
      {
        assume "¬A"  
        {
          assume A 
          with ‹¬A› have False by contradiction
          hence "C ⟶ B" by (rule FalseE)     
        }
        note tmp=this 
        {
          assume B 
          {
            assume C
            from ‹B› have B by assumption
          }
          hence "C ⟶ B" by (rule impI)
        }
        from ‹A ∨ B› and tmp and this have "C ⟶ B" by (rule disjE)
      }
      note tmp=this
      {
        assume "¬C"
        {
          assume C 
          with ‹¬C› have False by contradiction
          hence B by (rule FalseE)
        }
        hence "C ⟶ B" by (rule impI)
      }
      with ‹¬A ∨ ¬C› and tmp show "C ⟶ B" by (rule disjE)
    }
  }
qed
```

**Exercise 38: ¬C ⟹ ¬A  ∨  ((B ∧ C) ⟶ A)**

```isabelle
lemma "¬C ⟹ ¬A  ∨  ((B ∧ C) ⟶ A)"
proof -
  {
    assume a:"¬C"
    {
      assume b:"¬(¬A  ∨  ((B ∧ C) ⟶ A))"
      {
        assume "B ∧ C"
        hence c:C by (rule conjE)
        {
          assume "¬A"
          from a and c have False by contradiction
        }
        hence "¬¬A" by (rule notI)
        hence A by (rule notnotD)
      }
      hence "B ∧ C ⟶ A" by (rule impI)
      hence "¬A  ∨  ((B ∧ C) ⟶ A)" by (rule disjI2)
      with b have False by contradiction
    }
    hence "¬¬(¬A  ∨  ((B ∧ C) ⟶ A))" by (rule notI)
    thus "¬A  ∨  ((B ∧ C) ⟶ A)" by (rule notnotD)
  }
qed
```

**Exercise 39: ¬(((A ⟶ B)  ∧  A) ∧ (B ⟶ ¬C ∧ ¬C ⟶ B)) ⟶ ((¬D ⟶ B) ∨ (B ⟶ (¬B ⟶ ¬A)))**

```isabelle
lemma "¬(((A ⟶ B)  ∧  A) ∧ (B ⟶ ¬C ∧ ¬C ⟶ B)) ⟶ ((¬D ⟶ B) ∨ (B ⟶ (¬B ⟶ ¬A)))"  
proof -
  {
    assume "¬(((A ⟶ B)  ∧  A) ∧ (B ⟶ ¬C ∧ ¬C ⟶ B))"
    {
      assume a:"B"
      {
        assume b:"¬B"
        from a and b have False by contradiction
        hence "¬A" by (rule FalseE)
      }
      hence "¬B ⟶ ¬A" by (rule impI)
    }
    hence "B ⟶ ¬B ⟶ ¬A" by (rule impI)
    hence "(¬D ⟶ B) ∨ (B ⟶ (¬B ⟶ ¬A))" by (rule disjI2)
  }
  thus ?thesis by (rule impI)
qed
```
**Exercise 40: (A ⟶ B) ∨ (B ⟶ A)**

```isabelle
lemma "(A ⟶ B) ∨ (B ⟶ A)" 
proof - 
  {
    assume "¬((A ⟶ B) ∨ (B ⟶ A))"
    {
      assume "¬(A ⟶ B)"
      {
        assume B 
        {
          assume A 
          from ‹B› have B by assumption
        }
        hence "A ⟶ B" by (rule impI)
        with ‹¬(A ⟶ B)› have False by contradiction
        hence A by (rule FalseE)
      }
      hence "B ⟶ A" by (rule impI)
      hence "(A ⟶ B) ∨ (B ⟶ A)" by (rule disjI2)
      with ‹¬((A ⟶ B) ∨ (B ⟶ A))› have False by contradiction
    }
    hence "¬¬(A ⟶ B)" by (rule notI)
    hence "A ⟶ B" by (rule notnotD)
    hence "(A ⟶ B) ∨ (B ⟶ A)" by (rule disjI1)
    with ‹¬((A ⟶ B) ∨ (B ⟶ A))› have False by contradiction
  }
  hence "¬¬((A ⟶ B) ∨ (B ⟶ A))" by (rule notI)
  thus "(A ⟶ B) ∨ (B ⟶ A)" by (rule notnotD)
qed
```
 
**Exercise 41: B ∧ B ⟶ A ⟶ ((C ∨ ¬B) ∨ A ⟷ A ∧ ¬(B ⟶ ¬A))**

```isabelle
lemma "B ∧ B ⟶ A ⟶ ((C ∨ ¬B) ∨ A ⟷ A ∧ ¬(B ⟶ ¬A))"
proof - 
  {
    assume a:"B ∧ B"
    hence b:B by (rule conjE)
    {
      assume c:A 
      {
        assume "(C ∨ ¬B) ∨ A"
        {
          assume "B ⟶ ¬A"
          from this and  b have "¬A" by (rule mp)
          with c have False by contradiction
        }
        hence "¬(B ⟶ ¬A)" by (rule notI)
            with c have "A ∧ ¬(B ⟶ ¬A)" by (rule conjI)
      }
      moreover
      {
        assume d:"A ∧ ¬(B ⟶ ¬A)"
        hence A by (rule conjE)
        hence "(C ∨ ¬B) ∨ A" by (rule disjI2)
      }
      ultimately have "(C ∨ ¬B) ∨ A ⟷ A ∧ ¬(B ⟶ ¬A)" by (rule iffI)
    }
    hence " A ⟶ ((C ∨ ¬B) ∨ A ⟷ A ∧ ¬(B ⟶ ¬A))" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 42: (¬A ⟶ False) ⟶ A**

```isabelle
theorem ProofByContradiction: "(¬A ⟶ False) ⟶ A" 
proof -
  {
    assume "(¬A ⟶ False)"
    {
      assume "¬A"
      with ‹¬A ⟶ False› have False by (rule mp)
      hence A by (rule FalseE)
    }
    hence "A" by (rule classical)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 43: ⟦A ∧ B ; ¬A ∨ C ⟧ ⟹ ¬((A ∧ B) ⟶ ¬C)**
```isabelle
theorem "⟦A ∧ B ; ¬A ∨ C ⟧ ⟹ ¬((A ∧ B) ⟶ ¬C)" 
proof -
  assume a:"A ∧ B"
  and b:"¬A ∨ C"
  from a have A by (rule conjE)
  from a have B by (rule conjE)
  {
    assume "(A ∧ B) ⟶ ¬C"
    from this and a have "¬C" by (rule mp)
    {
      assume "¬A" 
      with ‹A› have False by contradiction
    }
    note tmp=this
    {
      assume C
      with ‹¬C› have False by contradiction
    }
    from b and tmp and this have False by (rule disjE)
  }
  thus ?thesis by (rule notI)
qed
```

**Exercise 44: ⟦¬(¬(A ⟶ B) ∧ ¬B) ; ¬C ⟶ A ⟧ ⟹ C ∨ B**
```isabelle
theorem "⟦¬(¬(A ⟶ B) ∧ ¬B) ; ¬C ⟶ A ⟧ ⟹ C ∨ B" 
proof - 
  assume a:"¬(¬(A ⟶ B) ∧ ¬B)"
  and b:"¬C ⟶ A"
  {
    assume c:"¬(C ∨ B)"
    {
      assume d:"¬C"
      {
        assume e:"¬B"
        {
          assume f:"A ⟶ B"
          from b d have A by (rule mp)
          with f have B by (rule mp)
          with e have False by contradiction
        }
        hence "¬(A ⟶ B)" by (rule notI)
        from this e have "¬(A ⟶ B) ∧ ¬B" by (rule conjI)
        with a have False by (rule notE)
      }
      hence "¬¬B" by (rule notI)
      hence B by (rule notnotD)
      hence "C ∨ B" by (rule disjI2)
      with c have False by (rule notE)
    }
    hence "¬¬C" by (rule notI)
    hence C by (rule notnotD)
    hence "C ∨ B" by (rule disjI1)
    with c have False by (rule notE)
  }
  hence "¬¬ (C ∨ B)" by (rule notI)
  thus "C ∨ B" by (rule notnotD)
qed
```

**Exercise 45: C ⟶ ¬A ∨ ((B ∨ C) ⟶ A)**
```isabelle
theorem "C ⟶ ¬A ∨ ((B ∨ C) ⟶ A)" 
proof - 
  {
    assume C
    {
      assume "¬(¬A ∨ ((B ∨ C) ⟶ A))" 
      {
        assume A 
        {
          assume "B ∨ C"
          from ‹A› have A by assumption
        }
        hence "(B ∨ C) ⟶ A" by (rule impI)
        hence "¬A ∨ ((B ∨ C) ⟶ A)" by (rule disjI2)
        with ‹¬(¬A ∨ ((B ∨ C) ⟶ A))› have False by (rule notE)
      }
      hence "¬A" by (rule notI)
      hence "¬A ∨ ((B ∨ C) ⟶ A)" by (rule disjI1)
      with ‹¬(¬A ∨ ((B ∨ C) ⟶ A))› have False by contradiction
    }
    hence "¬¬(¬A ∨ ((B ∨ C) ⟶ A))" by (rule notI)
    hence "¬A ∨ ((B ∨ C) ⟶ A)" by (rule notnotD)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 46: (A ∧ (A ⟶ ¬A)) ⟹ (A ∧ (B ⟶ ¬A))**
```isabelle
theorem "(A ∧ (A ⟶ ¬A)) ⟹ (A ∧ (B ⟶ ¬A))"  
proof -
  assume a:"A ∧ (A ⟶ ¬A)"
  hence b:"A ⟶ ¬A" by (rule conjE)
  from a have c:A by (rule conjE)
  with b have "¬A" by (rule impE)
  with c have False by contradiction
  thus ?thesis by (rule FalseE)
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
theorem "(∀x. ∃y. P x y) ∨ (∃x. ∀y. ¬P x y)" 
proof - 
  {
    assume a:"¬((∀x. ∃y. P x y) ∨ (∃x. ∀y. ¬P x y) )"
    {
      assume "∀x. ∃y. P x y"
      hence "(∀x. ∃y. P x y) ∨ (∃x. ∀y. ¬P x y)" ..
      with a have False ..
    }
    hence  b:"¬(∀x. ∃y. P x y)" by (rule notI)
    {
      assume c:"¬(∃x. ∀y. ¬P x y)"
      {
        fix aa
        {
          assume d:"¬(∃y. P aa y)"    
          {
            fix bb 
            {
              assume "P aa bb"
              hence "∃y. P aa y" by (rule exI)
              with d have False by contradiction
            }
            hence "¬P aa bb" by (rule notI)
          }
          hence "∀y. ¬P aa y" by (rule allI)
          hence "∃x. ∀y. ¬P x y" by (rule exI)
          with c have False by contradiction
        }
        hence "¬¬(∃y. P aa y)" by (rule notI)
        hence "∃y. P aa y" by (rule notnotD)
      }
      hence "∀x. ∃y. P x y" by (rule allI)
      with b have False by contradiction
    }
    hence "¬¬(∃x. ∀y. ¬P x y)" by (rule notI)
    hence "∃x. ∀y. ¬P x y" by (rule notnotD)
    hence "(∀x. ∃y. P x y) ∨ (∃x. ∀y. ¬P x y)"  by (rule disjI2)
    with a have False by contradiction
  }
  hence "¬¬((∀x. ∃y. P x y) ∨ (∃x. ∀y. ¬P x y))" by (rule notI)
  thus ?thesis by (rule notnotD)
qed
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
lemma "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)" 
proof -
  {
    assume "∃x. ∀y. P x y" 
    { 
      fix b
      {
        fix a           
        assume "∀y .P a y"
        hence "P a b" by (rule allE)
        hence "∃x. P x b" by (rule exI)
      } 
      with  ‹∃x. ∀y. P x y› have "∃x. P x b" by (rule exE)
    }
    hence "∀y. ∃x. P x y" by (rule allI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 7: (¬ (∀x. ∃y. P x y)) ⟷ (∃x. ∀y. ¬P x y)**

```isabelle
lemma "(¬(∀x. ∃y. P x y)) ⟷ (∃x. ∀y. ¬P x y)"  
proof -
  {
    assume a:"¬ (∀x. ∃y. P x y)"
    {
      assume b:"¬(∃x. ∀y. ¬P x y)"
      {
        fix aa
        {
          assume c:"¬(∃y. P aa y)"
          {
            fix bb
            {
              assume "P aa bb"
              hence "∃y. P aa y" by (rule exI)
              with c have False by contradiction
            }
            hence "¬P aa bb" by (rule notI)    
          }
          hence "∀y. ¬P aa y" by (rule allI)
          hence "∃x. ∀y. ¬P x y" by (rule exI)
          with b have False by contradiction
        }   
        hence "¬¬(∃y. P aa y)" by (rule notI)  
        hence "∃y. P aa y" by (rule notnotD)  
      }
      hence "∀x. ∃y. P x y" by (rule allI)
      with a have False by contradiction
    }
    hence "¬¬(∃x. ∀y. ¬P x y)" by (rule notI)
    hence "∃x. ∀y. ¬P x y" by (rule notnotD)
  }  
  moreover
  {
    assume a:"∃x. ∀y. ¬P x y"
    {
      assume b:"∀x. ∃y. P x y" 
      {
        fix aa 
        assume c:"∀y. ¬P aa y"
        from b have d:"∃y. P aa y" by (rule allE)
        {
          fix bb
          assume d:"P aa bb" 
          from c have "¬P aa bb" by (rule allE)
          with d have False by contradiction
        }
        with d have False by (rule exE)
      }
      with a have False by (rule exE)
    }
    hence "¬(∀x. ∃y. P x y)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 8: (¬ (∃x. ∀y. P x y)) ⟷ (∀x. ∃y. ¬P x y)**

```isabelle
lemma "(¬ (∃x. ∀y. P x y)) ⟷ (∀x. ∃y. ¬P x y)" 
proof-
  {
    assume a:"¬ (∃x. ∀y. P x y)"
    {
      assume b:"¬(∀x. ∃y. ¬P x y)" 
      {
        fix aa 
        {
          assume c:"¬(∃y. ¬P aa y)"
          {
            fix bb
            {
              assume "¬P aa bb" 
              hence "∃y. ¬P aa y" by (rule exI)
              with c have False by contradiction
            }
            hence "¬¬P aa bb" by (rule notI)
            hence "P aa bb" by (rule notnotD)
          }
          hence "∀y. P aa y" by (rule allI)
          hence "∃x. ∀y. P x y" by (rule exI)
          with a have False by contradiction
        }
        hence "¬¬(∃y. ¬P aa y)" by (rule notI)
        hence "∃y. ¬P aa y" by (rule notnotD)
      }
      hence "∀x. ∃y. ¬P x y" by (rule allI)
      with b have False by contradiction
    }
    hence "¬¬(∀x. ∃y. ¬P x y)" by (rule notI)
    hence "∀x. ∃y. ¬P x y" by (rule notnotD)
  }
  moreover
  {
    assume a:"∀x. ∃y. ¬P x y"
    {
      assume b:"∃x. ∀y. P x y" 
      {
        fix aa
        assume c:"∀y. P aa y"
        from a have d:"∃y. ¬P aa y" by (rule allE)
        {
          fix bb 
          assume d:" ¬P aa bb" 
          from c have "P aa bb" by (rule allE)
          with d have False by contradiction
        }
        with d have False by (rule exE)
      }
      with b have False by (rule exE)
    }
    hence "¬(∃x. ∀y. P x y)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 9: (∃x. P x) =  (¬(∀x. ¬P x))**

```isabelle
lemma "(∃x. P x) =  (¬(∀x. ¬P x))" 
proof -
  {
    assume a:"∃x. P x"
    {
      assume b:"∀x. ¬P x"
      {
        fix aa
        assume c:"P aa"
        from b have "¬P aa" by (rule allE)
        with c have False by contradiction
      }
      with a have False by (rule exE)
    }
    hence "¬(∀x. ¬P x)" by (rule notI)
  }
  moreover
  {
    assume d:"¬(∀x. ¬P x)"
    {
      assume e:"¬(∃x. P x)"
      {
        fix aa
        {
          assume "P aa"
          hence "∃x. P x" by (rule exI)
          with e have False by contradiction
        }   
        hence "¬P aa" by (rule notI)
      }
      hence "∀x. ¬P x" by (rule allI)
      with d have False by contradiction
    }
    hence "¬¬(∃x. P x)" by (rule notI)
    hence "(∃x. P x)" by (rule notnotD)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 10: (∀x. (P x ⟶ Q x)) ⟶ ((∀x. P x) ⟶ (∀x. Q x))**

```isabelle
lemma "(∀x. (P x ⟶ Q x)) ⟶ ((∀x. P x) ⟶ (∀x. Q x))"
proof -
  {
    assume a:"∀x. (P x ⟶ Q x)"
    {
      assume b:"∀x. P x"
      {
        fix aa 
        from a have c:"P aa ⟶ Q aa" by (rule allE)
        from b have "P aa" by (rule allE)
        with c have "Q aa" by (rule mp)
      }
      hence "∀x. Q x" by (rule allI)
    }
    hence "(∀x. P x) ⟶ (∀x. Q x)" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 11: (¬ (∃x. ∀y. P x y)) ⟶ ¬(∃x. ∃y .  ¬P x y) ⟶ False**

```isabelle
lemma "(¬ (∃x. ∀y. P x y)) ⟶ ¬(∃x. ∃y .  ¬P x y) ⟶ False " 
proof -
  {
    assume a:"(¬ (∃x. ∀y. P x y))"
    {
      fix aa
      assume b:"¬(∃x. ∃y .  ¬P x y)"
      {
        fix bb
        {
          assume "¬P aa bb"
          hence "∃y. ¬P aa y" by (rule exI)
          hence "∃x. ∃y. ¬P x y" by (rule exI)
          with b have False by contradiction
        }
        hence "¬¬P aa bb" by (rule notI)
        hence "P aa bb" by (rule notnotD)
      }
      hence "∀y. P aa y" by (rule allI)
      hence "∃x. ∀y. P x y" by (rule exI)
      with a have False by contradiction
    }
    hence "¬(∃x. ∃y .  ¬P x y) ⟶ False " by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 12: (∀x. (P x ⟶ Q x)) ⟶ (∀x. (Q x ⟶ R x)) ⟶ (∀x .(P x ⟶ R x))**

```isabelle
lemma "(∀x. (P x ⟶ Q x)) ⟶ (∀x. (Q x ⟶ R x)) ⟶ (∀x .(P x ⟶ R x))"  
proof - 
  {
    assume a:"∀x. (P x ⟶ Q x)"
    {
      assume b:"∀x. (Q x ⟶ R x)"
      {
        fix aa 
        {
          assume c:"P aa"
          from b have e:"Q aa ⟶ R aa" by (rule allE)
          from a have d:"P aa ⟶ Q aa" by (rule allE)
          from this and c have "Q aa" by (rule mp)
          with e have "R aa" by (rule mp)
        }
        hence "P aa ⟶ R aa" by (rule impI)
      }
      hence "∀x. (P x ⟶ R x)" by (rule allI)
    }
    hence "(∀x. (Q x ⟶ R x)) ⟶(∀x. (P x ⟶ R x))" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 13: ⋀aa. ((∀x. (P x ⟶ Q x)) ∧ P aa  ⟶ Q aa)**

```isabelle
lemma "⋀aa. ((∀x. (P x ⟶ Q x)) ∧ P aa  ⟶ Q aa)" 
proof -
  {
    fix aa
    assume a:"(∀x. (P x ⟶ Q x)) ∧ P aa"
    hence b:"P aa" by (rule conjE)
    from a have "∀x. (P x ⟶ Q x)" by (rule conjE)
    hence "P aa ⟶ Q aa" by (rule allE)
    from this and b have "Q aa" by (rule mp)
  }
  thus "⋀aa. ((∀x. (P x ⟶ Q x)) ∧ P aa  ⟶ Q aa)"  by (rule impI)  
qed
```

**Exercise 14: ¬(∃x. P x) ⟷ (∀x. ¬P x)**

```isabelle
lemma "¬(∃x. P x) ⟷ (∀x. ¬P x)"  
proof -
  {
    assume "¬(∃x. P x)"
    {
      assume "¬(∀x. ¬P x)"
      {
        fix aa 
        {
          assume "P aa"
          hence "∃x. P x" by (rule exI)
          with ‹¬(∃x. P x )› have False by contradiction
        }
        hence "¬P aa" by (rule notI)
      }
      hence "∀x. ¬P x" by (rule allI)
      with ‹¬(∀x. ¬P x)› have False by contradiction
    }
    hence "¬¬(∀x. ¬P x)" by (rule notI)
    hence "∀x. ¬P x" by (rule notnotD)
  }
  moreover
  {
    assume a:"∀x. ¬P x"
    {
      assume "∃x. P x"
      {
        fix aa 
        assume "P aa"
        from ‹∀x. ¬P x› have "¬P aa" by (rule allE)
        with ‹P aa› have False by contradiction
      }
      with ‹∃x. P x› have False by (rule exE)
    }
    hence "¬(∃x. P x)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)    
qed
```

**Exercise 15: ¬(∀x. P x) ⟷ (∃x. ¬P x)**

```isabelle
lemma "¬(∀x. P x) ⟷ (∃x. ¬P x)" 
proof -
  {
    assume a:"¬(∀x. P x)" 
    {
      assume b:"¬(∃x. ¬P x)"
      {
        fix aa 
        {
          assume "¬P aa"
          hence "∃x. ¬P x" by (rule exI)
          with b have False by contradiction
        }
        hence "¬¬P aa" by (rule notI)
        hence "P aa" by (rule notnotD)
      }
      hence "∀x. P x" by (rule allI)
      with a have False by contradiction
    }
    hence "¬¬(∃x. ¬P x)" by (rule notI)
    hence "∃x. ¬P x" by (rule notnotD)
  }
  moreover
  {
    assume a:"∃x. ¬P x"
    {
      assume b:"∀x. P x" 
      {
        fix aa
        assume c:"¬P aa"
        from b have "P aa" by (rule allE)
        with c have False by contradiction
      }
      with a have False by (rule exE)
    }
    hence "¬(∀x. P x)" by (rule notI)
  }
  ultimately show ?thesis by (rule iffI)
qed
```

**Exercise 16: (∃x. (P x ⟶ ¬P(F x))) ⟶ (∃x. ¬P x)**

```isabelle
lemma "(∃x. (P x ⟶ ¬P(F x))) ⟶ (∃x. ¬P x)" 
proof -
  {
    assume a:"∃x. (P x ⟶ ¬P(F x))"
    {
      assume b:"¬(∃x . ¬P x )"
      {
        fix aa
        assume c:"P aa ⟶ ¬P(F aa)"
        {
          assume "P aa"
          with c have "¬P (F aa)" by (rule mp)
          hence "∃x. ¬P (x)" by (rule exI)
          with b have False by contradiction
        }
        hence "¬P aa" by (rule notI)
        hence "∃x. ¬P x" by (rule exI)
        with b have False by contradiction
      }
      with a have False by (rule exE)
    }
    hence "¬¬(∃x . ¬P x )" by (rule notI)
    hence "∃x . ¬P x " by (rule notnotD)
  }
  thus ?thesis by (rule impI)
qed
```

**Exercise 17: P a (Q (Q a))  ⟶ (∀x. ∀y. P x (Q y) ⟶ (∃z. P (Q z) y)) ⟶ (∃z. P z a)**

```isabelle
lemma "P a (Q (Q a))  ⟶ (∀x. ∀y. P x (Q y) ⟶ (∃z. P (Q z) y)) ⟶ (∃z. P z a)" 
proof -
  {
    assume a:"P a (Q (Q a))"
    hence b:"∃z. P z (Q (Q a))" by (rule exI)
    {
      assume c:"(∀x. ∀y. P x (Q y) ⟶ (∃z. P (Q z) y))"
      hence "(∀y. P a (Q y) ⟶ (∃z. P (Q z) y))"  ..
      hence "(P a (Q (Q a)) ⟶ (∃z. P (Q z) (Q a)))" ..
      from this a have d:"(∃z. P (Q z) (Q a))" by (rule mp)
      {
        assume e:"(∀z . ¬P z a)" 
        {
          fix b     
          assume f:"P (Q b) (Q a)"
          from c have "(∀y. P (Q b) (Q y) ⟶ (∃z. P (Q z) y))" by (rule allE)
          hence "P (Q b) (Q a) ⟶ (∃z. P (Q z) a)" by (rule allE)
          from this and  f have g:"∃z. P (Q z) a" by (rule mp)
          {
            fix c 
            assume h:"P (Q c) a" 
            from e have "¬P (Q c) a" by (rule allE)
            with h have False by contradiction
          }
          with g have False by (rule exE)
        }
        with d have False by (rule exE)
      }
      hence e:"¬(∀z . ¬P z a)" by (rule notI)
      have f:"(∃z. P z a)"
      proof -
        {
          assume g:"¬(∃z. P z a)"
          have h:"∀z. ¬P z a"
          proof -
            {
              assume i:"¬(∀z . ¬P z a)"
              {
                fix b 
                {
                  assume "P b a"
                  hence "∃z. P z a" by (rule exI)
                  with g have False by contradiction
                }
                hence "¬P b a" by (rule notI)
              }
              hence "∀z. ¬P z a" by (rule allI)
              with i have False by contradiction
            }
            hence "¬¬(∀z . ¬P z a)" by (rule notI)
            thus "∀z . ¬P z a" by (rule notnotD)
          qed
          from h and e have False by contradiction  
        }
        hence "¬¬(∃z. P z a)" by (rule notI)
        thus "∃z. P z a" by (rule notnotD)
      qed  
    }
    hence "((∀x. ∀y. P x (Q y) ⟶ (∃z. P (Q z) y))) ⟶ (∃z. P z a)" by (rule impI)
  }
  thus ?thesis by (rule impI)
qed
```