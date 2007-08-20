[an integer/integers] [a program/programs] [a code/codes of x] 
[x succeeds/succeed on y and z] [x decides/decide halting]
[x halts on y] 

#Signature PrgSort.  Program is a notion.
#Signature IntSort.  Integer is a notion.

Let U,V,W stand for programs.
Let x,y,z stand for integers.

Signature CodeInt.  A code of W is an integer.
Axiom ExiCode.      Every program has a code.

#Signature HaltRel.  W halts on x is a relation.
#Signature SuccRel.  W succeeds on x and y is a relation.

Definition DefDH.   W decides halting iff
    for every z and every code x of every V
        W succeeds on x and z iff V halts on z.

Axiom Cantor.       Let W decide halting.
    Then there exists V such that for every y
    V halts on y iff W does not succeed on y and y.

Theorem Main.       No program decides halting.
