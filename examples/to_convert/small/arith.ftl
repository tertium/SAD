#
# Axioms of zero and the successor
#

[a number/numbers] [the zero]
[the successor/successors of x]
[x is nonzero @ x is not equal to zero]

Signature NatSort.  Number is a notion.

Let A,B,C stand for numbers.

Signature NatZero.  Zero is a number.

Signature NatSucc.  The successor of A is a nonzero number.

Axiom SuccEquSucc.
    If the successor of A is equal to the successor of B
    then A and B are equal.

#
# Axioms of addition
#

[the sum of x and y]

Signature NatSum.   The sum of A and B is a number.

Axiom AddZero.      The sum of A and zero is equal to A.

Axiom AddSucc.      The sum of A and the successor of B 
        is equal to the successor of the sum of A and B.

#
# We take the following facts as axioms, too
#

Axiom ZeroOrSucc.
    Every nonzero number is the successor of some number.

Axiom AssoAdd.
    The sum of A and the sum of B and C is equal
        to the sum of (the sum of A and B) and C.

Axiom InjAdd.
    If the sum of A and B is equal to the sum of A and C
        then B and C are equal.

Axiom Diff.
    There exists C such that
        A is the sum of B and C or B is the sum of A and C.

#
# Definition of order on natural numbers
#

[x is less than y] [x is greater than y @ y is less than x]

Definition DefLess.
    A is less than B  iff  B is equal to
        the sum of A and the successor of some number.

#
# Basic properties of order
#

Theorem NReflLess.
    A is not less than A.
Proof.
    Assume the contrary.
    Take a number C such that A is equal to
        the sum of A and the successor of C.
    Then the successor of C is zero (by AddZero,InjAdd).
    We have a contradiction.
qed.


Theorem TransLess.
    Assume A is less than B and B is less than C.
    Then A is less than C (by DefLess).
Proof.
    Let M be a number and N be the successor of M.
    Let P be a number and Q be the successor of P.
    Assume the sum of A and N is equal to B.
    Assume the sum of B and Q is equal to C.
    Let S be the sum of N and Q.
    S is the successor of the sum of N and P (by AddSucc).
    The sum of A and S is equal to C (by AssoAdd).
qed.


Theorem ASymmLess.
    If B is less than A then A is not less than B.


Theorem TotalLess.
    Let A,B be nonequal.
    Then A is less than B or B is less than A.
Proof.
    Take C such that A is the sum of B and C or B is the sum of A and C.
    If C is zero then B is equal to A.
    Hence C is the successor of some number.
    If B is the sum of A and C then A is less than B.
    Then A is the sum of B and C or A is less than B.
    If A is the sum of B and C then B is less than A.
    Hence the thesis.
qed.


#
# Axioms of multiplication
#

[the product of x and y]

Signature NatMul.   The product of A and B is a number.

Axiom MulZero.      The product of A and zero is equal to zero.

Axiom MulSucc.      The product of A and the successor of B 
        is equal to the sum of A and the product of A and B.

Axiom Monot.
    Assume A is greater than B and C is nonzero.
    Then the product of A and C is greater
        than the product of B and C.


Theorem MonotNSt.
    Assume A is not less than B.
    Then the product of A and C is not less
                than the product of B and C.
Proof.
    Case A, B are equal or C is zero.
        Then the product of A and C is equal
            to the product of B and C (by MulZero).
        Hence the thesis (by NReflLess).
    end.
    Case A, B are nonequal and C is nonzero.
        We have the thesis (by Monot,TotalLess,ASymmLess).
    end.
qed.

