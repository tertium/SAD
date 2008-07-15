#
# Integers
#

[integer/-s]

Signature Integers. An integer is a notion.

Let a,b,c,d,i,j,k,l,m,n stand for integers.

Signature IntZero.  0 is an integer.
Signature IntOne.   1 is an integer.
Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.

Let a - b stand for a + (-b).

Axiom AddAsso.      a + (b + c) = (a + b) + c.
Axiom AddComm.      a + b = b + a.
Axiom AddZero.      a + 0 = a = 0 + a.
Axiom AddNeg.       a - a = 0 = -a + a.

Axiom MulAsso.      a * (b * c) = (a * b) * c.
Axiom MulComm.      a * b = b * a.
Axiom MulOne.       a * 1 = a = 1 * a.

Axiom Distrib.      a * (b + c) = (a*b) + (a*c) and
                    (a + b) * c = (a*c) + (b*c).

Lemma MulZero.      a * 0 = 0 = 0 * a.
Lemma MulMinOne.    -1 * a = -a = a * -1.

Axiom ZeroDiv.      a * b = 0 => a = 0 \/ b = 0.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[divisor/-s] [divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Definition EquMod.  a = b (mod q) iff q | a-b.

Lemma EquModRef.    a = a (mod q).

Lemma EquModSym.    a = b (mod q) => b = a (mod q).
Proof.
    Assume that a = b (mod q).
    Take n such that q * n = a - b.
    We have q * -n = b - a.
qed.

Lemma EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).
Proof.
    Assume that a = b (mod q) /\ b = c (mod q).
    Take n such that q * n = a - b.
    Take m such that q * m = b - c.
    We have q * (n + m) = a - c.
qed.

Signature Prime.    p is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom PrimeDivisor. n has a prime divisor iff n != 1 /\ n != -1.


#
# Generic sets
#

[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature Sets.     A set is a notion.

Let S,T stand for sets.

Signature Elements. An element of S is a notion.

Let x belongs to S stand for x is an element of S.
Let x << S stand for x is an element of S.

Definition Subset.  A subset of S is a set T such that
                        every element of T belongs to S.

Let S [= T stand for S is a subset of T.

Signature FinSet.   S is finite is an atom.

Let x is infinite stand for x is not finite.


#
# Sets of integers
#

[intset/-s]

Let a intset stand for a set S such that
    every element of S is an integer.

Let A,B,C,D stand for intsets.

Definition ZSetUnion.
    A \-/ B = { integer x | x << A \/ x << B }.

Definition ZSetInter.
    A /-\ B = { integer x | x << A /\ x << B }.

Definition InnerUnion.
    Let S be a set such that every element of S is a intset.
    \-/ S = { integer x | x belongs to some element of S }.

Definition IntSetCompl.
    ~ A = { integer x | x does not belong to A }.


#
# Introducing topology
#

Definition NSet.    NSet(a,q) = { b | b = a (mod q) }.

Definition Open.    A is open iff for any a << A
                    there exists q such that NSet(a,q) [= A.

Definition Closed.  A is closed iff ~A is open.

Lemma UnionOpen.    Let S be a set such that
                        all elements of S are open intsets.
                    \-/ S is open.

Lemma InterOpen.    Let A,B be open intsets.
                    A /-\ B is open.
Proof.
    Let n belong to A /-\ B.
    Then n belongs to A and n belongs to B.
    Take p such that NSet(n,p) [= A.
    Take q such that NSet(n,q) [= B.
    Let us show that for all a,b
        a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
    proof.
        Assume that a = b (mod p * q).
        Take m such that (p * q) * m = a - b.
        We have p * (q * m) = a - b = q * (p * m).
    end.
    Then NSet(n,p*q) is a subset of A and a subset of B.
qed.

Lemma UnionClosed.  Let A,B be closed intsets.
                    A \-/ B is closed.
Proof.
    ~(A \-/ B) = ~A /-\ ~B.
qed.

Axiom IUnionClosed. Let S be a finite set such that
                        all elements of S are closed intsets.
                    \-/ S is closed.

Lemma ClosedNSet.   NSet(a,q) is closed.
Proof.
    If b << ~NSet(a,q) /\ c = b (mod q) then c << ~NSet(a,q).
qed.

Theorem Fuerst.     Let S = { NSet(0,r) | r is a prime }.
                    S is infinite.
Proof.
    We have ~ \-/ S = {1, -1}.
    Indeed n belongs to \-/ S iff n has a prime divisor.

    Assume that S is finite.
    Then \-/ S is closed and ~ \-/ S is open.

    Take p such that NSet(1,p) [= ~ \-/ S.
    NSet(1,p) has an element that does not belong to {1, -1}.
    proof.
        1 + p and 1 - p belong to NSet(1,p).
        1 + p !=  1 /\ 1 - p !=  1.
        1 + p != -1 \/ 1 - p != -1.
    end.
    We have a contradiction.
qed.

[quit]

STATISTICS

[ForTheL] fuerst-int.ftl: parsing successful
[Reason] fuerst-int.ftl: verification started
[Reason] line 31: goal: a * 0 = 0 = 0 * a.
[Reason] line 32: goal: -1 * a = -a = a * -1.
[Reason] line 49: goal: a = a (mod q).
[Reason] line 54: goal: Take n such that q * n = a - b.
[Reason] line 55: goal: We have q * -n = b - a.
[Reason] line 51: goal: a = b (mod q) => b = a (mod q).
[Reason] line 61: goal: Take n such that q * n = a - b.
[Reason] line 62: goal: Take m such that q * m = b - c.
[Reason] line 63: goal: We have q * (n + m) = a - c.
[Reason] line 58: goal: a = b (mod q) /\ b = c (mod q) => a = c (mod q).
[Reason] line 136: goal: \-/ S is open.
[Reason] line 142: goal: Then n belongs to A and n belongs to B.
[Reason] line 143: goal: Take p such that NSet(n,p) [= A.
[Reason] line 144: goal: Take q such that NSet(n,q) [= B.
[Reason] line 149: goal: Take m such that (p * q) * m = a - b.
[Reason] line 150: goal: We have p * (q * m) = a - b = q * (p * m).
[Reason] line 145: goal: for all a,b a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
[Reason] line 152: goal: Then NSet(n,p*q) is a subset of A and a subset of B.
[Reason] line 139: goal: A /-\ B is open.
[Reason] line 158: goal: ~(A \-/ B) = ~A /-\ ~B.
[Reason] line 156: goal: A \-/ B is closed.
[Reason] line 167: goal: If b << ~NSet(a,q) /\ c = b (mod q) then c << ~NSet(a,q).
[Reason] line 165: goal: NSet(a,q) is closed.
[Reason] line 174: goal: n belongs to \-/ S iff n has a prime divisor.
[Reason] line 173: goal: We have ~ \-/ S = {1, -1}.
[Reason] line 177: goal: Then \-/ S is closed and ~ \-/ S is open.
[Reason] line 179: goal: Take p such that NSet(1,p) [= ~ \-/ S.
[Reason] line 182: goal: 1 + p and 1 - p belong to NSet(1,p).
[Reason] line 183: goal: 1 + p != 1 /\ 1 - p != 1.
[Reason] line 184: goal: 1 + p != -1 \/ 1 - p != -1.
[Reason] line 180: goal: NSet(1,p) has an element that does not belong to {1, -1}.
[Reason] line 186: goal: We have a contradiction.
[Reason] line 171: goal: S is infinite.
[Reason] fuerst-int.ftl: verification successful
[Main] sections 150 - goals 33 - subgoals 229 - trivial 56 - proved 99
[Main] symbols 470 - checks 376 - trivial 337 - proved 39 - unfolds 419
[Main] parser 00:00.13 - reason 00:08.35 - prover 02:35.82/00:02.93
[Main] total 02:44.31

