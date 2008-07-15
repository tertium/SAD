#
# Natural numbers
#

[number/-s]

Signature Naturals. An natural number is a notion.

Let a,b,c,d,i,j,k,l,m,n stand for natural numbers.

Signature NatZero.  0 is an natural number.
Signature NatOne.   1 is an natural number.

Let x is nonzero stand for x != 0.

Let p,q stand for nonzero natural numbers.

Signature EquMod.   a = b (mod q) is an atom.

Axiom EquModRef.    a = a (mod q).
Axiom EquModSym.    a = b (mod q) => b = a (mod q).
Axiom EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).

Axiom Infinite.     Let a,q be natural numbers and q be nonzero.
                    There exists a natural number aplusq such that
                        aplusq != a and aplusq = a (mod q).

Axiom CommonMul.    Let p,q be nonzero natural numbers.
                    There exists a nonzero natural number pmulq
                        such that for all a,b if a = b (mod pmulq)
                            then a = b (mod p) and a = b (mod q).

[divisor/-s] [prime/-s]

Definition Divisor. A divisor of a is a nonzero natural number n
                        such that a = 0 (mod n).

Signature Prime.    p is prime is an atom.

Let a prime stand for a prime nonzero natural number.

Axiom PrimeDivisor. n has a prime divisor if and only if n != 1.


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
# Sets of natural numbers
#

[natset/-s]

Let a natset stand for a set S such that
    every element of S is a natural number.

Let A,B,C,D stand for natsets.

Definition ZSetUnion.
    A \-/ B = { natural number x | x << A \/ x << B }.

Definition ZSetInter.
    A /-\ B = { natural number x | x << A /\ x << B }.

Definition InnerUnion.
    Let S be a set such that every element of S is a natset.
    \-/ S = { natural number x | x belongs to some element of S }.

Definition NatSetCompl.
    ~ A = { natural number x | x does not belong to A }.


#
# Introducing topology
#

Definition NSet.    NSet(a,q) = { b | b = a (mod q) }.

Definition Open.    A is open iff for any a << A
                    there exists q such that NSet(a,q) [= A.

Definition Closed.  A is closed iff ~A is open.

Lemma UnionOpen.    Let S be a set such that
                        all elements of S are open natsets.
                    \-/ S is open.

Lemma InterOpen.    Let A,B be open natsets.
                    A /-\ B is open (by CommonMul).

Lemma UnionClosed.  Let A,B be closed natsets.
                    A \-/ B is closed (by CommonMul).

Axiom IUnionClosed. Let S be a finite set such that
                        all elements of S are closed natsets.
                    \-/ S is closed.

Lemma ClosedNSet.   NSet(a,q) is closed.

Theorem Fuerst.     Let S = { NSet(0,r) | r is a prime }.
                    S is infinite.
Proof.
    We have ~ \-/ S = {1, 1}.
    Indeed n belongs to \-/ S iff n has a prime divisor.

    Assume that S is finite.
    Then \-/ S is closed and ~ \-/ S is open.

    Take p such that NSet(1,p) [= ~ \-/ S.
    Take n << NSet(1,p) such that n != 1.
    We have n << ~ \-/ S and n << \-/ S.
qed.

[quit]

REMARKS

The formalization above is the Fuerstenberg's topological
proof of the infinitude of primes - with some deviations.

First of all, we define NSet(a,q) not as the arithmetic
progression { a + qn | n << Z } but as the equivalence
class { b | b = a (mod q) }. By doing so, we can make
use of the equivalence properties of equality modulo.
In particular, the lemma ClosedNSet becomes trivial
compared to the explicit construction of ~NSet(a,q)
in the original proof.

We can go further and take equality modulo as a basic
relation, keeping off the whole integer arithmetics.
We postulate the equivalence properties and add the
axioms Infinite and CommonMul - which appear the only
facts about integers we need for the proof. Similarly,
the only fact we need to know about primes is that
any integer except 1 and -1 has a prime divisor.

If we take these few (pretty trivial) properties
as axioms, we find that we don't even need integers:
natural numbers suffice. It could be more convenient
to define equality modulo for integers than for
natural numbers, but other than that we do not
use the properties of integers at all.

As far as induction is concerned, there are three places
in our development which would require it in a full-blown
formalization. First, to deduce PrimeDivisor from the
definition of a prime number (induction by the absolute
value of a dividend). Then, to deduce IUnionClosed from
UnionClosed (induction by the cardinality of a finite set).
And, finally, to prove that the set of primes is finite
if and only if the set S = { NSet(0,r) | r is a prime }
(from the main theorem) is finite. Note that our Fuerst
theorem only proves the infinitude of S (to me, this is
the most annoying deficiency of our formalization).


Technical remarks.

1. I would be happy to write 'a set of natural numbers'
instead of 'a natset'. Alas, 'the set of natural numbers'
means something entirely different, and I tried hard to
make ForTheL as article-indifferent as possible. Today,
'[a|the] set of apples' stands for { a | a is an apple }
and the guards in InnerUnion and IUnionClosed are ugly.

2. I write {1, 1} instead of {1} to evade a parser bug,
which I'm going to fix Really Soon Now. Idem for a couple
of other inconveniences in the set comprehension syntax.


Vague thoughts.

The present formalization differs a fair bit from the
original presentation. Partly, it is because of various
shortcomings of (the current versions of) formalization
language and verification machinery: see all the places
where we avoid talking about finite and infinite sets.
For example, the original proof quickly observes that
any NSet(a,q) is infinite, hence any nonempty open set
is infinite, hence {-1,1} can not be open. In ForTheL,
currently, it is easier to show directly that {-1,1}
can not contain NSet(a,q) than to prove that the former
set is finite and the latter is not.

Nevertheless, I see some changes as improvements of
the original proof: mainly the definition of NSet(a,q)
in terms of equality modulo instead of progressions.
It was a real pleasure to me to find that the lemma
ClosedNSet does not require a written proof at all;
I shudder to think about formalizing and verifying
NSet(a,q) = ~ \-/ { NSet(a+j, q) | 1 =< j =< a-1 }.
I also think that the proof in hand perfectly fits
into the domain of natural numbers; the integers
should have never been invoked in the first place.
(Was it just because it is much easier to define
a bi-infinite arithmetic progression starting with
a given integer than an arithmetic progression
passing through a given natural number?)

For better or for worse, you most often cannot
formalize a proof without tweaking it. It's by
looking for a best tweak (to make it shorter,
to make it cleaner, to make it more suitable
for your formalism) that you grasp the proof
better - and have fun.

STATISTICS

[ForTheL] fuerst-nat.ftl: parsing successful
[Reason] fuerst-nat.ftl: verification started
[Reason] line 108: goal: \-/ S is open.
[Reason] line 111: goal: A /-\ B is open (by CommonMul).
[Reason] line 114: goal: A \-/ B is closed (by CommonMul).
[Reason] line 120: goal: NSet(a,q) is closed.
[Reason] line 126: goal: n belongs to \-/ S iff n has a prime divisor.
[Reason] line 125: goal: We have ~ \-/ S = {1, 1}.
[Reason] line 129: goal: Then \-/ S is closed and ~ \-/ S is open.
[Reason] line 131: goal: Take p such that NSet(1,p) [= ~ \-/ S.
[Reason] line 132: goal: Take n << NSet(1,p) such that n != 1.
[Reason] line 133: goal: We have n << ~ \-/ S and n << \-/ S.
[Reason] line 123: goal: S is infinite.
[Reason] fuerst-nat.ftl: verification successful
[Main] sections 91 - goals 11 - subgoals 135 - trivial 34 - proved 56
[Main] symbols 252 - checks 199 - trivial 169 - proved 30 - unfolds 278
[Main] parser 00:00.05 - reason 00:00.21 - prover 00:42.62/00:00.22
[Main] total 00:42.90

