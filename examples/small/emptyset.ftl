[set/-s] [element/-s] [belong/-s] [subset/-s]

Signature SetSort.  A set is a notion.
Let S,T denote sets.

Signature ElmSort.  An element of S is a notion.
Let x belongs to X stand for x is an element of X.

Definition DefSubset.   A subset of S is a set T
    such that every element of T belongs to S.

Definition DefEmpty.    S is empty iff S has no elements.

Axiom ExEmpty.  There exists an empty set.

Proposition.
    S is a subset of every set iff S is empty.
Proof.
    Case S is empty. Obvious.

    Case S is a subset of every set.
        Take an empty set E.
        Let z be an element of S.
        Then z is an element of E.
        We have a contradiction.
    end.
qed.
