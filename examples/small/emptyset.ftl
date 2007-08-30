[a set/sets] [an element/elements of x]
[x is in/from y @ x is an element of y]
[x belongs/belong to y @ x is in y]
[a subset/subsets of x] [x is empty]

Signature SetSort.  Set is a notion.
Let S denote sets.

Signature ElmSort.  Element of S is a notion.

Definition DefSubset.   
    A subset of S is a set T such that
    every element of T belongs to S.

Definition DefEmpty.
    S is empty iff S has no elements.

Axiom ExEmpty. There exists an empty set.

Proposition.
    S is a subset of every set iff S is empty.
Proof.
  First assume S is a subset of every set.
    Then S is empty.
    Indeed
      Let z be in S and E be an empty set.
      Then z is an element of E.
      We have a contradiction.
    end.
  end.
  Now assume S is empty.
    Let T be a set.
    Every element of S is in T.
    Hence S is a subset of T.
  end.
qed.

