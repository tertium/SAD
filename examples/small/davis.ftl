[set/sets] [element/elements] [belongs/belong]
[subset/subsets]

Signature SetSort.  A set is a notion.
Let S,T denote sets.

Signature ElmSort.  An element of S is a notion.
Let x belongs to X stand for x is an element of X.

Let an element stand for an element of some set.

Definition DefSubset.   A subset of S is a set T
    such that every element of T belongs to S.

Signature CloseSort.    Let x,y be elements.
    x is close to y is an atom.

Signature NstSort.  S* is a set.

Axiom NstSubset.    Let T be a subset of S.
                    Then T* is a subset of S*.

Definition DefClosed.   S is closed iff
    for every element x
        if some element of S* is close to x
                            then x belongs to S.

Definition DefCompact.  S is compact iff
    every element of S* is close to some element of S.

Proposition.
    Every closed subset of every compact set is compact.
