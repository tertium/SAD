[set/sets] [element/elements] [belongs/belong]
[subset/subsets]

Signature SetSort.  A set is a notion.
Let S,T denote sets.

Signature ElmSort.  An element of S is a notion.
Let x belongs to X stand for x is an element of X.

Definition DefSubset.   A subset of S is a set T
    such that every element of T belongs to S.

Definition DefEmpty.    S is empty iff S has no elements.

Axiom ExEmpty.  There exists an empty set.

# To prove the following proposition, we must unfold
# the definition of 'empty' in ExEmpty. Currently, we
# never unfold in the global context, so, if you want
# to verify this text in flat mode, use --filter off.

Proposition.
    S is a subset of every set iff S is empty.
Proof.
    Case S is empty. Obvious.       # so we assume S != {}

    Case S is a subset of every set.
        Take an empty set E.
        Take an element z of S.     # that's why z exists
        Then z is an element of E.
        We have a contradiction.
    end.
qed.
