[an element/elements] [a relation/relations]
[R holds on x and y] [R[x,y] @ R holds on x and y]
[R is symmetric] [R is transitive] [R is total]
[R is complement to Q]

#Signature.  Element is a notion.
#Signature.  Relation is a notion.

Let x,y,z denote elements.
Let P,Q,R denote relations.

#Signature.  P[x,y] is a relation.

Definition. R is symmetric iff for all x,y 
            (R[x,y] => R[y,x]).

Definition. R is transitive iff for all x,y,z
            (R[x,y] /\ R[y,z] => R[x,z]).

Definition. R is total iff for all x,y R[x,y].

Definition. R and Q are complement iff for all x,y
            (Q[x,y] \/ R[x,y]).

Proposition.
    Let R, Q be transitive complement relations.
    Assume R is symmetric. Then R is total or Q is total.
