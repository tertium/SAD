[a natural number/numbers] [the zero] [the successor of x]
[0 @ the zero] [succ x @ the successor of x]
[x is nonzero @ x is not equal to 0]

Signature NatSort. Natural number is a notion.

Let i,j,k,l,m,n be natural numbers.

Signature ZeroNat.  0 is a natural number.
Signature SuccNat.  The successor of n is a nonzero natural number.

Axiom NatExtr.      For every nonzero m there exists n such that m = succ n.
Axiom SuccEqu.      succ m = succ n  =>  m = n.

Signature IHOrd.    m -<- n is a relation.
Axiom IH.           n -<- succ n.


[a scalar/scalars]
[the sum of x and y] [x + y @ the sum of x and y]
[the product of x and y] [x * y @ the product of x and y]
[the inverse of x] [-x @ the inverse of x] [x - y @ x + -y]
[the square of x @ x * x] [sq x @ the square of x]
[the scalar zero] [00 @ the scalar zero]

Signature ScSort.   Scalar is a notion.

Let u,v,w,x,y,z be scalars.

Signature SZeroSc.  00 is a scalar.
Signature SumSc.    x + y is a scalar.
Signature MulSc.    x * y is a scalar.
Signature NegSc.    -x is a scalar.

Axiom ScZero.       x + 00 = x  and 00 + x = x
                and x * 00 = 00 and 00 * x = 00
                and x + -x = 00 and -x + x = 00
                and --x = x and -00 = 00.

Axiom Arith.        (x + y) + z = x + (y + z) and x + y = y + x and
                    (x * y) * z = x * (y * z) and x * y = y * x.

Axiom Distr.        x * (y + z) = (x * y) + (x * z) and
                    (x + y) * z = (x * z) + (y * z).

Lemma Distr2.       (x + y) * (u + v) =
                        ((x * u) + (x * v)) + ((y * u) + (y * v)) (by Distr).
Proof.
    (x + y) * (u + v) = (x * (u + v)) + (y * (u + v)).
end.

Axiom MNeg.         x * -y = -(x * y) and -x * y = -(x * y).
Lemma MDNeg.        -x * -y = x * y.


[x is lessorequal than y] [x <= y @ x is lessorequal than y]
[x is nonnegative @ 00 <= x]

Signature.      x <= y is a relation.

Axiom _LERef.   x <= x.
Axiom LEASm.    x <= y /\ y <= x => x = y.
Axiom LETrn.    x <= y /\ y <= z => x <= z.
Axiom LEMon.    x <= y /\ u <= v => x + u <= y + v.
Axiom LEMonM.   x <= y /\ 00 <= u /\ u <= v => x * u <= y * v.
Axiom LETot.    x <= y \/ y <= x.

Axiom PosMon.   00 <= x /\ 00 <= y => 00 <= x + y /\ 00 <= x * y.
Axiom SqPos.    00 <= sq x.
Axiom Sqrt.     00 <= x /\ 00 <= y /\ sq x = sq y => x = y.


[a vector/vectors]
[the dimension/dimensions of x] [Dim x @ the dimension of x]
[the coordinate no n of x] [x[n] @ the coordinate no n of x]
[the lastaxe projection of x] [init x @ the lastaxe projection of x]
[x is equidimensional to y @ Dim x = Dim y]

Signature VcSort.   Vector is a notion.

Let p,q,r,s,t be vectors.

Signature DimNat.   Dim s is a natural number.
Signature ElmSc.    s[n] is a scalar.

Definition DefInit. Let s be a vector of a nonzero dimension.
    init s is a vector such that succ Dim init s = Dim s and
        for every natural number n  (init s)[n] = s[n].



[the scalar product of x and y] [x ** y @ the scalar product of x and y]
[the scalar square of x @ x ** x] [scsq x @ the scalar square of x]

Signature ScPr. Let s,t be equidimensional vectors. s ** t is a scalar.

Axiom DefScPrZ. For all s,t with dimensions equal to zero
                    s ** t = 00.

Axiom DefScPrN. For all equidimensional s,t with nonzero dimensions
                    s ** t = (init s ** init t) + (s[Dim s] * t[Dim t]).

#Lemma ScPrSc.  For all equidimensional vectors s,t  s ** t is a scalar.
#Proof by induction on Dim s.
#    Let s,t be equidimensional vectors.
#    Suppose that Dim s is nonzero.
#    init s, init t are equidimensional. # (by SuccEqu).
#    Hence the thesis (by IH,DefScPrN).
#qed.

Lemma ScSqPos.  For all vectors s scsq s is nonnegative.
Proof by induction on Dim s.
    Let s be a vector.
    Suppose that Dim s is nonzero.
    Then scsq s = scsq init s + sq s[Dim s].
    Hence the thesis (by IH,SqPos,ScPrSc,PosMon).
qed.

Theorem Main.
    For all equidimensional s,t
        sq (s ** t) <= scsq s * scsq t.
Proof by induction on Dim s.
    Let s,t be equidimensional vectors.
    Case Dim s = 0. Obvious.
    Case Dim s is nonzero.
        Take a vector p equal to init s.
        Take a vector q equal to init t.

        Take a scalar A equal to s[Dim s].
        Take a scalar B equal to t[Dim t].
        Take a scalar C equal to scsq p.
        Take a scalar D equal to scsq q.
        Take a scalar E equal to p ** q.
        Take a scalar F equal to sq A.
        Take a scalar G equal to sq B.
        Take a scalar H equal to A * B.
        Take a scalar R equal to C * G.
        Take a scalar P equal to E * H.
        Take a scalar S equal to F * D.
        Take a scalar N equal to R * S.

        sq E <= C * D.

        Let us show that P + P <= R + S.

            Show sq P <= N.
                sq P = sq H * sq E (by Arith).
                N = sq H * (C * D) (by Arith).
                Hence the thesis (by LEMonM,SqPos).
            end.

            Show sq P + sq P <= sq R + sq S.
                R * -S = -N and -S * R = -N and sq -S = sq S.
                sq (R - S) = (sq R - N) + (-N + sq S) (by Distr2).
                sq (R - S) = (sq R - N) + (sq S - N) (by Arith).
                sq (R - S) = ((sq R + sq S) - N) - N (by Arith).
                (sq (R - S) + N) + N = sq R + sq S (by Arith, ScZero).
                00 <= sq (R - S). N + N <= sq R + sq S (by LEMon, ScZero).
                Hence the thesis (by LEMon, LETrn).
            end.

            ((sq P + sq P) + sq P) + sq P <= ((sq R + sq S) + N) + N (by LEMon).
            ((sq R + N) + sq S) + N = (sq R + N) + (sq S + N) (by Arith).
            (sq P + sq P) + (sq P + sq P) <= (sq R + (R * S)) + ((S * R) + sq S) (by Arith).

            Then sq (P + P) <= sq (R + S) (by Distr2).

            Assume the contrary.
            Then R + S <= P + P.
            R + S, P + P are nonnegative.
            Then sq (R + S) <= sq (P + P).
            Then R + S = P + P (by LEASm,Sqrt).
            We have a contradiction.
        end.

        sq E + ((P + P) + sq H) <= (C * D) + ((R + S) + sq H) (by LEMon).
        (sq E + (E * H)) + ((H * E) + sq H) <= ((C * D) + (C * G)) + ((F * D) + (F * G)) (by Arith).
        Hence the thesis (by DefScPrN,Distr2).
    end.
qed.
