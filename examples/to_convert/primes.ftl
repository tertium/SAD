[number/numbers]

Signature NumSort.  A number is a notion.

Let x,y,z,u,v,w denote numbers.

Signature NatSort.  x is natural is an atom.

Let k,l,m,n denote natural numbers.

Signature SortsC.  0 is a natural number.

Let x is nonzero stand for x != 0.

Signature SortsC.  1 is a nonzero natural number.

Let x is nontrivial stand for x != 0 and x != 1.

Signature SortsB.  x + y is a number.
Signature SortsB.  x * y is a number.

Axiom SortsB.  m + n is natural.
Axiom SortsB.  m * n is natural.

Axiom AddComm.   x + y = y + x.
Axiom AddAsso.  (x + y) + z = x + (y + z).
Axiom _AddZero.  x + 0 = x = 0 + x.

Axiom MulComm.   x * y = y * x.
Axiom MulAsso.  (x * y) * z = x * (y * z).
Axiom _MulUnit.  x * 1 = x = 1 * x.
Axiom _MulZero.  x * 0 = 0 = 0 * x.

Axiom AMDistr.  x * (y + z) = (x * y) + (x * z) and
                (y + z) * x = (y * x) + (z * x).

Axiom AddCanc.  If (u + x = u + y \/ x + u = y + u) then x = y.

Axiom MulCanc.
    If (u * x = u * y \/ x * u = y * u) then u = 0 \/ x = y.

Axiom ZeroAdd.  If x + y = 0 then x = 0 /\ y = 0.
Lemma ZeroMul.  If x * y = 0 then x = 0 \/ y = 0.

Definition DefLE.   x <= y <=> exists z : x + z = y.

Definition DefDiff.  Assume that y <= x.
    x - y is a number z such that y + z = x.

Axiom NatDiff.  If m <= n then n - m is natural.

Lemma LERefl.   x <= x.

Lemma LEAsym.   x <= y <= x  =>  x = y.
Proof.
    Assume that x <= y <= x.
    We have x + ((y - x) + (x - y)) = x + 0.
    Hence (y - x) = 0 and (x - y) = 0.
qed.

Lemma LETran.   x <= y <= z  =>  x <= z.

Let x < y stand for x <= y and x != y.

Axiom LETotal.  x <= y \/ y < x.

Lemma MonAdd.   Assume that z < y.
    Then x + z < x + y and z + x < y + x.
Proof.
    (x + z) + (y - z) = x + y.
qed.

Lemma MonMul.   Assume that x is nonzero and z < y.
    Then x * z < x * y and z * x < y * x.
Proof.
    (x * z) + (x * (y - z)) = x * y (by AddComm, AMDistr).
qed.

Axiom LENTr.    n = 0 \/ n = 1 \/ 1 < n.

Lemma MonMul2.  m != 0 => n <= n * m.

Signature IH.   n -<- m is a relation.
Axiom IH.       n < m => n -<- m.

[quit]

[n divides/divide m] [n | m @ n divides m] [n is dividing m @ n | m]
[a divisor/divisors of n @ a natural number dividing n]
[the quotient of n to m] [n / m @ the quotient of n to m]

Definition DefDiv. Let n,m be natural numbers.
    n divides m iff for some natural number p (m = n * p).

#Axiom _QuotNat. Let n,m be natural numbers and m be nonzero.
#    n / m is a natural number.

Definition DefQuot. Let n,m be natural numbers and m != 0 and m | n.
    n / m is a natural number such that 
        (n / m) * m = n and m * (n / m) = n.


Lemma DivTrans. Let l,m,n be natural numbers.
    If l | m and m | n then l | n (by DefDiv,MulAsso).

Lemma DivSum. Let l,m,n be natural numbers.
    If l | m and l | n then l | m + n.
Proof.
    Suppose that l | m and l | n.
    Take a natural number p such that m = l * p.
    Take a natural number q such that n = l * q.
    Then m + n = l * (p + q) (by AMDistr).
    Hence the thesis. # (by DefDiv).
qed.

Lemma DivMin. Let l,m,n be natural numbers.
    If l | m and l | m + n then l | n.
Proof.
    Suppose that l | m and l | m + n.
    Take a natural number p such that m = l * p.
    Take a natural number q such that m + n = l * q. # (by DefDiv).
    Case q < p.
        Take a natural number r equal to p - q (by NatDiff).
        We have (l * q) = ((l * q) + (l * r)) + n (by AMDistr).
        Then (l * r) + n = 0 (by AddAsso, AddCanc). Hence n = 0.
    end.
    Case p <= q.
        Take a natural number r equal to q - p (by NatDiff).
        We have (l * p) + (l * r) = (l * p) + n (by AMDistr).
        Hence the thesis (by AddCanc). # ,DefDiv).
    end.
qed.

Lemma DivLE. Let m,n be natural numbers.
    Assume that m | n and n is nonzero.
    Then m <= n.
Proof.
    Take a natural number q such that n = m * q.
    q is nonzero.
qed.

[x is prime] [x is compound @ x is not prime]

Definition DefPrime. Let n be a natural number.
    n is prime iff n is nontrivial and
        for every divisor m of n (m = 1 \/ m = n).

Lemma PrimNTR. Every natural prime number is nontrivial.

Lemma PrimDiv. Every nontrivial natural number k has a prime divisor.
Proof by induction.
    Let k be a nontrivial natural number.
    Case k is prime. Obvious.
    Case k is compound.
        Take a divisor q of k such that q != 1 and q != k.
        q is nontrivial and q < k.
        Take a prime divisor r of q.
        Then r divides k (by MulAsso). #, DefDiv).
    end.
qed.

Lemma PDP.  For all natural numbers n,m,p
  if p is prime and p | n * m then p | n or p | m.
Proof by induction on ((n + m) + p).
  Let n,m,p be natural numbers.
  Assume that p is prime and p divides n * m.

  Case p <= n.
    Let us show that p divides (n - p) * m and n - p < n.
      n = p + (n - p) and n * m = p * ((n * m) / p).
      n * m = (p * m) + ((n - p) * m) (by AMDistr).
      p divides (n - p) * m (by DefDiv, DivMin). ## BAD
    end.
    Then p divides n - p or p divides m (by IH).
    Indeed ((n - p) + m) + p < (n + m) + p (by MonAdd). end.
    If p divides n - p then p divides n (by DefDiv,DivSum). ## DAD
  end.

  Case p <= m.
    Let us show that p divides n * (m - p) and m - p < m.
      m = p + (m - p) and n * m = p * ((n * m) / p).
      n * m = (p * n) + (n * (m - p)) (by MulComm,AMDistr).
      p divides n * (m - p) (by DefDiv, DivMin). ## BAD
    end.
    Then p divides n or p divides m - p (by IH).
    Indeed (n + (m - p)) + p < (n + m) + p (by MonAdd). end.
    If p divides m - p then p divides m (by DefDiv,DivSum). ## BAD
  end.

  Case n < p and m < p.
    Take a natural number k such that n * m = p * k.

    Case k = 0 \/ k = 1.
      If k = 1 then n = p or m = p (by MulComm). # ,DefPrime,DefDiv).
    end.

    Case k != 0 /\ k != 1.
      Take a prime divisor r of k.
      Let us show that r divides n * m and r <= k and k < p.
        k = (k / r) * r and n * m = (p * (k / r)) * r.
        Assume that p <= k. Then we have k > m.
        p * k > p * m and p * m > n * m (by MonMul).
        Then p * k > n * m. We have a contradiction.
      end.

      Then r divides n or r divides m (by IH).
      Indeed (n + m) + r < (n + m) + p. end.

      Case r divides n.
        Let us prove that p divides (n / r) * m and (n / r) < n.
            k = (k / r) * r and n * m = (p * (k / r)) * r.
            n = (n / r) * r and n * m = ((n / r) * m) * r.
            Then p * (k / r) = (n / r) * m (by MulCanc).
            Hence p divides (n / r) * m (by DefDiv). ## BAD
[tlim 12]
        end.
[tlim 3]
        Then p divides (n / r) or p divides m (by IH).
        Indeed ((n / r) + m) + p < (n + m) + p (by MonAdd). end.
        If p divides (n / r) then p divides n.
        Indeed (n / r) divides n (by DefDiv). end. ## BAD
      end.

      Case r divides m.
        Let us prove that p divides n * (m / r) and (m / r) < m.
            k = (k / r) * r and n * m = (p * (k / r)) * r.
            m = (m / r) * r and n * m = (n * (m / r)) * r.
            Then p * (k / r) = n * (m / r) (by MulCanc).
            Hence p divides n * (m / r) (by DefDiv). ## BAD
[tlim 12]
        end.
[tlim 3]
        Then p divides n or p divides (m / r) (by IH).
        Indeed (n + (m / r)) + p < (n + m) + p (by MonAdd). end.
        If p divides (m / r) then p divides m.
        Indeed (m / r) divides m (by DefDiv). end. ## BAD
      end.
    end.
  end.
qed.


[x is relatively prime to y]
[x is rational] [the square of n @ n * n]

Definition DefRelPr. Let n,m be natural numbers.
    n,m are relatively prime iff n,m have no common nontrivial divisor.

Definition DefRat. Let q be a number.
    q is rational iff there exist natural relatively prime numbers n,m
        such that m is nonzero and q * m = n.


Theorem Main.  Let p be a natural prime number.
  For no rational number q the square of q is p.
Proof by contradiction.
  Let q be a rational number such that q * q = p.
  Take natural relatively prime numbers n,m
                    such that q * m = n. # (by DefRat).
  Then p * (m * m) = (n * n) (by MulAsso,MulComm).
  Hence p divides n * n and p divides n. # (by DefDiv,PDP).
  Choose a natural number k such that n = p * k. # (by DefDiv).
  Then we have p * (m * m) = p * (k * n) (by MulAsso).
  The square of m is equal to (p * k) * k (by MulComm,MulCanc).
  Hence p divides m * m and p divides m (by MulAsso,DefDiv,PDP). ## BAD
  We have a contradiction (by DefRelPr). ## BAD
qed.

