# Chapter 3: Runge–Kutta Methods

Pages 137-315

## Sections

- **30** Preliminaries
- **31** Order Conditions
- **32** Low Order Explicit Methods
- **33** Runge–Kutta Methods with Error Estimates
- **34** Implicit Runge–Kutta Methods
- **35** Stability of Implicit Runge–Kutta Methods
- **36** Implementable Implicit Runge–Kutta Methods
- **37** Symplectic Runge–Kutta Methods
- **38** Algebraic Properties of Runge–Kutta Methods
- **39** Implementation Issues

## Definitions (18)

### Definition 310A (p.172)
*Section 31, Subsection 310*

```
Definition 310A Given a tree t and a function f : RN → RN , analytic in a
neighbourhood of y, the ‘elementary differential’ F (t)(y) is defined by

                 F (τ )(y) = f (y),                                                                      (310g)
                                            (m)
    F ([t1 , t2 , . . . , tm ]) = f               (y)(F (t1 )(y), F (t2 )(y), . . . , F (tm )(y)).       (310h)

Note that the tensor interpretation of (310h) is written as

           F i ([t1 , t2 , . . . , tm ]) = fji1 ,j2 ,...,jm F j1 (t1 )F j2 (t2 ) · · · F jm (tm ).

   The elementary differentials up to order 5 are shown in Table 310(II). Note
that we use the same abbreviation as in Table 310(I), in which f, f  , . . . denote
f (y(x)), f (y(x)) , . . . . The values of α(t) are also shown; their significance will
be explained in the next subsection.
   As part of the equipment we need to manipulate expressions involving
elementary differentials we consider the value of
                                                 hr(t)           
                                    hf y0 +   θ(t)       F (t)(y0 ) .                                     (310i)
                                                   σ(t)
                                                     t∈T


           Table 310(II)      Elementary differentials for orders 1 to 5
               r(t)      t     α(t) F (t)(y)                   F (t)(y)i
                1               1   f                          fi
                2                1     ff                     fji f j

                3                1     f  (f, f)              i
                                                               fjk fjfk
                3                1     ff f                  fji fkj f k

                4                1     f  (f, f, f)          i
                                                               fjkl f j f kf l
                4                3     f  (f, f  f)          i
                                                               fjk f j flk f l
                4                1     f  f  (f, f)              j k l
                                                               fji fkl f f
                4                1     ff ff                fji fkj flk f l

                5                1     f (4) (f, f, f, f)       i
                                                               fjklm f j f kf lf m
                5                6     f (3) (f, f, f  f)      i
                                                               fjkl f j f k fm
                                                                             l m
                                                                               f
                5                4     f  (f, f  (f, f))    i
                                                               fjk f j flm
                                                                        k
                                                                           f lf m
                5                4     f  (f, f  f  f)      i
                                                               fjk f j flk fm
                                                                            l m
                                                                              f
                5                3     f  (f  f, f  f)      i
                                                               fjk flj f l fm
                                                                            k m
                                                                              f
                5                1     f  f  (f, f, f)          j
                                                               fji fklm f kf lf m
                5                3     f  f  (f, f  f)          j k l m
                                                               fji fkl f fm f
                5                1     f  f  f  (f, f)     fji fkj flm
                                                                        k
                                                                           f lf m

                5                1     ff fff              fji fkj flk fm
                                                                            l m
                                                                              f



As a formal series, this can be evaluated using the following result:
```

**References:**
- uses_equation: `eq:310g`
- uses_equation: `eq:310h`
- uses_equation: `eq:310i`

---

### Definition 312A (p.178)
*Section 31, Subsection 312*

```
Definition 312A Let
                                             c    A
                                                  b
denote the tableau for an s-stage Runge–Kutta method. Then the ‘elementary
weights’ Φ(t), the ‘internal weights’ Φi (t) and the ‘derivative weights’ (Φi D)(t)
for t ∈ T and i = 1, 2, . . . , s are defined by

                                    (Φi D)(τ ) = 1,                                            (312a)
                                                 s
                                        Φi (t) =    aij (Φj D)(t),                             (312b)
                                                      j=1


                                                      k
                        (Φi D)([t1 t2 · · · tk ]) =         Φi (tj ),                          (312c)
                                                      j=1
                                                      s
                                          Φ(t) =            bi (Φi D)(t).                      (312d)
                                                      i=1

This definition is used recursively. First Φi D is found for t = τ , using (312a),
then Φi is evaluated for this single vertex tree, using (312b). This enables
(Φi D)([τ ]), using (312c), and then Φi ([τ ]) to be found for each stage. The
order is built up in this way until (Φi D)(t) is known for any required tree.
Finally, (312d) is used to evaluate Φ(t).
  The notation Φi D is part of a more general scheme, which we introduce in
Subsection 387. In the meantime, D should be thought of as an operator to
be applied to Φi , which replaces the sequence of Taylor coefficient weights in
a stage value by the set of coefficient weights for the stage derivatives.


              Table 312(II)     Elementary weights for orders 1 to 5

            r(t)            t     Φ(t)
                                                        "s
             1                                             i=1 bi
                                                        "s
             2                                             i=1 bi ci
                                                        "s         2
             3                                             i=1 bi ci
                                                        "s
             3                                             i,j=1 bi aij cj

                                                        "s         3
             4                                             i=1 bi ci
                                                        "s
             4                                             i,j=1 bi ci aij cj
                                                        "s               2
             4                                             i,j=1 bi aij cj
                                                        "s
             4                                             i,j,k=1 bi aij ajk ck

                                                        "s        4
             5                                           i=1 bi ci
                                                        "s
             5                                                  bi c2i aij cj
                                                        "i,j=1
             5                                           i,j=1 bi ci aij cj
                                                        "s
             5                                                    bi ci aij ajk ck
                                                        "i,j,k=1
                                                         s       "    s          2
             5                                                bi       j=1 aij cj
                                                        "i=1
             5                                           i,j=1 bi aij cj
                                                        "s
             5                                           i,j,k=1 bi aij cj ajk ck
                                                        "s                    2
             5                                           i,j,k=1 bi aij ajk ck
                                                        "s
             5                                           i,j,k,l=1 bi aij ajk akl cl




  An alternative formula for Φ(t), which uses the vertex and edge
characterization of each tree t, is given in the following lemma, which we
state without proof.
```

**References:**
- uses_equation: `eq:312a`
- uses_equation: `eq:312b`
- uses_equation: `eq:312c`
- uses_equation: `eq:312d`
- uses_section: `sec:387`

---

### Definition 323A (p.203)
*Section 32, Subsection 323*

```
Definition 323A Consider a Runge–Kutta method given by the tableau

                                                     c    A
                                                          b       .
For a tree t and stage i, let Φi (t) denote the elementary weight associated with
t for the tableau
                                      c A
                                         ei A .
Stage i has ‘internal order q’, if for all trees such that r(t) ≤ q,
                                                                r(t)
                                                               ci
                                              Φi (t) =              .
                                                               γ(t)

The significance of this definition is that if stage i has internal order q, then,
in any step with initial value yn−1 = y(xn−1 ), the value computed in stage
i satisfies Yi = y(xn−1 + hci ) + O(hq+1 ). Note that the C(q) condition is

necessary and sufficient for every stage to have internal order q, and this is
possible only for implicit methods.
  We are now in a position to generalize the remarks we have made about
third and fourth order methods.
```

---

### Definition 350A (p.251)
*Section 36, Subsection 350*

```
Definition 350A Let α denote an angle satisfying α ∈ (0, π) and let S(α)
denote the set of points x + iy in the complex plane such that x ≤ 0 and
− tan(α)|x| ≤ y ≤ tan(α)|x|. A Runge–Kutta method with stability function
R(z) is A(α)-stable if |R(z)| ≤ 1 for all z ∈ S(α).

The region S(α) is illustrated in Figure 350(i) in the case of the Runge–Kutta
method

        λ              λ                     0                 0
       1+λ             1−λ
        2               2                    λ                 0
                              2
                                      2(1−λ)(1−6λ+6λ2 )
                                                                           (350c)
        1     − (1−λ)(1−9λ+6λ
                   1−3λ+6λ2
                                )
                                          1−3λ+6λ2             λ       ,
                      1+3λ                 2(1−3λ)          1−3λ+6λ2
                    6(1−λ)2                3(1−λ)2           6(1−λ)2

where λ ≈ 0.158984 is a zero of 6λ3 − 18λ2 + 9λ − 1. This value of λ was
chosen to ensure that (350b) holds, even though the method is not A-stable.
It is, in fact, A(α)-stable with α ≈ 1.31946 ≈ 75.5996◦ .
```

**References:**
- uses_equation: `eq:350c`
- uses_equation: `eq:350b`

---

### Definition 355A (p.264)
*Section 36, Subsection 355*

```
Definition 355A The locus of points in the complex plane for which φ(z) =
R(z) exp(−z) is real and positive is said to be the ‘order web’ for the rational
function R. The part of the order web connected to 0 is the ‘principal order
web’. The rays emanating from 0 with increasing value of φ are ‘up arrows’
and those emanating from 0 with decreasing φ are ‘down arrows’.
The up and down arrows leave the origin in a systematic pattern:
```

---

### Definition 356A (p.268)
*Section 36, Subsection 356*

```
Definition 356A A Runge–Kutta method (A, b , c) is ‘AN-stable’ if the
function
                               R(Z) = 1 + b Z(I − AZ)−1 1,
                      '                   (
where Z = diag z1 z2 · · · zs                 is bounded in magnitude by 1 whenever
z1 , z2 , . . . , zs are in the left half-plane.

  It is interesting that a simple necessary and sufficient condition exists for
AN-stability. In Theorem 356C we state this criterion and prove it only in
terms of necessity. Matters become complicated if the method can be reduced
to a method with fewer stages that gives exactly the same computed result.
This can happen, for example, if there exists j ∈ {1, 2, . . . , s} such that
bj = 0, and furthermore, aij = 0 for all i = 1, 2, . . . , s, except perhaps for
i = j. Deleting stage j has no effect on the numerical result computed in a
step. We make a detailed study of reducibility in Subsection 381, but in the
meantime we identify ‘irreducibility in the sense of Dahlquist and Jeltsch’,
or ‘DJ-irreducibility’, (Dahlquist and Jeltsch, 1979) as the property that a
tableau cannot be reduced in the sense of Definition 356B.
```

**References:**
- uses_theorem: `thm:356C`
- uses_definition: `def:356B`
- uses_section: `sec:381`

---

### Definition 356B (p.268)
*Section 36, Subsection 356*

```
Definition 356B A Runge–Kutta method is ‘DJ-reducible’ if there exists a
partition of the stages
                        {1, 2, . . . , s} = S ∪ S0 ,
with S0 non-empty, such that if i ∈ S and j ∈ S0 ,

                               bj = 0 and aij = 0.

The ‘reduced method’ is the method formed by deleting all stages numbered by
members of the set S0 .

  The necessary condition to be given in Theorem 356C will be strengthened
under DJ-irreducibility in Corollary 356D.
```

**References:**
- uses_theorem: `thm:356C`
- uses_corollary: `cor:356D`

**Referenced by:**
- `def:356A` (uses_definition)

---

### Definition 357A (p.271)
*Section 36, Subsection 357*

```
Definition 357A was first introduced, it was referred to as ‘B-stability’, because
it is one step more stringent than A-stability. In the non-autonomous form
in which it seems to be a more useful concept, a more natural name is BN-
stability.
```

---

### Definition 357B (p.271)
*Section 36, Subsection 357*

```
Definition 357B A Runge–Kutta method (A, b , c) is ‘algebraically stable’ if
bi > 0, for i = 1, 2, . . . , s, and if the matrix M , given by

                       M = diag(b)A + A diag(b) − bb ,                     (357d)

is positive semi-definite.
  We now show the sufficiency of this property.
```

**References:**
- uses_equation: `eq:357d`

---

### Definition 370A (p.297)
*Section 36, Subsection 370*

```
Definition 370A A Runge–Kutta method (A, b , c) is symplectic if

                        M = diag(b)A + A diag(b) − bb

is the zero matrix.
The property expressed by Definition 370A was first found by Cooper (1987)
and, as a characteristic of symplectic methods, by Lasagni (1988), Sanz-Serna
(1988) and Suris (1988).
```

---

### Definition 381A (p.302)
*Section 36, Subsection 380*

```
Definition 381A Two Runge–Kutta methods are ‘equivalent’ if, for any
initial value problem defined by an autonomous function f satisfying a
Lipschitz condition, and an initial value y0 , there exists h0 > 0 such that
the result computed by the first method is identical with the result computed
by the second method, if h ≤ h0 .
```

---

### Definition 381B (p.302)
*Section 36, Subsection 380*

```
Definition 381B Two Runge–Kutta methods are ‘Φ-equivalent’ if, for any
t ∈ T , the elementary weight Φ(t) corresponding to the first method is equal
to Φ(t) corresponding to the second method.

   In introducing P -equivalence, we need to make use of the concept of
reducibility of a method. By this we mean that the method can be replaced
by a method with fewer stages formed by eliminating stages that do not
contribute in any way to the final result, and combining stages that are
essentially the same into a single stage. We now formalize these two types
of reducibility.
```

---

### Definition 381C (p.303)
*Section 36, Subsection 380*

```
Definition 381C A Runge–Kutta method (A, b , c) is ‘0-reducible’ if the
stage index set can be partitioned into two subsets {1, 2, . . . , s} = P0 ∪ P1
such that bi = 0 for all i ∈ P0 and such that aij = 0 if i ∈ P1 and j ∈ P0 .
The method formed by deleting all stages indexed by members of P0 is known
as the ‘0-reduced method’.
```

---

### Definition 381D (p.303)
*Section 36, Subsection 380*

```
Definition 381D A Runge–Kutta method (A, b , c) is ‘P -reducible’ if the
stage index set can be partitioned "    into {1, 2, . . . , s} = P1 ∪ P2 ∪ · · · ∪ Ps and
if, for all I, J = 1, 2, . . . , s, j∈PJ aij is constant for all i ∈ PI . The method
                                         "                                "
(A, b , c), with s stages with aIJ = j∈PJ aij , for i ∈ PI , bI = i∈PI bi and
cI = ci , for i ∈ PI , is known as the P -reduced method.
```

---

### Definition 381E (p.303)
*Section 36, Subsection 380*

```
Definition 381E A Runge–Kutta method is ‘irreducible’ if it is neither
0-reducible nor P -reducible. The method formed from a method by first
carrying out a P -reduction and then carrying out a 0-reduction is said to
be the ‘reduced method’.
```

---

### Definition 381F (p.303)
*Section 36, Subsection 380*

```
Definition 381F Two Runge–Kutta methods are ‘P -equivalent’ if each of
them reduces to the same reduced method.
```

---

### Definition 388D (p.322)
*Section 36, Subsection 388*

```
Definition 388D A member α of G1 is in C(ξ) if, for any tree t such that
r(t) ≤ ξ, α(t) = γ(t)−1 α(τ )r(t) and also
                                                 1
                     α([t t1 t2 · · · tm ]) =        α([τ r(t) t1 t2 · · · tm ]),   (388c)
                                                γ(t)
for any t1 t2 · · · tm ∈ T .
```

**References:**
- uses_equation: `eq:388c`

---

### Definition 388F (p.322)
*Section 36, Subsection 388*

```
Definition 388F A member α of G1 is a member of D(ξ) if

                               α(tu) + α(ut) = α(t)α(u),                            (388d)

whenever t, u ∈ T and r(t) ≤ ξ.
```

**References:**
- uses_equation: `eq:388d`

---

## Theorems (56)

### Theorem 301A (p.161)
*Section 30, Subsection 301*

```
Theorem 301A Let t = [tm 1 m2      mk

trees. Then
                                                
                                                k
                                r(t) = 1 +            mi r(ti ),                      (301a)
                                                i=1

                                          k
                                σ(t) =          mi !σ(ti )mi ,                        (301b)
                                          i=1

                                                k
                                γ(t) = r(t)           γ(ti )mi .                      (301c)
                                                i=1

Furthermore,
                           r(τ ) = σ(τ ) = γ(τ ) = 1.                     (301d)
```

<details><summary>Proof</summary>

```
Proof. To verify (301d), calculate r, σ and γ for the single tree with one
vertex. To prove (301a), add the numbers of vertices in the m1 +m2 +· · ·+mk
trees attached to the new root, and add one extra for the new root. In the
calculation of γ(t), the integers attached to the vertices in the m1 + m2 +
· · · + mk trees joined to the new root are the same as in the constituent trees
themselves. The product of these integers, and the integer r(t), gives the result
(301c). Finally, (301b) follows by noting that the permutations which leave
the vertex pairs, making up the list of edges, are just as in the individual
attached trees, together with the additional permutations of the label sets
amongst identical subtrees.                                                    
```
</details>

**References:**
- uses_equation: `eq:301a`
- uses_equation: `eq:301b`
- uses_equation: `eq:301c`
- uses_equation: `eq:301d`

---

### Theorem 302A (p.162)
*Section 30, Subsection 302*

```
Theorem 302A
                                         r(t)!
                               α(t) =           ,                         (302a)
                                       σ(t)γ(t)
                                       r(t)!
                                β(t) =       .                            (302b)
                                       σ(t)
```

<details><summary>Proof</summary>

```
Proof. The value of β(t) is found by labelling the vertices of t with all
permutations and then dividing by σ(t) so as to count, only once, sets of
labellings which are equivalent under symmetry. In the case of α(t), we are
restricted by the requirement that, of the labels assigned to any vertex v and
to its descendants, only the lowest may be assigned to v. The product of the
factors that must be divided out to satisfy this constraint is γ(t).         

  We now look at the enumeration question of the number of rooted trees of
various orders.
```
</details>

**References:**
- uses_equation: `eq:302a`
- uses_equation: `eq:302b`

---

### Theorem 302B (p.163)
*Section 30, Subsection 302*

```
Theorem 302B Let θk , k = 1, 2, 3, . . . denote the number of rooted trees
with exactly k vertices. Then,

      θ1 + θ2 x + θ3 x2 + · · · = (1 − x)−θ1 (1 − x2 )−θ2 (1 − x3 )−θ3 · · · .              (302c)

Before proving this result, we consider how (302c) is to be interpreted. The
right-hand side can be formally expanded as a power series, and it can be seen
that the coefficient of xk depends only on θ1 , θ2 , . . . , θk (and is independent of
any of θ1 , θ2 , . . . if k = 0). Equate this to the coefficient of xk on the left-hand
side and the result is a formula for θk+1 in terms of previous members of the
θ sequence. In particular, k = 0 gives θ1 = 1. We now turn to the justification
of the result.
```

<details><summary>Proof</summary>

```
Proof. Let Θk (U ) denote the number of trees of order k that can be formed
using the operation (t1 , t2 , . . . , tn ) → [t1 , t2 , . . . , tn ], where t1 , t2 , . . . , tn are
all members of U which is assumed to be a subset of T . In particular, Θk (T )
is identical to θk . Let V denote the set U ∪ {t̂}, where t̂ ∈ U . Every tree of the
form [t̂m , . . . ], with order k, is included in a set with Θk (V )−Θk (U ) members.
However, there are the same number of members of this set as there are trees
of order k − r(t̂) of the form [t̂m−1 , . . . ]. Thus, Θk (V ) − Θk (U ) = Θk−r(t̂) (V ),
which is equivalent to

      Θ1 (U ) + Θ2 (U )x + · · · = (1 − xr(t̂) )(Θ1 (V ) + Θ2 (V )x + · · · ).              (302d)

Since
                                Θ1 (U ) + Θ2 (U )x + · · · = 1,
when U is the empty set, we can successively compute the value of this
expression when U = {t1 , t2 , . . . , tn } using (302d) as

                                                        n
                      Θ1 (U ) + Θ2 (U )x + · · · =          (1 − xr(tk ) )−1 .              (302e)
                                                       k=1

Now assume that t1 , t2 , . . . consist of all trees of orders up to some integer p,
and we can write (302e) as


                                                         p
                       Θ1 (U ) + Θ2 (U )x + · · · =          (1 − xk )−θk .
                                                         k=1
                                                                                         %p
Since Θi (U ) = θi if i ≤ p + 1, we obtain the result by replacing
%                                                                                          k=1 by
  ∞
  k=1 .                                                                                           

  The values of θk , computed using Theorem 302B, are shown in Table 302(I)
up to order 10. Also shown are the total numbers of trees up to a given order,
and two further functions equal to the totals of the α(t) and β(t) values for
each order.

       Table 302(I)      Various enumerations of rooted trees up to order 10
                              "n          "                 "
                  n     θn       i=1 θi       r(t)=n α(t)       r(t)=n β(t)
                  1      1           1                1                1
                  2      1           2                1                2
                  3      2           4                2                9
                  4      4           8                6               64
                  5      9          17               24              625
                  6     20          37              120             7776
                  7     48          85              720           117649
                  8    115         200             5040          2097152
                  9    286         486            40320         43046721
                 10    719        1205           362880       1000000000

  The entries in last two columns of Table 302(I) are important in classical
combinatorics, although their roles in our work is only incidental. The sum of
the β(t) for r(t) = n is the number of fully labelled rooted trees with n vertices,
whereas the corresponding sum for α(t) is the number of monotonically
labelled rooted trees. It is easy to guess a formula for each of these totals,
and we now verify these.
                               "                    "
```
</details>

**References:**
- uses_equation: `eq:302c`
- uses_equation: `eq:302d`
- uses_equation: `eq:302e`

---

### Theorem 302C (p.164)
*Section 30, Subsection 302*

```
Theorem 302C Let An = r(t)=n α(t), Bn = r(t)=n β(t). Then
                             An = (n − 1)!,     Bn = nn−1 .
```

<details><summary>Proof</summary>

```
Proof. Let Xn denote the set of vectors of the form [x1 , x2 , . . . , xn−1 ] and Yn
the set of vectors of the form [y1 , y2 , . . . , yn−1 ], where xi ∈ {1, 2, . . . , i} and
yi ∈ {1, 2, . . . , n}, for i = 1, 2, . . . , n. It is easy to see that the cardinalities
of these sets are #Xn = (n − 1)!, #Yn = nn−1 . We conclude the proof by
showing how to define bijections between the monotonically labelled rooted
trees of order n and Xn and between the fully labelled rooted trees of order
n and Yn . In each case, given a labelled rooted tree, let v denote the leaf with
greatest label and assign, as the value of xn−1 or yn−1 , respectively, the label
attached to the parent of v. Delete the leaf v and continue the process until
only the root remains. That is, in step i = 1, 2, . . . , n − 1, we work with a tree
with n + 1 − i vertices. We assign to xn−i (or to yn−i , respectively) the label
attached to the parent of the leaf with the highest remaining label, and then
delete this leaf to yield a tree with n − i vertices.                                    

  Although we have not included details of the bijections involved in this
summarized proof, we illustrate these in the cases n = 4, for monotonically
labelled trees in Table 302(II), and n = 3, for fully labelled trees in Table
302(III).

Table 302(II)     The bijection relating a monotonically labelled fourth order tree t
                                     and x ∈ X4

                     x           t                  x            t                 x                t
                                                                         4                                  4
                                 3
                  [1, 1, 1] 2            4       [1, 1, 2] 3             2     [1, 1, 3] 2                  3
                                     1                               1                                  1
                                                                                                        4
                                         3                   3           4                              3
                  [1, 2, 1] 4            2       [1, 2, 2]           2         [1, 2, 3]                2
                                     1                               1                                  1


  Table 302(III)      The bijection relating a fully labelled third order tree t and
                                        y ∈ Y3

                         y           t             y         t                 y        t
                                                                 3                          2
                      [1, 1] 2               3   [1, 2]          2           [1, 3]         3
                                         1                       1                          1
                                         3                                                  1
                      [2, 1]             1       [2, 2] 1            3       [2, 3]         3
                                         2                       2                          2
                                         2                       1
                      [3, 1]             1       [3, 2]          2           [3, 3] 1           2
                                         3                       3                          3
```
</details>

---

### Theorem 304A (p.167)
*Section 30, Subsection 304*

```
Theorem 304A The generating functions for trees and non-superfluous trees
are
                               x                
                φ(x) = θ(x) −     θ(x)2 − θ(x2 ) ,               (304b)
                               2                
                               x
                ψ(x) = θ(x) −     θ(x)2 + θ(x2 ) .               (304c)
                               2
```

**References:**
- uses_equation: `eq:304b`
- uses_equation: `eq:304c`

---

### Theorem 306A (p.170)
*Section 30, Subsection 306*

```
Theorem 306A
                              
                               m                         1 (#I)
                          f a+   δi =                          f  (a)δI .
                                    i=1
                                                          σ(I)
                                                  I∈Im
```

<details><summary>Proof</summary>

```
Proof. Continue to write ki for the number of occurrences of i in I, so that
                                          (#I)
σ(I)
  %m                "m The coefficient of f
     is given by (306b).                        (a)δI is equal%to the coefficient
of i=1 x in exp ( i=1 xi ). This equals the coefficient of m
           ki
                                                                i=1 x
                                                                      ki
                                                                         in
              1                 1                          1           
     1 + x1 + x21 + · · · 1 + x2 + x22 + · · · · · · 1 + xm + x2m + · · ·
                  2!                             2!                                    2!
and is equal to 1/σ(I).                                                                                       

  We illustrate this result by applying (306A) to the case m = 2, using Table
306(I):

  f (a + δ1 + δ2 ) = f (a) + f  (a)δ1 + f  (a)δ2 + 12 f  (a)(δ1 , δ1 )
                + f  (a)(δ1 , δ2 ) + 12 f  (a)(δ2 , δ2 ) + 16 f  (a)(δ1 , δ1 , δ1 )
        + 12 f  (a)(δ1 , δ1 , δ2 ) + 12 f  (a)(δ1 , δ2 , δ2 ) + 16 f  (a)(δ2 , δ2 , δ2 ) + · · · .
```
</details>

**References:**
- uses_equation: `eq:306b`

**Referenced by:**
- `lem:310B` (uses_theorem)

---

### Theorem 311B (p.175)
*Section 31, Subsection 311*

```
Theorem 311B Let S denote a finite ordered set. Then
                                  
                   y (#S) (y0 ) =      F (|t|)(y0 ).
                                  t∈TS
```

<details><summary>Proof</summary>

```
Proof. In the case |t| = τ , the result is obvious. For the case #S > 1, apply
```
</details>

---

### Theorem 311C (p.175)
*Section 31, Subsection 311*

```
Theorem 311C
                                                
                            y (n) (y(x)) =             α(t)F (t)(y(x)).
                                                t∈Tn

  The alternative approach to finding the Taylor coefficients is based on the
Picard integral equation
                                          ξ
                 y(x0 + hξ) = y(x0 ) + h     f (y(x0 + hξ))dξ,
                                                           0

which, written in terms of Picard iterations, becomes
                                         ξ
              yn (x0 + hξ) = y(x0 ) + h     f (yn−1 (x0 + hξ))dξ,                      (311b)
                                                       0

where the initial iterate is given by
                                         y0 (x + hξ) = y(x0 ).                       (311c)
For n = 1, 2, . . . , we expand yn (x0 + hξ) for ξ ∈ [0, 1], omitting terms that are
O(hn+1 ).
```

**References:**
- uses_equation: `eq:311b`
- uses_equation: `eq:311c`

---

### Theorem 311D (p.176)
*Section 31, Subsection 311*

```
Theorem 311D The Taylor expansion of yn given by (311b) and (311c) is
equal to
                          
                          n                       1
        yn = y(x0 ) +           hi ξ i                   F (t)(y(x0 )) + O(hn+1 ).   (311d)
                          i=1
                                                σ(t)γ(t)
                                         t∈Ti
```

<details><summary>Proof</summary>

```
Proof. The case n = 0 is obvious. We now use induction and suppose that
(311d) is true with n replaced by n − 1. By Lemma 310B, with
                                                          1
                                                θ(t) =        ,
                                                         γ(t)
we have as the coefficient of F (t)(y(x0 ))hr(t) , the expression
          ξ
                 1                              1                    1 r(t)
             %k            ξ r(t)−1 dξ =      %k           ξ r(t) =      ξ ,
          0    i=1 γ(t i )               r(t)  i=1 γ(t i )          γ(t)

where t = [t1 t2 · · · tk ].                                                             
```
</details>

**References:**
- uses_lemma: `lem:310B`
- uses_equation: `eq:311b`
- uses_equation: `eq:311c`
- uses_equation: `eq:311d`

---

### Theorem 313B (p.181)
*Section 31, Subsection 313*

```
Theorem 313B The Taylor expansions for the stages, stage derivatives and
output result for a Runge–Kutta method are
                                 1
       Yi = y0 +                      Φi (t)hr(t) F (t)(y0 )+O(hn+1 ), i = 1, 2, . . . , s, (313c)
                                 σ(t)
                       r(t)≤n
                            1
  hf (Yi ) =                     (Φi D)(t)hr(t) F (t)(y0 ) + O(hn+1 ), i = 1, 2, . . . , s, (313d)
                            σ(t)
               r(t)≤n
                                  1
      y1 = y0 +                        Φ(t)hr(t) F (t)(y0 ) + O(hn+1 ).                         (313e)
                                  σ(t)
                        r(t)≤n
```

<details><summary>Proof</summary>

```
Proof. In a preliminary part of the proof, we consider the sequence of
approximations to Yi given by
                      [0]
                 Yi         = y0 ,                                i = 1, 2, . . . , s,          (313f)
                                       
                                       s                  
                      [k]                            [k−1]
                 Yi         = y0 + h         aij f Yj        ,    i = 1, 2, . . . , s.         (313g)
                                       j=1

                                             [n]
We prove by induction that Yi agrees with the expression given for Yi to
within O(hn+1 ). For n = 0 this is clear. For n > 0, suppose it has been proved
for n replaced by n − 1. From Lemma 313A with k = n − 1 and Yi replaced
     [n−1]
by Yi      , we see that

       [n−1]
                                1
 hf (Yi        )=                    (Φi D)(t)hr(t) F (t)(y0 ) + O(hn+1 ),         i = 1, 2, . . . , s.
                                σ(t)
                      r(t)≤n

                [n]
Calculate Yi     using (313c) and the preliminary result follows. Assume
that h is sufficiently small to guarantee convergence of the sequence
   [0]  [1]  [2]
(Yi , Yi , Yi , . . . ) to Yi and (313c) follows. Finally, (313d) follows from
```
</details>

**References:**
- uses_lemma: `lem:313A`
- uses_equation: `eq:313c`
- uses_equation: `eq:313d`
- uses_equation: `eq:313e`
- uses_equation: `eq:313f`
- uses_equation: `eq:313g`

---

### Theorem 314A (p.182)
*Section 31, Subsection 314*

```
Theorem 314A The values of the elementary differentials for the differential
equation (314b), evaluated at the initial value, are given by

                      F (ti )(y(x0 )) = ei ,             i = 1, 2, . . . , N.

  Because the natural basis vectors e1 , e2 , . . . , eN are independent, there
cannot be any linear relation between the elementary differentials for an
arbitrary differential equation system.
  We illustrate this theorem in the case where U consists of the eight trees
with up to four vertices. Table 314(I) shows the trees numbered from i = 1
to i = 8, together with their recursive definitions in the form (314a) and the
corresponding differential equations. Note that the construction given here is
given as an exercise in Hairer, Nørsett and Wanner (1993) .
```

**References:**
- uses_equation: `eq:314b`
- uses_equation: `eq:314a`

---

### Theorem 315A (p.183)
*Section 31, Subsection 315*

```
Theorem 315A A Runge–Kutta method with elementary weights

                                      Φ : T → R,

has order p if and only if
                          1
                Φ(t) =        , for all t ∈ T such that r(t) ≤ p.              (315a)
                         γ(t)

                                                      1
```

<details><summary>Proof</summary>

```
Proof. The coefficient of F (t)(y0 )hr(t) in (313e) is σ(t) Φ(t), compared with
                                      1
the coefficient in (311d), which is σ(t)γ(t) . Equate these coefficients and we
obtain (315a).                                                             
```
</details>

**References:**
- uses_equation: `eq:315a`
- uses_equation: `eq:313e`
- uses_equation: `eq:311d`

---

### Theorem 317A (p.184)
*Section 31, Subsection 317*

```
Theorem 317A Given a finite subset T0 , of T and a mapping φ : T0 → R,
there exists a Runge–Kutta method such that the elementary weights satisfy

                         Φ(t) = φ(t),           for all t ∈ T0 .
```

<details><summary>Proof</summary>

```
Proof. Let #T0 = n. The set of possible values that can be taken by the
vector of Φ(t) values, for all t ∈ T0 , is a vector space. To see why this is the
case, consider Runge–Kutta methods given by the tableaux
                              c   A                      c   A
                                             and                                   (317a)
                                  b                          b
with s and s stages, respectively. If the elementary weight functions for these
two Runge–Kutta methods are Φ and Φ, then the method given by the tableau
                                      c      A      0
                                      c      0      A
                                            θb     θb

has elementary weight function θΦ+θΦ. Let V ⊂ Rn denote this vector space.
We complete the proof by showing that V = Rn . If this were      " not the case, there
would exist a non-zero function ψ : T0 → R such that t∈T0 ψ(t)Φ(t) = 0,
for all Runge–Kutta methods. Because every coefficient in a Runge–Kutta
tableau can be multiplied by an arbitrary scalar θ to give a new method for
which Φ(t) is replaced by θr(t) Φ(t), we may assume that every non-zero value
of ψ corresponds to trees with the same order k. This is impossible for k = 1,
because in this case there is only a single tree τ . Suppose the impossibility
of this has been proved for all orders less"than k, but that there exist trees
t1 , t2 , . . . , tm , each of order k, such that m
                                                  i=1 ψ(ti )Φ(ti ) = 0, for all Runge–
Kutta methods with ψ(ti ) = 0, for i = 1, 2, . . . , m. Write ti = [tli1i1 tli2i2 · · · ],
for i = 1, 2, . . . , m. Let t̂ denote a tree appearing amongst the tij which does
not occur with the same exponent in each of the ti . Construct an s-stage
Runge–Kutta method
                                            c A
                                                b
for which each of Φ(tij ) = 1, except for Φ(t̂) = θ. Define second Runge–Kutta
tableau with s + 1 stages of the form
                                       c A         0
                                       1 b         0 .
                                         0         1

If qi is the exponent of t̂ in ti , then it follows that
                                   
                                   m
                                          ψ(ti )θ qi = 0.
                                    i=1

Since θ can take any value and since qi is not constant, it is not possible that
ψ is never zero.                                                              
```
</details>

**References:**
- uses_equation: `eq:317a`

**Referenced by:**
- `thm:324B` (uses_theorem)

---

### Theorem 319B (p.190)
*Section 31, Subsection 319*

```
Theorem 319B Let h0 and L be such that the local truncation error at step
k = 1, 2, . . . , n is bounded by

                           δk ≤ Chp+1 ,            h ≤ h0 .

Then the global truncation error is bounded by
                                     
                                   exp(L (x−x0 ))−1
                                         L         Chp ,        L > 0,
              y(xn ) − yn ≤
                                   (x − x0 )Ch ,p
                                                                 L = 0.
```

<details><summary>Proof</summary>

```
Proof. Use Figure 319(ii) and obtain the estimate

                                                   
                                                   n
                     y(xn ) − yn ≤ Chp+1               (1 + hL )k .
                                                   k=1

The case L = 0 is obvious. For the case L > 0, calculate the sum and use
the bound
               (1 + hL )n ≤ exp(L hn) = exp(L (x − x0 )).            
```
</details>

---

### Theorem 323B (p.204)
*Section 32, Subsection 323*

```
Theorem 323B Let
                                               c A 
                                                  b

denote a Runge–Kutta method with s − 1 stages and generalized order p − 1,
satisfying cs−1 = 1. Let q be an integer such that 2q + 2 ≥ p and suppose that
for any i ∈ S ⊂ {1, 2, . . . , s − 1}, the method has internal order q. If there
exists b ∈ Rs , with bs = 0 such that

                                             
                                             s
                                                   bi = 1,                           (323g)
                                             i=1


and such that bi = 0 implies i ∈ S, ci = 1 and bi (1 − ci ) = bi , then the s-stage
method
                                      c A
                                          b

has order p, where c = [ c 1 ] and the s × s matrix A is formed from A     
by adding an additional row with component j ∈ {1, 2, . . . , s − 1} equal to
     "           
 bj − s−1
        i=1 bi aij /bs and then adding an additional column of s zeros.
```

<details><summary>Proof</summary>

```
Proof. The case p = 1 follows from (323g), so we consider instead the case
p ≥ 2. Also, without loss of generality we
                                         "assume    that 1 ≤ q ≤ p − 1, because
                                           s
internal order 1 is equivalent to ci =     j=1 a ij and because q ≥ p implies
internal order p − 1. We first prove that

                           
                           s
                                             1
                                 bi ck−1
                                     i   =     ,        k = 1, 2, . . . , p.
                           i=1
                                             k

For k = 1 the result is equivalent to (323g). If the result has been proved for
k − 1 < p, we verify it for k, thus completing an induction argument. We have

        
        s                  
                           s                 
                                             s
                                                                  1      1      1
               bi ck−1 =         bi ck−2 −         bi ck−2 =        −         = .
         i=1
                   i
                           i=1
                                     i
                                             i=1
                                                        i
                                                                k − 1 k(k − 1)  k

The next step is to extend the internal order property to stage s. Write the
                     "s
value of Φi (t) as      j=1 aij χj . We then have


                 1         
                           s
                         =    bj χj
           γ(t)(r(t) + 1) j=1
                                       
                                       s
                                 =           bi aij χj
                                     i,j=1
                                                         
                                        s
                                                      1       s
                                                                    c
                                                                      r(t)
                                 = bs      asj χj −      +      bi i
                                        j=1
                                                     γ(t)     i=1
                                                                    γ(t)
                                                         
                                        s
                                                      1             1
                                 = bs      asj χj −        +                ,
                                        j=1
                                                     γ(t)     γ(t)(r(t) + 1)

implying that
                                         
                                         s
                                                                1
                                               asj χj =             .
                                         j=1
                                                               γ(t)

                                                                k−1
Next we prove the order condition"s for a tree of the form [τ       t1 ] where
k + r(t1 ) ≤ p. We write Φ(t1 ) = i=1 bi χi . For k = 1 we have

                      
                      s                      
                                             s
                                                                        1             1
          Φ(t) =             bi aij χj =           bj χj =                        =      .
                     i,j=1                   j=1
                                                                γ(t1 )(r(t1 ) + 1)   γ(t)

Now assume that k > 1 and that the result has been proved"when k is replaced
by k − 1. For the rest of this proof, we write Φ([t1 ]) = si=1 bi χi . We have
bi ck−1
    i   = bi ck−2
              i   − bi ck−2
                         i   and hence

                     Φ(t) = Φ([τ k−1 t1 ])
                            s
                          =    bi ck−1
                                   i    χi
                                 i=1
                                 
                                 s                       
                                                         s
                             =         bi ck−2
                                           i   χi −            bi ck−2
                                                                    i   χi
                                 i=1                     i=1
                                       1                  1
                             =                 −
                               γ(t1 )(r(t) − 1) γ(t1 )r(t)(r(t) − 1)
                                   1
                             =
                               γ(t1 )r(t)
                                1
                             =      .
                               γ(t)

Finally, we consider a tree of the form t = [t1 t2 · · · tm ], where r(t1 ) ≥ r(t2 ) ≥
· · · ≥ r(tm ). Because 2q + 2 ≥ p, r(tk ) ≤ q for k = 2, 3, . . . , m. We now have

                     Φ(t) = Φ([t1 t2 · · · tm ])
                               
                               s
                                             m  r(t )
                                               c k  i
                           =         bi χi
                               i=1
                                                   γ(tk )
                                             k=2
                               
                               s
                                             r(t)−r(t1 )−1      1
                           =         bi χi ci                %m
                               i=1                            k=2 γ(tk )
                                    1
                           = %m           Φ([τ r(t)−r(t1 )−1 t1 ])
                               k=2 γ(tk )
                                       1
                           =           %
                             r(t)γ(t1 ) m k=2 γ(tk )
                              1
                           =      .                                                 
                             γ(t)

  Before we consider how to extend the benefits of Theorem 323B beyond the
gain of a single order, we look again at the generalized order conditions

                                                   1
                               Φ(t) =                       .                 (323h)
                                             (r(t) + 1)γ(t)

Because the series
                                      ξ r(t) hr(t)
                        y(x0 ) +                        F (t)(y(x0 ))
                                             γ(t)σ(t)
                                     t∈T

represents the solution of
                                     y  (x) = f (y(x))
at x = x0 + ξh, we find by integrating term by term, from ξ = 0 to ξ = 1,
         x +h
that h−1 x00 y(x)dx has Taylor expansion

                                          hr(t)
                   y(x0 ) +                            F (t)(y(x0 )).          (323i)
                                    (r(t) + 1)γ(t)σ(t)
                              t∈T

Hence a method satisfying (323h) for r(t) ≤ p agrees with (323i) to within
O(hp+1 ).
   We can generalize the meaning of order further by replacing the single
integral by the double integral
                                1 ξ
                                           y(x0 + ξh)dξdξ,
                                0     0

and we now find
    x0 +h x                        
 −2                                                                  hr(t)
h             y(x)dxdx = 12 y(x0 ) +                                                  F (t)(y(x0 )).
      x0   x0                                            (r(t) + 1)(r(t) + 2)γ(t)σ(t)
                                               t∈T

  For a method with generalized order conditions, it might seem possible
to carry out the process of reducing to one less stage and the second
generalization of the order conditions, but this is of little value. When we
have recovered the method with the first generalization, the last abscissa will
have value 1, and it will not be possible to go further to recover a method
satisfying the standard order conditions.
  However, this difficulty can be overcome, to some extent, by setting the last
component of the abscissa vector of the first generalized method to 0 rather
than to 1, with appropriate modifications made to the method of recovery. To
see how this works, consider the method with first level of generalized order
equal to 3 whose tableau is

                                  0
                                  1        1
                                  4        4
                                  1        1
                                  2        2         0
                                  3                  1        1
                                           0
                                  4                  2        4          .
                                           0         1
                                                     2     − 16    1
                                                                   6

Note that this method was constructed to satisfy not only the four generalized
order conditions
                       1                   1                       1                  1
                b 1=     ,       b c=        ,           b c2 =      ,       b Ac =      ,
                       2                   6                      12                  24
but also the condition
                                       
                                       4
                                             bi
                                                   = 1,
                                       i=1
                                           1 −  ci
which is imposed in anticipation of our intention to construct a fourth order
method by adding an additional stage. The new method is

                             0
                             1        1
                             4        4
                             1        1
                             2        2          0
                             3                  1            1
                             4         0        2            4
                             0        0         1
                                               6β         − 3β
                                                             1      1
                                                                   6β
                                  −β            2
                                                3         − 13      2
                                                                    3        β

and it is an easy matter to check that all the fourth order conditions are
satisfied for any choice of the non-zero parameter β.
```
</details>

**References:**
- uses_equation: `eq:323g`
- uses_equation: `eq:323h`
- uses_equation: `eq:323i`

---

### Theorem 324A (p.208)
*Section 32, Subsection 324*

```
Theorem 324A If an explicit s-stage Runge–Kutta method has order p, then
s ≥ p.
```

<details><summary>Proof</summary>

```
Proof. Let t = [[· · · [t] · · · ]] such that r(t) = p > s. The order condition
associated with this tree is Φ(t) = 1/γ(t), where γ(t) = p! and Φ(t) = b Ap−1 1.
Because A is strictly lower triangular, Ap = 0. Hence, the order condition
becomes 0 = 1/p!, which has no solution.                                      
```
</details>

---

### Theorem 324B (p.208)
*Section 32, Subsection 324*

```
Theorem 324B If an explicit s-stage Runge–Kutta method has order p ≥ 5,
then s > p.
```

<details><summary>Proof</summary>

```
Proof. Assume s = p. Evaluate the values of the following four expressions:
                                     6    2(c2 + c4 )     c2 c 4
       b Ap−4 (C − c4 I)(C − c2 I)c =   −             +          ,       (324a)
                                     p!    (p − 1)!     (p − 2)!
                                     3       c4
               b Ap−4 (C − c4 I)Ac =    −         ,                      (324b)
                                     p! (p − 1)!
                                     2       c2
               b Ap−4 A(C − c2 I)c =    −         ,                      (324c)
                                     p! (p − 1)!
                                     1
                        b Ap−4 A2 c = .                                  (324d)
                                     p!
  From the left-hand sides of these expressions we observe that (324a)×(324d)
= (324b)×(324c). Evaluate the right-hand sides, and we find that
                                                                  
    6   2(c2 + c4 )     c 2 c4     1        3       c4       2       c2
      −             +                  =      −                 −          ,
   p!    (p − 1)!     (p − 2)!     p!       p! (p − 1)!      p! (p − 1)!
which simplifies to c2 (c4 − 1) = 0.
  Now consider the four expressions
                                       8    3c2 + 2c5     c2 c5
      b Ap−5 (C − c5 I)A(C − c2 I)c =     −           +          ,       (324e)
                                       p!    (p − 1)!   (p − 2)!
                                       4       c5
               b Ap−5 (C − c5 I)A2 c =    −         ,                    (324f)
                                       p! (p − 1)!
                                       2       c2
               b Ap−5 A2 (C − c2 I)c =    −         ,                    (324g)
                                       p! (p − 1)!
                                       1
                         b Ap−5 A3 c = .                                 (324h)
                                       p!

Again we see that (324e)×(324h) = (324f)×(324g), so that evaluating the
right-hand sides, we find
                                                            
     8    3c2 + 2c5     c2 c5    1    4      c5       2       c2
        −           +               =   −               −            ,
     p!    (p − 1)!   (p − 2)!   p!   p! (p − 1)!     p! (p − 1)!

leading to c2 (c5 − 1) = 0. Since we cannot have c2 = 0, it follows that c4 =
c5 = 1. Now evaluate b Ap−5 (C − e)A2 c. This equals (4 − p)/p! by the order
conditions but, in contradiction to this, it equals zero because component
number i of b Ap−5 vanishes unless i ≤ 5. However, these components of
(C − e)A2 c vanish.                                                         

   The bound s − p ≥ 1, which applies for p ≥ 5, is superseded for p ≥ 7
by s − p ≥ 2. This is proved in Butcher (1965a). For p ≥ 8 we have the
stronger bound s − p ≥ 3 (Butcher, 1985). It seems likely that the minimum
value of s − p rises steadily as p increases further, but there are no published
results dealing with higher orders. On the other hand, it is known, because of
the construction of a specific method (Hairer, 1978), that p = 10, s = 17 is
possible.
   That a sufficiently high s can be found to achieve order p follows
immediately from Theorem 317A. We now derive an upper bound on the
minimum value of such an s. This is done by constructing methods with odd
orders, or methods satisfying the generalization of odd orders introduced in
Subsection 323. In the latter case, we then use the results of that subsection
to extend the result to the next even order higher.
```
</details>

**References:**
- uses_theorem: `thm:317A`
- uses_equation: `eq:324a`
- uses_equation: `eq:324b`
- uses_equation: `eq:324c`
- uses_equation: `eq:324d`
- uses_equation: `eq:324e`
- uses_equation: `eq:324f`
- uses_equation: `eq:324g`
- uses_equation: `eq:324h`
- uses_section: `sec:323`

---

### Theorem 324C (p.209)
*Section 32, Subsection 324*

```
Theorem 324C For any positive integer p, an explicit Runge–Kutta method
exists with order p and s stages, where
                           2
                              3p −10p+24
                                    8     , p even,
                      s=      3p2 −4p+9
                                   8    ,   p odd.
```

<details><summary>Proof</summary>

```
Proof. We consider the case of p odd, but allow for generalized order
conditions. If p = 1 + 2m, we construct first an implicit Runge–Kutta method
with 1 + m stages, using (case I) standard order conditions and (case II)
generalized order conditions. For case I, the order condition associated with
the tree t is, as usual,
                                          1
                                 Φ(t) =       .
                                         γ(t)
In case II, this condition is replaced by

                                            1
                            Φ(t) =                  .
                                     (r(t) + 1)γ(t)

  For the implicit method, the abscissae are at the zeros of the polynomial
                              dm m+1
                                 x   (x − 1)m , in case I,
                             dxm
                          dm m+1
                             x   (x − 1)m+1 , in case II,
                         dxm


with the zero x = 1 omitted in case II. It is clear that x = 0 is a zero in both
cases and that the remaining zeros are distinct and lie in the interval [0, 1).
Denote the positive zeros by ξi , i = 1, 2, . . . , m. We now construct methods
with abscissae chosen from the successive rows of the following table:

                      row 0                 0
                      row 1                 ξ1
                      row 2                 ξ1     ξ2
                      row 3                 ξ1     ξ2     ξ3
                                             ..     ..     ..        ..
                                              .      .      .             .
                      row m                 ξ1     ξ2     ξ3         ···      ξm
                      row m + 1             ξ1     ξ2     ξ3         ···      ξm
                                              ..     ..     ..                 ..
                                               .      .      .                  .
                      row 2m                ξ1     ξ2     ξ3         ···      ξm

where there are exactly m + 1 repetitions of the rows with m members. The
total number of stages will then be
                                                1
      s = 1 + 1 + 2 + · · · + (m − 1) + (m + 1)m = (3m2 + m + 2).
                                                  2
                                              
Having chosen c = 0 ξ1 ξ1 ξ2 · · · ξm , we construct b with all
components zero except the first component and the final m components.
The non-zero components are chosen so that
                       
          m
                            1,         case I
     b1 +     bs−m+i =      1
          i=1               2,         case II
                                                          /
      
                                 k,            case I
            bs−m+i ξik−1 =          1                            ,    k = 1, 2, . . . , 2m + 1.
      i=1                        k(k+1) ,      case II

   The possibility that the non-zero b components can be found to satisfy these
conditions follows from the theory of Gaussian quadrature. The final step in
the construction of the method is choosing the elements of the matrix A. For
i corresponding to a member of row k for k = 1, 2, . . . , m, the only non-zero

aij are for j = 1 and for j corresponding to a member of row k − 1. Thus, the
quadrature formula associated with this row has the form
                      ci                        
                                                 k−1
                            φ(x)dx ≈ w0 φ(0) +         wj φ(ξj )
                      0                          j=1

and the coefficients are chosen to make this exact for φ a polynomial of degree
k − 1. For i a member of row k = m + 1, m + 2, . . . , 2m, the non-zero aij are
found in a similar way based on the quadrature formula
                     ci                    m
                         φ(x)dx ≈ w0 φ(0) +     wj φ(ξj ).
                      0                          j=1

The method constructed in this way has order, or generalized order,
respectively, equal to p = 2m + 1. To see this, let Yi denote the approximation
to y(xn−1 + hξi ) in stage 1 + i of the order 2m + 1 Radau I method (in case
I) or the order 2m + 2 Lobatto method (in case II). It is easy to see that
the stages corresponding to row k approximate the Y quantities to within
O(hk+1 ). Thus the full method has order 2m + 1 in case I and generalized
order 2m + 1 in case II. Add one more stage to the case II methods, as in
```
</details>

---

### Theorem 333A (p.224)
*Section 32, Subsection 333*

```
Theorem 333A If (333b) has order p and (333a) has order p + 1 and
B = bs+1 , then
                       1 − Br(t)
                Φ(t) =           ,  r(t) ≤ p + 1.          (333d)
                          γ(t)
Conversely, if (333d) holds with cs = 1 and B = 0 and, in addition,

      bs+1 = B,                                                                                          (333e)
                 −1
    as+1,s = B        bs (1 − cs ),                                                                      (333f)
                                                               !
                                              
                                              s
    as+1,j = B −1           bj (1 − cj ) −          bi aij         ,          j = 1, 2, . . . , s − 1,   (333g)
                                              i=1

then (333b) has order p and (333a) has order p + 1.
```

<details><summary>Proof</summary>

```
Proof. For a given tree t, let Φ(t) denote the elementary weight for (333a) and
Φ(t) the elementary weight for (333b). Because the latter method has order
p, it follows that for a tree t = [t1 t2 · · · tm ], with order not exceeding p + 1, we
have Φ(ti ) = 1/γ(ti ), for i = 1, 2, . . . , m. Hence, for a method identical with
(333a) except for b replaced by the basis vector es+1 , the elementary weight
corresponding to t will be

                                             m
                                                   1      r(t)
                                                        =      .
                                             i=1
                                                 γ(ti )   γ(t)

Adding B multiplied by this quantity to Φ(t) gives the result
                                                 r(t)          1
                                  Φ(t) + B            =
                                                       Φ(t) =      ,
                                                 γ(t)         γ(t)
which is equivalent to (333d).
   To prove the converse, we first note that, because B = 0, the previous
argument can be reversed. That is, if (333b) has order p then (333d) implies
that (333a) has order p + 1. Hence, it is only necessary to prove that (333b)
has order p. We calculate Φ(t), for r(t) ≤ p as follows, where we have written
χi (t) for the coefficient of bi in Φ(t)
                        
                        s                                      s−1
                                                              s 
       Φ(t) = B −1            bj (1 − cj )χj (t) − B −1                 bi aij χj (t)
                        j=1                                   i=1 j=1

             = B −1 (Φ(t) − Φ(tτ ) − Φ(τ t))
                                                                      
                 −1   1 − Br(t) r(t)(1 − B(1 + r(t))) 1 − B(1 + r(t))
             =B                  −                    −
                         γ(t)          (1 + r(t))γ(t)   (1 + r(t))γ(t)
                1
             =      .                                                                                     
               γ(t)
  Although the derivation is carried out from a modified version of the order
conditions, it is convenient to display a particular method in the format

                                0
                                c2     a21
                                c3     a31     a32
                                 ..     ..      ..   ..
                                  .      .       .        .
                                cs     as1     as2   ···      as,s−1            ,
                                       b1      b2    ···       bs−1      bs
                                       d1      d2    ···       ds−1      ds
where
      [ d1   d2   ···     ds−1        ds ] = [ b1 −as1        b2 −as2     ···       bs−1 −as,s−1   bs ]

is "the vector of coefficients in the proposed error estimator. That is,
h si=1 di f (Yi ) is used "
                          to evaluate the difference between the order p
approximation yn−1 + h si=1 as+1,i f (Yi ) and the
                                               " supposedly more accurate
approximation of order p + 1 given by yn−1 + h si=1 bi f (Yi ). The dashed line
above row number s of the tableau is intended to indicate that the row below
it is the approximation to be propagated and, of course, the dashed line below
the b vector separates the order p+1 approximation from the error estimator.
   Now let us look at some example of these embedded methods. Methods of
orders 1 and 2 are easy to derive and examples of each of these are as follows:

                                   0
                                   1       1
                                          1           1
                                          2           2
                                       − 12           1
                                                      2

and
                             0
                             1   1
                             2   2
                             1         1
                             2   0     2
                             1   0     0         1
                                                              .
                                 1     1         1        1
                                 6     3          3       6
                                 1
                                 6
                                       1
                                       3       − 23       1
                                                          6

Observe that for the second order method, the third order method in which
it is embedded is actually the classical fourth order method.
   Order 3 embedded in order 4 requires s = 4 stages. From the modified order
conditions we find that
                                                                 
  b3 (c3 − c4 )c3 (c3 − c2 ) = 41 − B −(c2 + c4 ) 13 − B +c2 c4 12 − B , (333h)
                               1     B              
         b4 a43 c3 (c3 − c2 ) = 12 −     − c2 16 − B2 ,                   (333i)
                                      3
                               1                  
         b3 (c3 − c4 )a32 c2 = 8 − B          1   B
                                     2 − c4 6 − 2 ,                       (333j)
                               1     B
                b4 a43 a32 c2 = 24 − 6 ,                                 (333k)

so that, equating the products (333h)×(333k) and (333i)×(333j) and
simplifying, we find the consistency condition

                                     1 − 7B + 12B 2
                            c4 =                    .
                                     1 − 6B + 12B 2
                            1
For example, choosing B = 12  to give c4 = 67 , together with c2 = 27 and
     4
c3 = 7 , yields the tableau


                        0
                        2         2
                        7         7
                        4
                        7      − 35
                                  8         4
                                             5
                        6
                        7
                                 29
                                 42       − 23         5
                                                       6
                                  1         1          5             1
                        1         6          6        12             4            .
                                 11         7         35             7        1
                                 96        24         96            48       12
                               − 96
                                  5         1
                                             8      − 96
                                                       5
                                                                  − 48
                                                                     5        1
                                                                             12

  Order 4 embedded in order 5 requires s = 6. That is, there are seven stages
overall, but the last stage derivative is identical to the first stage derivative
for the following step. To derive a method of this type, make the simplifying
assumption
                          6
                                      1
                              aij cj = c2i ,    i = 2,
                          j=1
                                      2

together with the subsidiary conditions

                         
                         6                
                                          6                   
                                                              6 
                                                                i−1
                 b2 =          bi ai2 =         bi ci ai2 =              bi aij aj2 = 0.
                         i=3              i=3                 i=4 j=3


Also, impose order conditions for the trees                                           but instead of
the corresponding conditions for the trees                                                 , use linear
combinations as follows:
                                        1                     
                   bi aij cj (cj − c3 ) = 12 − 13 B − c3 16 − 12 B ,                            (333l)
               6≥i>j≥4
                                                   1                              
        bi ci (ci − c6 )(ci − c4 )(ci − c3 ) =       5 −B    − (c6 + c4 + c3 ) 14 − B
                                                                             1     
 5≥i≥5                                              +(c6 c4 + c6 c3 + c4 c3 ) 3 − B     (333m)
                                                             1      
                                                    −c6 c4 c3 2 − B ,
                                             1            1         
              bi (ci − c6 )aij cj (cj − c3 ) = 15 − 13 B − c6 12 − 13 B
                                                  1 1            1 1  (333n)
      5≥i>j≥4                                 −c3 8 − 2 B + c6 c3 6 − 2 B ,
                                             1                    1         
              bi aij cj (ci − c4 )(cj − c3 ) = 20 − 14 B − (c4 + c3 ) 12 − 13 B
                                                    1 1                         (333o)
      6≥i>j≥5                                 +c4 c3 6 − 2 B ,
                                             1            1        
                    bi aij ajk ck (ck − c3 ) = 60 − 12
                                                     1
                                                       B − c3 24 − 16 B .                       (333p)
        6≥i>j>k≥4

The left-hand sides of (333m)–(333p) consist of only a single term and we
see that the product of (333m) and (333p) is equal to the product of (333n)
and (333o). Thus we obtain consistency conditions for the values of a65 and
a54 by comparing the products of the corresponding right-hand sides. After
considerable manipulation and simplification, we find that this consistency
condition reduces to
                                        q0 B
                         c6 = 1 −                    ,               (333q)
                                  q0 − q1 B + q2 B 2
with

                     q0 = 10c23 c4 + 2c4 − 8c3 c4 − c3 ,
                     q1 = 60c23 c4 − 56c3 c4 + 16c4 − 8c3 ,
                     q2 = 120c23 c4 − 120c3 c4 + 40c4 − 20c3 .

Construction of the method consists of selecting c2 , c3 , c4 , c5 and B; choosing
c6 in accordance with (333q); evaluating a65 and a54 from the consistent
equations (333n), (333o) and (333p); and then evaluating a64 from (333l).
The remaining coefficients are then evaluated using the remaining conditions
that have been stated.
  An example of a method in this family is

        0
        1      1
        4      4
        1      1          1
        4      8          8
        1
        2      0       − 12        1
       13
       20
               13
              200     − 1000
                         299        78
                                   125
                                            13
                                            50
        4
        5
              548
             7475
                         688
                        2875
                                   572
                                  2875   − 575
                                            88       132
                                                     299
        1      37
```
</details>

**References:**
- uses_equation: `eq:333b`
- uses_equation: `eq:333a`
- uses_equation: `eq:333d`
- uses_equation: `eq:333e`
- uses_equation: `eq:333f`
- uses_equation: `eq:333g`
- uses_equation: `eq:333h`
- uses_equation: `eq:333i`
- uses_equation: `eq:333j`
- uses_equation: `eq:333k`
- uses_equation: `eq:333l`
- uses_equation: `eq:333m`
- uses_equation: `eq:333n`
- uses_equation: `eq:333o`
- uses_equation: `eq:333p`
- uses_equation: `eq:333q`

---

### Theorem 342C (p.238)
*Section 33, Subsection 342*

```
Theorem 342C

                                      G(2s) ⇒ B(2s),                          (342j)
                                      G(2s) ⇒ E(s, s),                       (342k)
                        B(2s) ∧ C(s) ∧ D(s) ⇒ G(2s),                          (342l)
                               B(2s) ∧ C(s) ⇒ E(s, s),                      (342m)
                                B(2s) ∧ E(s, s) ⇒ C(s),                     (342n)
                                 B(2s) ∧ D(s) ⇒ E(s, s),                    (342o)
                                B(2s) ∧ E(s, s) ⇒ D(s).                     (342p)
```

<details><summary>Proof</summary>

```
Proof. The first two results (342j), (342k) are consequences of the order
conditions. Given that C(s) is true, all order conditions based on trees
containing the structure · · · [τ k−1 ] · · · , with k ≤ s, can be removed, as we




                                    C(s)

                                                                     G(2s)
                           ∧           ∧

                                              E(s, s)
                  B(2s)                                         ∧

                                                 ∧
                           ∧

                                    D(s)


              Figure 342(i)     Schema representing Theorem 342C



saw in Subsection 321. Similarly, the condition D(s) enables us to remove
from consideration all trees of the form [τ k−1 [· · · ]]. Hence, if both C(s) and
D(s) are true, the only trees remaining are those associated with the trees
covered by B(2s). Hence, (342l) follows. Multiply the matrix of quantities
that must be zero according to the C(s) condition
          "               "                             "                     
              j a1j − c1       a1j cj − 12 c21    ···                 − 1s cs1
                                                                  s−1
                                                          j a1j cj
          "               "j                            "                     
            j a2j − c2       j a2j cj − 2 c2      ···                 − 1s cs2 
                                         1 2                      s−1
                                                         j a2j cj
                                                                              
                ..                ..                              ..          
                 .                 .                               .          
           "               "                             "
             j asj − cs      j asj cj − 2 cs      ···                 − s cs
                                        1 2                       s−1   1 s
                                                           j asj cj

by the non-singular matrix
                                                                
                            b1         b2        ···       bs
                                                                
                        b1 c1       b2 c2       ···     bs cs 
                                                                
                            ..         ..                  ..   
                             .          .                   .   
                         b1 cs−1
                              1     b2 cs−1
                                         2       ···    bs css−1


and the result is the matrix of E(s, s) conditions. Hence, (342m) follows and,
because the matrix multiplier is non-singular, (342n) also follows. The final
results (342o) and (342p) are proved in similar way.                        

  A schema summarizing Theorem 342C is shown in Figure 342(i). To turn
this result into a recipe for constructing methods of order 2s we have:
```
</details>

**References:**
- uses_equation: `eq:342j`
- uses_equation: `eq:342k`
- uses_equation: `eq:342l`
- uses_equation: `eq:342m`
- uses_equation: `eq:342n`
- uses_equation: `eq:342o`
- uses_equation: `eq:342p`
- uses_section: `sec:321`

---

### Theorem 343A (p.242)
*Section 33, Subsection 343*

```
Theorem 343A The reflection of the reflection of a Runge–Kutta method is
the original method.
  If a method satisfies some of the simplifying assumptions introduced in
Subsection 321, then we consider the possibility that the reflection of the
method satisfies corresponding conditions. To enable us to express these
                                   
connections conveniently, we write B(η),  
                                         C(η),  
                                                D(η)        ζ) to represent
                                                      and E(η,
B(η), C(η), D(η) and E(η, ζ), respectively, but with reference to the reflected
method. We then have:
```

**References:**
- uses_section: `sec:321`

---

### Theorem 343B (p.242)
*Section 33, Subsection 343*

```
Theorem 343B If η and ζ are positive integers, then
                                                    
                                             B(η) ⇒ B(η),                                  (343d)
                                                    
                                      B(η) ∧ C(η) ⇒ C(η),                                  (343e)
                                   B(η) ∧ D(η) ⇒  D(η),                                   (343f)
                                                    ζ).
                              B(η + ζ) ∧ E(η, ζ) ⇒ E(η,                                    (343g)
```

<details><summary>Proof</summary>

```
Proof. Let P and Q be arbitrary polynomials of degrees less than η and
less than ζ, respectively. By using the standard polynomial basis, we see that
B(η), C(η), D(η) and E(η, ζ) are equivalent respectively to the statements
                    
                    s                    1
                         bj P (cj ) =         P (x)dx,                                     (343h)
                   j=1                   0

                   
                   s                     ci
                        aij P (cj ) =          P (x)dx,         i = 1, 2, . . . , s,       (343i)
                 j=1                     0

                 
                 s                            1
                       bi P (ci )aij = bj          P (x)dx,         j = 1, 2, . . . , s,   (343j)
                 i=1                          cj

        
        s                                1            x          
               bi P (ci )aij Q(cj ) =         P (x)           Q(x)dx dx.                   (343k)
       i,j=1                             0               0


     " part of the result B(η) holds with η ≥ 1, and hence we can assume
In each
that si=1 bi = 1. Hence the reflected tableau can be assumed to be

                    1 − c1     b1 − a11        b2 − a12       ···    bs − a1s
                    1 − c2     b1 − a21        b2 − a22       ···    bs − a2s
                       ..          ..              ..                    ..
                        .           .               .                     .
                    1 − cs     b1 − as1        b2 − as2       ···    bs − ass      .
                                  b1              b2          ···       bs

To prove (343d) we have, using (343h),

                  
                  s                         1                             1
                        bj P (1 − cj ) =         P (1 − x)dx =                  P (x)dx.
                  j=1                       0                              0


To prove (343e) we use (343i) to obtain

           
           s                                      1                   ci
                  (bj − aij )P (1 − cj ) =                P (x)dx −             P (1 − x)dx
           j=1                                    0                       0
                                                  1                   1
                                            =             P (x)dx −                 P (x)dx
                                                  0                       1−ci
                                                  1−ci
                                            =                  P (x)dx.
                                                  0

Similarly, we prove (343f) using (343j):

        
        s                                          1                           1
               bi P (1 − ci )(bj − aij ) = bj              P (x)dx − bj               P (1 − x)dx
        i=1                                           0                          cj
                                                   1                          1−cj             
                                           = bj                P (x)dx −                P (x)dx
                                                          0                     0
                                                   1
                                           = bj                P (x)dx.
                                                      1−cj

Finally, use (343k) to prove (343g):

        
        s
               bi P (1 − ci )(bj − aij )Q(1 − cj )
       i,j=1
                1              1                 1                     x
          =          P (x)dx         Q(x)dx −                 P (1 − x)
                                                        Q(1 − x)dx dx
             0           0            0              0
             1          1           1            1         
          =     P (x)dx     Q(x)dx −     P (1 − x)       Q(x)dx dx
             0           0            0              1−x
             1          1           1        1        
          =     P (x)dx     Q(x)dx −     P (x)      Q(x)dx dx
             0           0            0          x
             1        x       
          =     P (x)      Q(x)dx dx.                                                                 
                 0             0
```
</details>

**References:**
- uses_equation: `eq:343d`
- uses_equation: `eq:343e`
- uses_equation: `eq:343f`
- uses_equation: `eq:343g`
- uses_equation: `eq:343h`
- uses_equation: `eq:343i`
- uses_equation: `eq:343j`
- uses_equation: `eq:343k`

---

### Theorem 344A (p.244)
*Section 33, Subsection 344*

```
Theorem 344A Let c1 < c2 < · · · < cs be chosen as abscissae of the Radau
I, the Radau II or the Lobatto quadrature formula, respectively. Then:
  I For the Radau I formula, c1 = 0. This formula is exact for polynomials
     of degree up to 2s − 2.
 II For the Radau II formula, cs = 1. This formula is exact for polynomials
     of degree up to 2s − 2.
III For the Lobatto formula, c1 = 0, cs = 1. This formula is exact for
     polynomials of degree up to 2s − 3.
Furthermore, for each of the three quadrature formulae, ci ∈ [0, 1], for
i = 1, 2, . . . , s, and bi > 0, for i = 1, 2, . . . , s.
```

<details><summary>Proof</summary>

```
Proof. The fact that x = 1 is a zero of Ps∗ (x)−Ps−1
                                                 ∗
                                                     (x) and of Ps∗ (x)−Ps−2
                                                                         ∗
                                                                             (x)
                                                          ∗        ∗
follows from (342b). The fact that x = 0 is a zero of Ps (x) + Ps−1 (x) and of
Ps∗ (x) − Ps−2
           ∗
               (x) follows from (342b) and (342c), with x = 1. Let φ denote
an arbitrary polynomial of degree not exceeding 2s − 2 in the Radau cases
or 2s − 3 in the Lobatto case. Divide this by the polynomial satisfied by the
abscissae and write Q for the quotient and R for the remainder. We have in
the three cases,
          φ(x) = Q(x)(Ps∗ (x) + Ps−1
                                 ∗
                                     (x)) + R(x),        Radau I case,
          φ(x) = Q(x)(Ps∗ (x) − Ps−1
                                 ∗
                                     (x)) + R(x),        Radau II case,
                        ∗        ∗
          φ(x) = Q(x)(Ps (x) − Ps−2  (x)) + R(x),        Lobatto case.

          Table 344(I)    Methods in the Radau and Lobatto families

 Name            Choice of b and c        Choice of A
 Radau I         Radau I quadrature       C(s)
 Radau IA        Radau I quadrature       The reflections of Radau II
 Radau II        Radau II quadrature      D(s)
 Radau IIA       Radau II quadrature      The reflections of Radau I
 Lobatto III     Lobatto quadrature       C(s − 1), a1s = a2s = · · · = ass = 0
 Lobatto IIIA    Lobatto quadrature       C(s)
 Lobatto IIIB    Lobatto quadrature       D(s)
 Lobatto IIIC    Lobatto quadrature       The reflections of Lobatto III


Evaluate the approximate integral of φ written in this form, and the terms
involving Q are zero because of orthogonality, and the terms involving R are
exact because of the interpolational nature of the quadrature.
   In the Radau cases, to prove that the abscissae are always in [0, 1] and that
the weights are positive, use a homotopy t → Ps∗ ± tPs−1   ∗
                                                              , where the upper
sign is used for Radau I and the lower sign for Radau II. If any of the weights
becomes zero, then for this value of t, the quadrature formula has a greater
order than is possible. Furthermore, no abscissae can move outside [0, 1], until
t reaches a value t = 1. The proof is slightly more complicated in the Lobatto
case, where we use the homotopy t → Ps∗ − tPs−2 ∗
                                                    . Because of the symmetry of
the quadrature formula for all t, c1 = 0 and cs = 1 both occur at the same time
and this is when t = 1. If a weight passes through zero, then we again obtain
a contradiction to the optimality of Gaussian quadrature because two weights
vanish simultaneously. The one case not covered by this argument is when s
is odd and the weight corresponding to c(s+1)/2 = 12 vanishes. However, it is
impossible that as t moves from 0 to 1, it passes through a point for which
this happens because in this case the remaining abscissae would have to be
               ∗
the zeros of Ps−1 . By (342f), this occurs only for t = −(n − 1)/n, and this has
the wrong sign.                                                               

   Given the choice of c and b in accordance with the requirements of Radau
I, Radau II or Lobatto quadrature, the choice of A to yield a Runge–Kutta
of the same order as for the underlying quadrature formula remains. The
most obvious choice, of making the methods as close to explicit as possible, is
inappropriate for stiff problems, but makes the method more efficient for non-
stiff problems. Other choices can be made in terms of the C and D conditions,
and in terms of specific choices of specific elements of A. To distinguish these
from the simple (closest to explicit) choices, a letter A, B or C is added to
the designation for the method. A summary of many of the methods in the
Radau and Lobatto families is given in Table 344(I).

  Selected examples of these methods are as follows, where we note that
Lobatto IIIB with s = 2 does not exist:

  Radau I        (s = 2, p = 3),
                                                      0        0       0
                                                      2        1       1
                                                      3        3       3
                                                               1       3
                                                               4       4



  Radau IA       (s = 2, p = 3),
                                                  0        1
                                                           4       − 14
                                                  2        1            5
                                                  3        4           12
                                                           1            3
                                                           4            4



  Radau II       (s = 2, p = 3),
                                                      1        1
                                                      3        3       0
                                                      1        1       0
                                                               3       1
                                                               4       4



  Radau IIA      (s = 2, p = 3),
                                               1
                                               3
                                                           5
                                                          12       − 12
                                                                      1

                                                           3           1
                                               1           4           4
                                                           3           1
                                                           4           4



  Radau I        (s = 3, p = 5),

                                    0√
                                              0 √                 √
                                                                   0             0   √
                                   6− 6      9+ 6            24+ 6            168−73 6
                                     √
                                    10         √
                                              75               120 √               √
                                                                                 600
                                   6+ 6      9− 6          168+73 6             24− 6
                                    10        75               600√              120
                                                                                   √
                                               1             16+ 6              16− 6
                                               9                36                36



  Radau IA       (s = 3, p = 5),
                                                                 √                √
                                               1           −1− 6             −1+ 6
                                        0√     9               18√              18 √
                                     6− 6      1           88+7 6           88−43 6
                                       √
                                      10       9              360√             360√
                                     6+ 6      1          88+43 6            88−7 6
                                      10       9              360√             360
                                                                                 √
                                               1            16+ 6             16− 6
                                               9               36               36

  Radau II       (s = 3, p = 5),
                                         √           √                     √
                                       4− 6     24− 6               24−11 6
                                         √
                                        10        120√                 120√
                                                                               0
                                       4+ 6    24+11 6               24+ 6
                                        10          √
                                                  120                    √
                                                                       120     0
                                                 6− 6                 6+ 6
                                         1         12√                  12√    0
                                                16− 6                16+ 6     1
```
</details>

**References:**
- uses_equation: `eq:342b`
- uses_equation: `eq:342c`
- uses_equation: `eq:342f`

---

### Theorem 351B (p.252)
*Section 36, Subsection 351*

```
Theorem 351B A Runge–Kutta method with stability function R(z) =
N (z)/D(z) is A-stable if and only if (a) all poles of R (that is, all zeros
of D) are in the right half-plane and (b) E(y) ≥ 0, for all real y.
```

<details><summary>Proof</summary>

```
Proof. The necessity of (a) follows from the fact that if z ∗ is a pole then
limz→z∗ |R(z)| = ∞, and hence |R(z)| > 1, for z close enough to z ∗ . The
necessity of (b) follows from the fact that E(y) < 0 implies that |R(iy)| > 1,
so that |R(z)| > 1 for some z = − + iy in the left half-plane. Sufficiency of
these conditions follows from the fact that (a) implies that R is analytic in
the left half-plane so that, by the maximum modulus principle, |R(z)| > 1 in
this region implies |R(z)| > 1 on the imaginary axis, which contradicts (b). 
```
</details>

---

### Theorem 352A (p.254)
*Section 36, Subsection 352*

```
Theorem 352A Let l, m ≥ 0 be integers and define polynomials Nlm and
Dlm by

                                  l!    (l + m − i)!
                                        l
                  Nlm (z) =                           zi ,             (352b)
                              (l + m)! i=0 i!(l − i)!
                                 m!  (l + m − i)!
                                       m
                  Dlm (z) =                           (−z)i .          (352c)
                              (l + m)! i=0 i!(m − i)!

Also define
                                            l!m!
                     Clm = (−1)m                         .
                                    (l + m)!(l + m + 1)!
Then
                                     m+1
 Nlm (z)−exp(z)Dlm (z)+Clm z l+m+1+ l+m+2 Clm z l+m+2 = O(z l+m+3 ). (352d)
```

<details><summary>Proof</summary>

```
Proof. In the case m = 0, the result is equivalent to the Taylor series for
exp(z); by multiplying both sides of (352d) by exp(−z) we find that the result
is also equivalent to the Taylor series for exp(−z) in the case l = 0. We now
suppose that l ≥ 1 and m ≥ 1, and that (352d) has been proved if l is replaced
by l − 1 or m replaced is by m − 1. We deduce the result for the given values
of l and m so that the theorem follows by induction.
   Because the result holds with l replaced by l − 1 or with m replaced by
m − 1, we have
                                                
   Nl−1,m (z) − exp(z)Dl−1,m (z) + 1 + l+m+1
                                           m+1
                                                z Cl−1,m z l+m = O(z l+m+2 ),
                                                                    (352e)
                                            
  Nl,m−1 (z) − exp(z)Dl,m−1 (z) + 1 + l+m+1 z Cl,m−1 z
                                        m              l+m
                                                           = O(z l+m+2
                                                                       ).
                                                                        (352f)

Multiply (352e) by l/(l + m) and (352f) by m/(l + m), and we find that the
coefficient of z l+m has the value
                        l           m
                          Cl−1,m +     Cl,m−1 = 0.
                      l+m          l+m

The coefficient of z l+m+1 is found to be equal to Clm . Next we verify that

                l               m
                  Nl−1,m (z) +     Nl,m−1 (z) − Nlm (z) = 0            (352g)
              l+m              l+m
and that
                l               m
                  Dl−1,m (z) +     Dl,m−1 (z) − Dlm (z) = 0.           (352h)
              l+m              l+m

          Table 352(I)           Padé approximations Nlm /Dlm for l, m = 0, 1, 2, 3
      
      l
      
      m            0                       1                        2                        3
      0            1                     1+z                   1+z+ 12 z 2          1+z+ 12 z 2 + 16 z 3

                  1                     1+ 12 z               1+ 23 z+ 16 z 2      1+ 34 z+ 14 z 2 + 24
                                                                                                     1 3
                                                                                                        z
      1          1−z                    1− 12 z                 1− 13 z                   1− 14 z
                1                      1+ 13 z               1+ 12 z+ 12
                                                                       1 2
                                                                         z        1+ 35 z+ 20
                                                                                            3 2
                                                                                              z + 601 3
                                                                                                     z
      2      1−z+ 12 z 2             1− 23 z+ 16 z 2         1− 12 z+ 12
                                                                      1 2
                                                                         z            1− 25 z+ 20
                                                                                               1 2
                                                                                                  z
                 1                      1+ 14 z               1+ 25 z+ 20
                                                                       1 2
                                                                          z       1+ 12 z+ 10
                                                                                           1 2     1
                                                                                              z + 120 z3
      3   1−z+ 12 z 2 − 16 z 3   1− 34 z+ 14 z 2 − 24
                                                   1 3
                                                      z   1− 35 z+ 20
                                                                    3 2
                                                                      z − 601 3
                                                                             z    1− 12 z+ 10
                                                                                           1 2     1
                                                                                              z − 120 z3




The coefficient of z i in (352g) is
             (l − 1)!(l + m − i − 1)!                              
                                        l(l − i) + ml − l(l + m − i) = 0,
                 (l + m)!i!(l − i)!
so that (352g) follows. The verification of (352h) is similar and will be omitted.
It now follows that
                                      m+1 
 Nlm (z)−exp(z)Dlm (z)+Clm z l+m+1 + l+m+2 Clm z l+m+2 = O(z l+m+3 ), (352i)

and we finally need to prove that C lm = Clm . Operate on both sides of (352i)
                         l+1
with the operator (d/dz)     and multiply the result by exp(−z). This gives
                                                
              m+1 (l+m+2)!         (l+m+1)!
    P (z) + l+m+2   (m+1)!   C lm −    m!    C lm z
                                                    m+1
                                                        = O(z m+2 ),    (352j)

where P is the polynomial of degree m given by
                                                 l+1
                    (l + m + 1)!                d
            P (z) =              Clm z m − 1 +         Dlm (z).
                         m!                    dz
                            lm = Clm .
It follows from (352j) that C                                                                               

  The formula we have found for a possible (l, m) Padé approximation to
exp(z) is unique. This is not the case for an arbitrary function f , as the
example of the function given by (352a) shows; the (2, 1) approximation is
not unique. The case of the exponential function is covered by the following
result:
```
</details>

**References:**
- uses_equation: `eq:352b`
- uses_equation: `eq:352c`
- uses_equation: `eq:352d`
- uses_equation: `eq:352e`
- uses_equation: `eq:352f`
- uses_equation: `eq:352g`
- uses_equation: `eq:352h`
- uses_equation: `eq:352i`
- uses_equation: `eq:352j`
- uses_equation: `eq:352a`

**Referenced by:**
- `thm:352B` (uses_theorem)

---

### Theorem 352B (p.255)
*Section 36, Subsection 352*

```
Theorem 352B The function Nlm /Dlm , where the numerator and denomi-
nator are given by (352b) and (352c), is the unique (l, m) Padé approximation
to the exponential function.
```

<details><summary>Proof</summary>

```
Proof. If N lm /D
                  lm is a second such approximation then, because these
functions differ by O(z l+m+1 ),
                                                lm Dlm = 0,
                                          lm − N
                                     Nlm D

      Table 352(II)      Diagonal members of the Padé table Nmm /Dmm for
                                 m = 0, 1, 2, . . . , 7
                                             Nmm
    m
                                             Dmm

     0                                          1
                                              1 + 12 z
     1
                                              1 − 12 z
                                          1 + 12 z + 12
                                                      1 2
                                                         z
     2
                                          1 − 2 z + 12 z
                                               1      1 2

                                   1 + 12 z + 10  1 2
                                                    z + 1201 3
                                                              z
     3
                                   1 − 2 z + 10 z − 120 z
                                          1       1 2      1 3

                              1 + 12 z + 28 3 2
                                             z + 84  1 3
                                                       z + 1680  1
                                                                   z4
     4
                              1 − 12 z + 28  z − 84
                                            3 2      1 3
                                                       z + 1680  1
                                                                   z4
                              1      1 2      1 3        1    4      1
                         1 + 2 z + 9 z + 72 z + 1008 z + 30240          z5
     5
                         1 − 12 z + 19 z 2 − 72
                                              1 3
                                                 z + 10081
                                                            z 4 − 30240
                                                                     1
                                                                        z5
                       1      5 2        1 3       1 4         1           1
                  1 + 2 z + 44 z + 66 z + 792 z + 15840 z 5 + 665280          z6
     6
                  1 − 2 z + 44 z − 66 z + 792 z − 15840 z + 665280 z 6
                       1      5 2        1 3       1 4         1   5       1

         1 + 12 z + 26
                     3 2
                       z + 312 5 3
                                  z + 3432 5           1
                                             z 4 + 11440            1
                                                           z 5 + 308880           1
                                                                        z 6 + 17297280 z7
     7
         1 − 2 z + 26 z − 312 z + 3432 z 4 − 11440 z 5 + 308880 z 6 − 17297280 z 7
              1      3 2       5 3         5           1            1             1




because the expression on the left-hand side is O(z l+m+1 ), and is at the same
time a polynomial of degree not exceeding l +m. Hence, the only way that two
distinct approximations can exist is when they can be cancelled to a rational
function of lower degrees. This means that for some (l, m) pair, there exists
a Padé approximation for which the error coefficient is zero. However, since
exp(z) is not equal to a rational function, there is some higher exponent k and
a non-zero constant C such that
                   Nlm (z) − exp(z)Dlm (z) = Cz k + O(z k+1 ),                      (352k)
with k ≥ l + m + 2. Differentiate (352k) k − m − 1 times, multiply the result
by exp(−z) and then differentiate a further m + 1 times. This leads to the
contradictory conclusion that C = 0.                                      

   Expressions for the (l, m) Padé approximations are given in Table 352(I) for
l, m = 0, 1, 2, 3. To extend the information further, Table 352(II) is presented
to give the values for l = m = 0, 1, 2, . . . , 7. Similar tables are also given for
the first and second sub-diagonals in Tables 352(III) and 352(IV), respectively,
and error constants corresponding to entries in each of these three tables are
presented in Table 352(V).


Table 352(III)        First sub-diagonal members of the Padé table Nm−1,m /Dm−1,m
                                    for m = 1, 2, . . . , 7
                                              Nm−1,m
      m
                                              Dm−1,m
                                                  1
      1
                                               1−z
                                              1 + 13 z
      2
                                          1 − 23 z + 16 z 2
                                         1 + 25 z + 201 2
                                                        z
      3
                                    1 − 5 z + 20 z − 60
                                          3       3 2       1 3
                                                              z
                                         3       1 2        1 3
                                    1 + 7 z + 14 z + 210       z
      4
                                1 − 7 z + 7 z − 105 z + 840
                                    4       1 2      2 3         1 4
                                                                    z
                                   4       1 2       1 3          1
                               1 + 9 z + 12 z + 126 z + 3024 z 4
      5
                         1 − 9 z + 36
                             5      5 2
                                       z − 2525 3
                                                  z + 30245
                                                              z 4 − 15120
                                                                        1
                                                                          z5
                              5       1 2      1 3        1             1
                         1 + 11 z + 11  z + 99    z + 1584    z 4 + 55440 z5
      6
                    1 − 11 z + 22 z − 99 z + 528 z − 9240 z 5 + 332640
                         6      3 2      2 3        1 4         1          1
                                                                                z6
                       6      5 2       5 3        1             1           1
                  1 + 13 z + 52 z + 429 z + 1144 z + 25740 z + 1235520 z 6
                                                       4              5
      7
           1 − 13 z + 52
                7
                         z − 1716
                       7 2      35 3
                                   z + 3432 7
                                               z 4 − 51480
                                                        7               7
                                                             z 5 + 1235520 z 6 − 8648640
                                                                                    1
                                                                                         z7


   For convenience, we write Vmn (z) for the two-dimensional vector whose
first component is Nlm (z) and whose second component is Dlm (z). From the
proof of Theorem 352A, it can be seen that the three such vectors Vl−1,m (z),
Vl,m−1 (z) and Vl,m (z) are related by


                      lVl−1,m (z) + mVl,m−1 (z) = (l + m)Vl,m (z).


Many similar relations between neighbouring members of a Padé table exist,
and we present three of them. In each case the relation is between three Padé
vectors of successive denominator degrees.
```
</details>

**References:**
- uses_theorem: `thm:352A`
- uses_equation: `eq:352b`
- uses_equation: `eq:352c`
- uses_equation: `eq:352k`

---

### Theorem 352C (p.257)
*Section 36, Subsection 352*

```
Theorem 352C If l, m ≥ 2 then

                           m−l           
  Vlm (z) = 1 +                          z Vl−1,m−1 (z)
                      (l + m)(l + m − 2)
                                       (l − 1)(m − 1)
                           +                                     z 2 Vl−2,m−2 (z).
                             (l + m − 1)(l + m − 2)2 (l + m − 3)


         Table 352(IV) Second sub-diagonal members of the Padé table
                     Nm−2,m /Dm−2,m for m = 2, 3, . . . , 7

                                             Nm−2,m
    m
                                             Dm−2,m
                                                  1
     2
                                           1 − z + 12 z 2
                                               1 + 14 z
     3
                                      1 − 34 z + 14 z 2 − 241 3
                                                              z
                                               1        1 2
                                         1 + 3 z + 30 z
     4
                                1 − 23 z + 15 z 2 − 301 3
                                                         z + 360 1 4
                                                                    z
                                         3        3 2       1 3
                                     1 + 8 z + 56 z + 336 z
     5
                        1 − 58 z + 28   z − 168
                                      5 2        5 3
                                                   z + 336    z − 6720
                                                            1 4         1
                                                                           z5
                                    2      1 2        1 3         1    4
                             1 + 5 z + 15 z + 180 z + 5040 z
     6
                   1 − 35 z + 16 z 2 − 36
                                        1 3
                                          z + 336  1 4
                                                      z − 5040 1            1
                                                                   z 5 + 151200 z6
                            5         5 2       1 3         1    4       1    5
                      1 + 12 z + 66 z + 132 z + 2376 z + 95040 z
     7
          1 − 12 z + 44 z − 264
               7      7 2        7 3
                                    z + 2376 7
                                                z 4 − 31680
                                                          7             1
                                                              z 5 + 95040  z 6 − 3991680
                                                                                    1
                                                                                         z7
```

<details><summary>Proof</summary>

```
Proof. Let
                                 m−l            
  V (z) = Vlm (z) − 1 +                         z Vl−1,m−1 (z)
                            (l + m)(l + m − 2)
                                       (l − 1)(m − 1)
                          −                                     z 2 Vl−2,m−2 (z).
                            (l + m − 1)(l + m − 2)2 (l + m − 3)

It is easy to verify that the coefficients of z 0 , z 1 and z 2 vanish in both
components of V (z). We also find that

                         [1     − exp(z) ]V (z) = O(z l+m−1 ).

If V (z) is not the zero vector, we find that
                           '             (
                       z −2 1    − exp(z) V (z) = O(z l+m−3 ),

contradicting the uniqueness of Padé approximations of degrees (l − 2, m − 2).
                                                                             

  Theorems 352D and 352E which follow are proved in the same way as
```
</details>

---

### Theorem 352D (p.259)
*Section 36, Subsection 352*

```
Theorem 352D If l ≥ 1 and m ≥ 2 then
                                  
                        l
 Vlm (z) = 1 −                    z Vl,m−1 (z)
               (l + m)(l + m − 1)
                                     l(m − 1)
                        +                                 z 2 Vl−1,m−2 (z).
                          (l + m)(l + m − 1)2 (l + m − 2)
```

---

### Theorem 352E (p.259)
*Section 36, Subsection 352*

```
Theorem 352E If l ≥ 0 and m ≥ 2 then
                1                        m−1
  Vlm (z) = 1 −     z Vl+1,m−1 (z) +                      z 2 Vl,m−2 (z).
                l+m                  (l + m)2 (l + m − 1)
```

---

### Theorem 353A (p.259)
*Section 36, Subsection 353*

```
Theorem 353A Let s be a positive integer and let
                                           N (z)
                                  R(z) =
                                           D(z)
denote the (s − d, s) member of the Padé table for the exponential function,
where d = 0, 1 or 2. Then
                                |R(z)| ≤ 1,
for all complex z satisfying Rez ≤ 0.
```

<details><summary>Proof</summary>

```
Proof. We use the E-polynomial. Because N (z) = exp(z)D(z) + O(z 2s−d+1 ),
we have

      E(y) = D(iy)D(−iy) − N (iy)N (−iy)
           = D(iy)D(−iy) − exp(iy)D(iy) exp(−iy)D(−iy) + O(y 2s−d+1 )
           = O(y 2s−d+1 ).

Because E(y) has degree not exceeding 2s and is an even function, either
E(y) = 0, in the case d = 0, or E(y) = Cy 2s with C > 0, in the cases d = 1
and d = 2. In all cases, E(y) ≥ 0 for all real y.
  To complete the proof, we must show that the denominator of R has no
zeros in the left half-plane. Without loss of generality, we assume that Re z < 0
and we prove that D(z) = 0. Write D0 , D1 , . . . , Ds for the denominators of
the sequence of Padé approximations given by

                             V00 , V11 , . . . , Vs−1,s−1 , Vs−d,s ,

so that D(z) = Ds (z). From Theorems 352C, 352D and 352E, we have

                                1
 Dk (z) = Dk−1 (z) +                      z 2 Dk−2 ,               k = 2, 3, . . . , s − 1, (353a)
                        4(2k − 1)(2k − 3)

and
                       Ds (z) = (1 − αz)Ds−1 + βz 2 Ds−2 ,                                     (353b)
where the constants α and β will depend on the value of d and s. However,
α = 0 if d = 0 and α > 0 for d = 1 and d = 2. In all cases, β > 0.
  Consider the sequence of complex numbers, ζk , for k = 1, 2, . . . , s, defined
by
                  1
          ζ1 = 1 − z,
                  2
                             1              −1
          ζk = 1 +                     z 2 ζk−1 ,                k = 2, 3, . . . , s − 1,
                     4(2k − 1)(2k − 3)
                                −1
          ζs = (1 − αz) + βz 2 ζs−1 .

This means that ζ1 /z = −1/2 + 1/z has negative real part. We prove by
induction that ζk /z also has negative real part for k = 2, 3, . . . , s. We see this
by noting that
                                                      −1
        ζk  1          1                        ζk−1
           = +                                               ,      k = 2, 3, . . . , s − 1,
        z   z  4(2k − 1)(2k − 3)                  z
                          −1
        ζs  1         ζs−1
           = −α+β              .
         z  z           z

The fact that Ds (z) cannot vanish now follows by observing that

                             Ds (z) = ζ1 ζ2 ζ3 · · · ζs .

Hence, D = Ds does not have a zero in the left half-plane.                    

  Alternative proofs of this and related results have been given byAxelsson
(1969, 1972), Butcher (1977), Ehle (1973), Ehle and Picel (1975), Watts and
Shampine (1972) and Wright (1970).
```
</details>

**References:**
- uses_equation: `eq:353a`
- uses_equation: `eq:353b`

---

### Theorem 355B (p.264)
*Section 36, Subsection 355*

```
Theorem 355B Let R be a rational approximation to exp of exact order p,
so that
                R(z) = exp(z) − Cz p+1 + O(z p+2 ),
where the error constant C is non-zero. If C < 0 (C > 0) there are up
(down) arrows tangential at 0 to the rays with arguments k2πi/(p + 1),
k = 0, 1, . . . , p, and down (up) arrows tangential at 0 to the rays with
arguments (2k + 1)πi/(p + 1), k = 0, 1, . . . , p.
```

<details><summary>Proof</summary>

```
Proof. If, for example, C < 0, consider the set {r exp(iθ) : r > 0, θ ∈
[k2πi/(p + 1) − , k2πi/(p + 1) + }, where and r are both small and
k ∈ {0, 1, 2, . . . , p}. We have

           R(z) exp(−z) = 1 + (−C)r p+1 exp((p + 1)θ) + O(r p+2 ).

For r sufficiently small, the last term is negligible and, for sufficiently
small, the real part of (−C)r p+1 exp((p + 1)θ)) is positive. The imaginary
part changes sign so that an up arrow lies in this wedge. The cases of the
down arrows and for C > 0 are proved in a similar manner.                

  Where the arrows leaving the origin terminate is of crucial importance.
```
</details>

---

### Theorem 355C (p.264)
*Section 36, Subsection 355*

```
Theorem 355C The up arrows terminate either at poles of R or at −∞.
The down arrows terminate either at zeros of R or at +∞.
```

<details><summary>Proof</summary>

```
Proof. Consider a point on an up arrow for which |z| is sufficiently large
to ensure that it is not possible that z is a pole or that z is real with
(d/dz)(R(z) exp(−z)) = 0. In this case we can assume without loss of
generality that Im(z) ≥ 0. Write R(z) = Kz n + O(|z|n−1 ) and assume that
K > 0 (if K < 0, a slight change is required in the details which follow). If
z = x + iy = r exp(iθ), then

        w(z) = R(z) exp(−z)
                                                              
             = Kr n exp(−x) 1 + O(r −1 ) exp i(nθ − y + O(r −1 )) .

Because θ cannot leave the interval [0, π], then for w to remain real, y is
bounded as z → ∞. Furthermore, w → ∞ implies that x → −∞.
  The result for the down arrows is proved in a similar way.             

  We can obtain more details about the fate of the arrows from the following
result.
```
</details>

---

### Theorem 355D (p.265)
*Section 36, Subsection 355*

```
Theorem 355D Let R be a rational approximation to exp of order p with
numerator degree n and denominator degree d. Let   n denote the number of
down arrows terminating at zeros and d the number of up arrows terminating
at poles of R. Then
                                n + d ≥ p.
                                
```

<details><summary>Proof</summary>

```
Proof. There are p + 1 − n  down arrows and p + 1 − d up arrows terminating
at +∞ and −∞, respectively. Let θ and φ be the minimum angles with the
properties that all the down arrows which terminate at +∞ lie within θ on
either side of the positive real axis and all the up arrows which terminate at
−∞ lie within an angle φ on either side of the negative real axis. Hence

                            (p − 
                                 n)2π                 
                                                 (p − d)2π
                     2θ ≥             ,   2φ ≥             .
                              p+1                  p+1
Because up arrows and down arrows cannot cross and, because there is a
wedge with angle equal to at least π/(p + 1) between the last down arrow and
the first up arrow, it follows that 2θ + 2φ + 2π/(p + 1) ≤ 2π. Hence we obtain
the inequality
                            2p + 1 − n − d
                                            2π ≤ 2π,
                                 p+1
and the result follows.                                                     

                                                                 
                                                            and d.
  For Padé approximations we can obtain precise values of n
```
</details>

**Referenced by:**
- `thm:355E` (uses_theorem)

---

### Theorem 355E (p.265)
*Section 36, Subsection 355*

```
Theorem 355E Let R(z) denote a Padé approximation to exp(z), with
degrees n (numerator) and d (denominator). Then n of the down arrows
terminate at zeros and d of the up arrows terminate at poles.
```

<details><summary>Proof</summary>

```
Proof. Because p = n + d, n ≥           it follows from Theorem 355D
                              n and d ≥ d,
that
                         p=n+d≥    n + d ≥ p
                    ) + (d − 
and hence that (n − n         d) = 0. Since both terms are non-negative they
must be zero and the result follows.                                      

  Before proving the ‘Ehle barrier’, we establish a criterion for A-stability
based on the up arrows that terminate at poles.
```
</details>

**References:**
- uses_theorem: `thm:355D`

**Referenced by:**
- `thm:355G` (uses_theorem)

---

### Theorem 355F (p.266)
*Section 36, Subsection 355*

```
Theorem 355F A Runge–Kutta method is A-stable only if all poles of the
stability function R(z) lie in the right half-plane and no up arrow of the order
web intersects with or is tangential to the imaginary axis.
```

<details><summary>Proof</summary>

```
Proof. The requirement on the poles is obvious. If an up arrow intersects or
is tangential to the imaginary axis then there exists y such that

                              |R(iy) exp(−iy)| > 1.

Because | exp(−iy)| = 1, it follows that |R(iy)| > 1 and the method is not
A-stable.                                                               

  We are now in a position to prove the result formerly known as the Ehle
conjecture (Ehle, 1973),but which we will also refer to as the ‘Ehle barrier’.
```
</details>

**Referenced by:**
- `thm:355G` (uses_theorem)

---

### Theorem 355G (p.266)
*Section 36, Subsection 355*

```
Theorem 355G Let R(z) denote the stability function of a Runge–Kutta
method. If R(z) is an (n, d) Padé approximation to exp(z) then the Runge–
Kutta is not A-stable unless d ≤ n + 2.
```

<details><summary>Proof</summary>

```
Proof. If d ≥ n + 3 and p = n + d, it follows that d ≥ 12 (p + 3). By Theorem
355E, at least d up arrows terminate at poles. Suppose these leave zero in
directions between −θ and +θ from the positive real axis. Then

                                     2π(d − 1)
                              2θ ≥             ≥ π,
                                       p+1
and at least one up arrow, which terminates at a pole, is tangential to the
imaginary axis or passes into the left half-plane. If the pole is in the left half-
plane, then the stability function is unbounded in this half-plane. On the other
hand, if the pole is in the right half-plane, then the up arrow must cross the
imaginary axis. In either case, the method cannot be A-stable, by Theorem
355F.                                                                            
```
</details>

**References:**
- uses_theorem: `thm:355E`
- uses_theorem: `thm:355F`

---

### Theorem 356C (p.268)
*Section 36, Subsection 356*

```
Theorem 356C Let (A, b , c) be an implicit Runge–Kutta method. Then the
method is AN-stable only if

                            bj ≥ 0,     j = 1, 2, . . . , s,

and the matrix
                       M = diag(b)A + A diag(b) − bb
is positive semi-definite.
```

<details><summary>Proof</summary>

```
Proof. If bj < 0 then choose Z = −t diag(ej ), for t positive. The value of
R(Z) becomes
                        R(Z) = 1 − tbj + O(t2 ),

which is greater than 1 for t sufficiently small. Now consider Z chosen with
purely imaginary components

                                   Z = i diag(vt),

where v has real components and t is a small positive real. We have

          R(Z) = 1 + itb diag(v)1 − t2 b diag(v)A diag(v)1 + O(t3 )
                = 1 + itb v − t2 v diag(b)Av + O(t3 ),

so that
                       |R(Z)|2 = 1 − t2 v M v + O(t3 ).
Since this cannot exceed 1 for t small and any choice of v, M is positive
semi-definite.                                                          

  Since there is no practical interest in reducible methods, we might look
at the consequences of assuming a method is irreducible. This result was
published in Dahlquist and Jeltsch (1979):
```
</details>

**Referenced by:**
- `def:356A` (uses_theorem)
- `def:356B` (uses_theorem)
- `cor:356D` (uses_theorem)

---

### Theorem 357C (p.271)
*Section 36, Subsection 357*

```
Theorem 357C If a Runge–Kutta method is algebraically stable then it is
BN-stable.
```

<details><summary>Proof</summary>

```
Proof. Let Fi = f (xn−1 + hci , Yi ). We note that if M given by (357d) is
positive semi-definite, then there exist vectors vl ∈ Rs , l = 1, 2, . . . , s ≤ s,
such that
                                     s
                               M=        µl µl .
                                       l=1

This means that a quadratic form can be written as the sum of squares as
follows:
                                  s
                          ξ Mξ =      (µl ξ)2 .
                                              l=1
Furthermore, a quadratic form of inner products
                                    
                                    s
                                            mij Ui , Uj 
                                    i,j=1

is equal to
                                   s 
                                      s        2
                                               
                                        µli Ui  ,
                                    l=1     i=1
and cannot be negative. We show that
                                  
                                  s                           
                                                              s
         yn − yn−1 2 = 2h               bi Yi , Fi  − h2           mij Fi , Fj ,   (357e)
                                  i=1                        i,j=1

so that the result will follow. To prove (357e), we use the equations
                                                  
                                                  s
                             Yi = yn−1 + h              aij Fj ,                       (357f)
                                                  j=1
                                             
                                             s
                             Yi = yn + h           (aij − bj )Fj ,                     (357g)
                                             j=1

which hold for i = 1, 2, . . . , s. In each case, form the quasi-inner product with
Fi , and we find
                                                     
                                                     s
                  Yi , Fi  = yn−1 , Fi  + h            aij Fi , Fj ,
                                                     j=1
                                                  
                                                  s
                  Yi , Fi  = yn , Fi  + h       (aij − bj )Fi , Fj .
                                                  j=1

Hence,
                    
                    s                    2              
               2h         bi Yi , Fi  = yn + yn−1 , h   bi Fi
                    i=1                                       i=1
                                             
                                             s
                                    = h2            (2bi aij − bi bj )Fi , Fj .
                                            i,j=1

Substitute yn and yn−1 from (357f) and (357g) and rearrange to deduce (357e).
                                                                           

  Our final aim in this discussion of non-autonomous and non-linear
stability is to show that BN-stability implies AN-stability. This will give the
satisfactory conclusion that algebraic stability is equivalent to each of these
concepts.
  Because we have formulated BN-stability in terms of a quasi-inner product
over the real numbers, we first need to see how (356a) can be expressed in a
suitable form. Write the real and imaginary parts of q(x) as α(x) and β(x),
respectively. Also write y(x) = ξ(x) + iη(x) and write ζ(x) for the function
with values in R2 whose components are ξ(x) and η(x), respectively.
  Thus, because

          y  (x) = (α(x) + iβ(x))(ξ(x) + iη(x))
                = (α(x)ξ(x) − β(x)η(x)) + i(β(x)ξ(x) + α(x)η(x)),

we can write
                                          ζ  (x) = Qζ,
where
                                           α(x) −β(x)
                             Q=                                .
                                           β(x) α(x)
Using the usual inner product we now have the dissipativity property

                               Qv, v = α v 2 ≤ 0,

if α ≤ 0.
   What we have found is that the test problem for AN-stability is an instance
of the test problem for BN-stability. This means that we can complete the
chain of equivalences interconnecting AN-stability, BN-stability and algebraic
stability. The formal statement of the final step is as follows:
```
</details>

**References:**
- uses_equation: `eq:357d`
- uses_equation: `eq:357e`
- uses_equation: `eq:357f`
- uses_equation: `eq:357g`
- uses_equation: `eq:356a`

---

### Theorem 357D (p.273)
*Section 36, Subsection 357*

```
Theorem 357D If an irreducible non-confluent Runge–Kutta method is BN-
stable, then it is AN-stable.
```

---

### Theorem 358A (p.275)
*Section 36, Subsection 358*

```
Theorem 358A A collocation Runge–Kutta method is algebraically stable if
and only if the abscissae are zeros of a polynomial of the form

                                     Ps∗ − θPs−1
                                             ∗
                                                 ,                             (358b)

where θ ≥ 0.
```

<details><summary>Proof</summary>

```
Proof. Because     i = 0 for i = 1, 2, . . . , 2s − 1, it follows that

                                1
                                     P (x)φ(x)dx = 0,                          (358c)
                                 0


where φ(x) is a polynomial of degree s, with positive leading coefficient
and zeros c1 , c2 , . . . , cs and P is any polynomial of degree not exceeding
s − 2. Furthermore, if P is a polynomial of degree s − 1 and positive leading
coefficient, the integral in (358c) has the same sign as − 2s . Because of the
orthogonality of φ and polynomials of degree less than s − 1, φ is a positive
constant multiple of (358b). Apart from a positive factor, we can now evaluate
                                         ∗
the integral in (358c), with P (x) = Ps−1   (x),

            1                                            1
                  ∗
                 Ps−1 (x)(Ps∗ (x) − θPs−1
                                      ∗
                                          (x))dx = −θ           ∗
                                                               Ps−1 (x)2 dx,
            0                                              0


which has the opposite sign to θ.                                                  

  A consequence of this result is that both Gauss and Radau IIA methods
are algebraically stable. Many other methods used for the solution of stiff
problems have stage order lower than s and are therefore not collocation
methods. A general characterization of algebraic stable methods is found by
using a transformation based not on the Vandermonde matrix V , but on a
generalized Vandermonde matrix based on the polynomials that are essentially
the same as Pi∗ , for i = 0, 1, 2, . . . , s − 1.
```
</details>

**References:**
- uses_equation: `eq:358b`
- uses_equation: `eq:358c`

**Referenced by:**
- `thm:359C` (uses_theorem)

---

### Theorem 359C (p.278)
*Section 36, Subsection 359*

```
Theorem 359C The Gauss, Radau IA, Radau IIA and Lobatto IIIC methods
are algebraically stable.
```

<details><summary>Proof</summary>

```
Proof. We have already settled the Gauss and Radau IIA cases, using the V
transformation, making use of the C(s) and B(p) conditions, as in Theorem
358A.
  To prove the result for Radau IA methods, use the D(s) and B(2s − 1)
conditions:
 
 s                            
                              s
         ck−1
          i   bi aij cl−1
                      j   +           ck−1
                                       i   bj aji cl−1
                                                   j
 i,j=1                        i,j=1

                                        1                     1
                                           s                      s
                                                                                         1
                                      =       bj (1 − cj )cj +
                                                       k l−1
                                                                     bi (1 − cli )ck−1
                                                                                   i   −
                                        k j=1                  l i=1                     kl

                                               k + l  k+l−1
                                                     s
                                          1
                                      =      −         bi c  .
                                          kl    kl i=1 i

The value of this expression is zero if k +l ≤ 2s−1. Although it can be verified
directly that the value is positive in the remaining case k = l = s, it is enough
to show that the (1, 1) element of M is positive, because this will have the
same sign as the only non-zero eigenvalue of the rank 1 matrix V M V . We
note that all values in the first column of A are equal to b1 because these give
the unique solution to the D(s) condition applied to the first column. Hence,
we calculate the (1, 1) element of M to be

                                      2b1 a11 − b21 = b21 > 0.

In the case of the Lobatto IIIC methods, we can use a combination of the
C(s − 1) and D(s − 1) conditions to evaluate the (k, l) and (l, k) elements of
M , where k ≤ s − 1 and l ≤ s. The value of these elements is

      
      s                            
                                   s
              ck−1
               i   bi aij cl−1
                           j   +           ck−1
                                            i   bj aji cl−1
                                                        j
      i,j=1                        i,j=1

                                               1                     1  k+l−1
                                                  s                      s
                                                                                    1
                                           =         (1 − ckj )cl−1
                                                                j   +       bi ci −
                                               k j=1                  k i=1         kl

                                               1  l−1
                                                  s
                                                           1
                                           =        bj c −
                                               k j=1 j     kl
                                           = 0.

The final step of the proof is the same as for the Radau IA case, because again
ai1 = b1 , for i = 1, 2, . . . , s.                                         

  The V transformation was used to simplify questions concerning algebraic
stability in Butcher (1975) and Burrage (1978). The W transformation
was introduced in Hairer and Wanner (1981, 1982). Recent results on the
W transformation, and especially application to symplectic methods, were
presented in Hairer and Leone (2000) .
```
</details>

**References:**
- uses_theorem: `thm:358A`

---

### Theorem 363A (p.289)
*Section 36, Subsection 363*

```
Theorem 363A The (i, j) element of T −1 is equal to

                                           ξj
                                                     Li−1 (ξj ).                        (363d)
                                      s2 Ls−1 (ξj )2

     denote T −1 AT ; then
Let A
                                                                        
                                 1 0 0                 ···     0      0
                                                                        
                               −1 1 0                 ···     0      0 
                                                                        
                               0 −1 1                 ···     0      0 
                          = λ
                         A     .  .. ..                       ..
                                                                         
                                                                      ..  .            (363e)
                               ..  . .                                . 
                                                               .        
                                                                        
                               0  0 0                 ···     1      0 
                                 0 0 0                 ···    −1      1
```

<details><summary>Proof</summary>

```
Proof. To prove (363d), use the Christoffel–Darboux formula for Laguerre
polynomials in the form

          
          s−1
                                  s                                 
                Lk (x)Lk (y) =        Ls (y)Ls−1 (x) − Ls (x)Ls−1 (y) .
                                 x−y
          k=0

For i = j, substitute x = ξi , y = ξj to find that rows i and j of T are
orthogonal. To evaluate the inner product of row i with itself, substitute y = ξi
and take the limit as x → ξi . It is found that

                
                s−1
                                                               s2 Ls−1 (ξi )2
                      Lk (ξk )2 = −sLs (ξi )Ls−1 (ξi ) =                     .   (363f)
                                                                    ξi
                k=0

The value of T T as a diagonal matrix with (i, i) element given by (363f) is
equivalent to (363d).
  The formula for A is verified by evaluating

                  
                  s                        
                                           s
                        aij Lk−1 (ξj ) =         aij Lk−1 (cj /λ)
                  j=1                      j=1
                                            λξi
                                      =             Lk−1 (cj /λ)dt
                                            0
                                             ξi
                                      =λ            Lk−1 (t)dt
                                                0
                                             ξi
                                      =λ            (Lk−1 (t) − Lk (t))dt
                                                0
                                      = λ(Lk−1 (ξi ) − Lk (ξi ))dt,

where we have used known properties of Laguerre polynomials. The value of
this sum is equivalent to (363e).                                      

  For convenience we sometimes write
                                                                 
                            0 0 0                   ···   0    0
                                                                 
                          1 0 0                    ···   0    0 
                                                                 
                          0 1 0                    ···   0    0 
                                                                 
                      J = . . .                          ..   ..  ,
                          .. .. ..                             . 
                                                          .      
                                                                 
                          0 0 0                    ···   0    0 
                            0 0 0                   ···   1    0

so that (363e) can be written
                                     = λ(I − J).
                                    A

 We now consider the possible A-stability or L-stability of singly implicit
methods. This hinges on the behaviour of the rational functions
                                           N (z)
                                R(z) =             ,
                                         (1 − λz)s
where the degree of the polynomial N (z) is no more than s, and where
                       N (z) = exp(z)(1 − λz)s + O(z s+1 ).
  We can obtain a formula for N (z) as follows:
                             s−i              
                                      i (s−i)   1
                     N (z) =      (−λ) Ls         zi,
                              i=0
                                                λ
        (m)
where Ln denotes the m-fold derivative of Ln , rather than a generalized
Laguerre polynomial. To verify the L-stability of particular choices of s and
λ, we note that all poles of N (z)/(1 − λz)s are in the right half-plane. Hence,
it is necessary only to test that |D(z)|2 − |(1 − λz)s |2 ≥ 0, whenever z is on
the imaginary axis. Write z = iy and we find the ‘E-polynomial’ defined in
this case as
                     E(y) = (1 + λ2 y 2 )s − N (iy)N (−iy),
with E(y) ≥ 0 for all real y as the condition for A-stability. Although A-
stability for s = p is confined to the cases indicated in Table 363(II), it will
be seen in the next subsection that higher values of s can lead to additional
possibilities.
  We conclude this subsection by constructing the two-stage L-stable singly
implicit method of order 2. From the formulae for the first few Laguerre
polynomials,
                                                               1
              L0 (x) = 1,   L1 (x) = 1 − x,   L2 (x) = 1 − 2x + x2 ,
                                                               2
we find the values of ξ1 and ξ2 , and evaluate the matrices T and T −1 . We
have                            √                √
                      ξ1 = 2 − 2,       ξ2 = 2 + 2
and
                                          √                    √       √
       L0 (ξ1 ) L1 (ξ1 )        1 −1 + 2            −1
                                                          1
                                                            +    2 1
                                                                     −   2
T =                        =              √    , T = 2 √2 4        2 √ 4    .
       L0 (ξ2 ) L1 (ξ2 )        1 −1 − 2                     4      − 42

                                         √
For L-stability, choose λ = ξ2−1 = 1− 12 2, and we evaluate A = λT (I −J)T −1
to give the tableau
                             √            √         √
                        3 − 2 2 54 − 34 2 74 − 54 2
                                          √         √
                                              4 − 4 √2 .
                                   1    1     3   1
                           1       4 + 4 √2
                                                                       (363g)
                                              4 − 4 2
                                   1    1     3   1
                                   4 + 4 2

  In the implementation of this, or any other, singly implicit method, the
actual entries in this tableau are not explicitly used. To emphasize this
point, we look in detail at a single Newton iteration for this method. Let
M = I − hλf  (yn−1 ). Here the Jacobian matrix f  is supposed to have been
evaluated at the start of the current step. In practice, a Jacobian evaluated
at an earlier time value might give satisfactory performance, but we do not
dwell on this point here. If the method were to be implemented with no special
use made of its singly implicit structure, then we would need, instead of the
N × N matrix M , a 2N × 2N matrix M     4 given by

               4=       I − ha11 f  (yn−1 )      −ha12 f  (yn−1 )
               M                                                        .
                         −ha21 f  (yn−1 )       I − ha22 f  (yn−1 )
In this ‘fully implicit’ situation, a single iteration would start with the input
approximation yn−1 and existing approximations to the stage values and stage
derivatives Y1 , Y2 , hF1 and hF2 . It will be assumed that these are consistent
with the requirements that
       Y1 = yn−1 + a11 hF1 + a12 hF2 ,         Y2 = yn−1 + a21 hF1 + a22 hF2 ,
and the iteration process will always leave these conditions intact.
```
</details>

**References:**
- uses_equation: `eq:363d`
- uses_equation: `eq:363e`
- uses_equation: `eq:363f`
- uses_equation: `eq:363g`

---

### Theorem 372A (p.299)
*Section 36, Subsection 372*

```
Theorem 372A Let (A, b , c) be a symplectic Runge–Kutta method. The
method has order p if and only if for each non-superfluous tree and any vertex
in this tree as root, Φ(t) = 1/γ(t), where t is the rooted tree with this vertex.
```

<details><summary>Proof</summary>

```
Proof. We need only to prove the sufficiency of this criterion. If two rooted
trees belong to the same tree but have vertices v0 , v say, then there is a
sequence of vertices v0 , v1 , . . . , vm = v, such that vi−1 and vi are adjacent
for i = 1, 2, . . . , m. This mean that rooted trees t, u exist such that tu is the
rooted tree with root vi−1 and ut is the rooted tree with root vi . We are
implicitly using induction on the order of trees and hence we can assume that
Φ(t) = 1/γ(t) and Φ(u) = 1/γ(u). Hence, if one of the order conditions for the
trees tu and ut is satisfied, then the other is. By working along the chain of
possible roots v0 , v1 , . . . , vm , we see that the order condition associated with
the root v0 is equivalent to the condition for v. In the case of superfluous
trees, one choice of adjacent vertices would imply that t = u. Hence, (372a) is
equivalent to 2Φ(tt) = 2/γ(tt) so that the order condition associated with tt
is satisfied and all rooted trees belonging to the same tree are also satisfied.

```
</details>

**References:**
- uses_equation: `eq:372a`

---

### Theorem 381G (p.303)
*Section 36, Subsection 380*

```
Theorem 381G Let (A, b , c) be an irreducible s-stage Runge–Kutta method.
Then, for any two stage indices i, j ∈ {1, 2, . . . , s}, there exists a Lipschitz-
continuous differential equation system such that Yi = Yj . Furthermore, there
exists t ∈ T , such that Φi (t) = Φj (t).
```

<details><summary>Proof</summary>

```
Proof. If i, j exist such that

                            Φi (t) = Φj (t) for all t ∈ T,                       (381a)

then define a partition P = {P1 , P2 , . . . , Ps } of {1, 2, . . . , s} such that i and
j are in the same component of the partition if and only if (381a) holds.
Let A denote the algebra of vectors in Rs such that, if i and j are in the
same component of P , then the i and j components of v ∈ A are identical.
The algebra is closed under vector space operations and under component-by-
component multiplication. Note that the vector with every component equal
to 1 is also in A. Let A denote the subalgebra generated by the vectors made
up from the values of the elementary weights for the stages for all trees. That
is, if t ∈ T , then v ∈ Rs defined by vi = Φi (t), i = 1, 2, . . . , s, is in A,     as
are the component-by-component products of the vectors corresponding to
any finite set of trees. In particular, by using the empty set, we can regard
the vector defined by vi = 1 as also being a member of A.               Because of the
                                                               
way in which elementary weights are constructed, v ∈ A implies Av ∈ A.             We
                   
now show that A = A. Let I and J be two distinct members of P . Then
because t ∈ T exists so that Φi (t) = Φj (t) for i ∈ I and j ∈ J, we can find
v ∈ A so that vi = vj . Hence, if w = (vi − vj )−1 (v − vj 1), where 1 in this

context represents the vector in Rs with every component equal to 1, then
wi = 1 and wj = 0. Form the product of all such members of the algebra
for J = I and we deduce that the characteristic function of I is a member
of A. Since the S such vectors constitute a basis for this algebra, it follows
that A = A. Multiply the characteristic function of J by A and note that, for
all i ∈ I ∈ P , the corresponding component in the product is the same. This
contradicts the assumption that the method is irreducible. Suppose it were
possible that two stages, Yi and Yj , say, give identical results for any Lipschitz
continuous differential equation, provided h > 0 is sufficiently small. We now
prove the contradictory result that Φi (t) = Φj (t) for all t ∈ T . If there were
a t ∈ T for which this does not hold, then write U for a finite subset of T
containing t as in Subsection 314. Construct the corresponding differential
equation as in that subsection and consider a numerical solution using the
Runge–Kutta method (A, b , c) and suppose that t corresponds to component
k of the differential equation. The value of component k of Yi is Φi (t) and the
value of component k of Yj is Φj (t).                                            

  Now the key result interrelating the three equivalence concepts.
```
</details>

**References:**
- uses_equation: `eq:381a`
- uses_section: `sec:314`

---

### Theorem 381H (p.304)
*Section 36, Subsection 380*

```
Theorem 381H Two Runge–Kutta methods are equivalent if and only if they
are P -equivalent and if and only if they are Φ-equivalent.
```

<details><summary>Proof</summary>

```
Proof.
P -equivalence ⇒ equivalence. It will enough to prove that if i, j ∈ PI , in
any P -reducible Runge–Kutta method, where we have used the notation of
```
</details>

---

### Theorem 382A (p.306)
*Section 36, Subsection 380*

```
Theorem 382A Let m1 , m2 , m1 , m2 denote Runge–Kutta methods, such
that
                  m1 ≡ m1 and m2 ≡ m2 .                      (382f)
Then
                              [m1 · m2 ] = [m1 · m2 ].
```

<details><summary>Proof</summary>

```
Proof. We note that an equivalent statement is

                               m1 · m2 ≡ m1 · m2 .                           (382g)

Let y1 and y2 denote the output values over the two steps for the sequence
of steps constituting m1 · m2 , and y 1 and y 2 denote the corresponding output
values for m1 · m2 . If f satisfies a Lipschitz condition and if h is sufficiently

small, then y1 = y 1 because m1 ≡ m1 , and y2 = y 2 because m2 ≡ m2 . Hence,
(382g) and therefore (382f) follows.                                      

   Having constructed a multiplicative operation, we now construct an identity
element and an inverse for equivalence classes of Runge–Kutta methods. For
the identity element we consider the class containing any method m0 that
maps an initial value to an equal value, for a problem defined by a Lipschitz
continuous function, provided that h is sufficiently small. It is clear that
[m0 ·m] = [m·m0 ] = [m] for any Runge–Kutta method m. It will be convenient
to denote the identity equivalence class by the symbol 1, where it will be clear
from the context that this meaning is intended.
   To define the inverse of an equivalence class, start with a particular
representative m = (A, b , c), with s stages, and consider the tableau
                  "
              c1 − sj=1 bj     a11 − b1   a12 − b2   ···    a1s − bs
                  "
              c2 − sj=1 bj     a21 − b1   a22 − b2   ···    a2s − bs
                   ..              ..         ..                ..
                    .               .          .                 .
                  "
              cs − sj=1 bj     as1 − b1   as2 − b2   ···    ass − bs   .
                                 −b1        −b2      ···      −bs

As we saw in Subsection 343, this method exactly undoes the work of m.
Denote this new method by m−1 , and we prove the following result:
```
</details>

**References:**
- uses_equation: `eq:382f`
- uses_equation: `eq:382g`
- uses_section: `sec:343`

---

### Theorem 382B (p.307)
*Section 36, Subsection 380*

```
Theorem 382B Let m denote a Runge–Kutta method. Then

                           [m · m−1 ] = [m−1 · m] = 1.
```

<details><summary>Proof</summary>

```
Proof. The tableaux for the two composite methods m · m−1 and m−1 · m
are, respectively,

       c1    a11   a12   ···   a1s        0          0        ···      0
       c2    a21   a22   ···   a2s        0          0        ···      0
        ..    ..    ..          ..        ..         ..                ..
         .     .     .           .         .          .                 .
       cs    as1   as2   ···   ass        0          0        ···      0

       c1    b1    b2    ···   bs     a11 − b1   a12 − b2     ···   a1s − bs
       c2    b1    b2    ···   bs     a21 − b1   a22 − b2     ···   a2s − bs
        ..    ..    ..          ..        ..         ..                 ..
         .     .     .           .         .          .                  .
       cs    b1    b2    ···   bs     as1 − b1   as2 − b2     ···   ass − bs
             b1    b2    ···   bs       −b1        −b2        ···     −bs

and
     "
 c1 − sj=1 bj     a11 − b1    a12 − b2    ···    a1s − bs       0     0    ···     0
     "
 c2 − sj=1 bj     a21 − b1    a22 − b2    ···    a2s − bs       0     0    ···     0
      ..              ..          ..                 ..         ..    ..           ..
       .               .           .                  .          .     .            .
     "s
 cs − j=1 bj      as1 − b1    as2 − b2    ···    ass − bs       0     0    ···     0
     "
 c1 − sj=1 bj        −b1         −b2      ···      −bs         a11   a12   ···   a1s
     "
 c2 − sj=1 bj        −b1         −b2      ···      −bs         a21   a22   ···   a2s
      ..              ..          ..                ..          ..    ..          ..
       .               .           .                 .           .     .           .
     "s
 cs − j=1 bj         −b1         −b2      ···      −bs         as1   as2   ···   ass      .
                     −b1         −b2      ···      −bs         b1    b2    ···   bs

Each of these methods is P -reducible to the methods m and m−1 , respectively,
but in each case with b replaced by the zero vector, so that each lies in the
equivalence class 1.                                                        
```
</details>

---

### Theorem 384A (p.311)
*Section 36, Subsection 384*

```
Theorem 384A Let Φ : T → R be the elementary weight function associated
with (A, b , c) and  Φ : T → R the elementary weight function associated with
               
(A, b , c). Let Φ : T → R denote the elementary weight function for the product
method as represented by (382a). Then

                                       = ΦΦ.
                                      Φ    

                                                                  A, b , c)
```

<details><summary>Proof</summary>

```
Proof. Denote the (s + s)-stage composite coefficient matrices by ( 
                          
with the elements of A and b given by

                         
                         
                           aij ,         i ≤ s,        j ≤ s,
                         
                          0,             i ≤ s,        j > s,
                  ij =
                  a
                         
                           bj ,          i > s,        j ≤ s,
                         
                         
                            i−s,j−s ,
                            a             i > s,        j > s.
                         
                            bi ,          i ≤ s,
                   bi =   bi−s ,        i > s.

For a tree t, such that r(t) = n, represented by the vertex–edge pair (V, E),
                                               
with root ρ ∈ V , write the elementary weight Φ(t)   in the form
                               
                         =
                       Φ(t)       bi(ρ)     ai(v),i(w) .            (384a)
                                  i∈I      (v,w)∈E


In this expression, I is the set of all mappings from V to the set {1, 2, . . . , s}
and, for i ∈ I and v ∈ V , i(v) denotes the value to which the vertex v maps.
   If v < w and i(v) ≤ s < i(w) then the corresponding term in (384a) is
zero. Hence, we sum only over I  defined as the subset of I from which such
i are omitted. For any i ∈ I  , define R  S = (V, E) such that all the vertices
associated with R map into {s + 1, s + 2, . . . , s + s}. Collect together all i ∈ I 
which share a common R so that (384a) can be written in the form
                              
                      
                     Φ(t) =            bi(ρ)        i(v),i(w) .
                                                     a
                               R S i∈IR      (v,w)∈E


For each R, the terms in the sum have total value Φ(S \ R) 
                                                          Φ(R), and the
result follows.                                                      
```
</details>

**References:**
- uses_equation: `eq:382a`
- uses_equation: `eq:384a`

---

### Theorem 386A (p.314)
*Section 36, Subsection 386*

```
Theorem 386A For α ∈ G1 and β ∈ G,

                       (αβ)(∅) = β(∅),
                        (αβ)(t) = λ(α, t)(β) + α(t)β(∅).
```

<details><summary>Proof</summary>

```
Proof. In this proof only, we introduce the notation R ˙S to denote R  S,
with R = ∅. If a tree t is represented by the set S of vertices, with an implied
set of edges, then the notation tR , where R  S, will denote the tree formed
from the elements of R, with the induced set of edges. With this terminology,
we can write (383a) in the form
                                
                    (αβ)(t) =       α(S \ R)β(R) + α(t)β(∅).
                               R˙S

Hence, we need to show that
                                        
                           λ(α, t) =          α(S \ R)
                                                      tR .
                                        R˙S

This is obvious in the case t = τ . We now consider a tree tu with t represented
by S and u represented by Q. This means that tu can be represented by the
graph (V, E), where V is the union of the vertex sets associated with S and

                Table 386(I)          The function λ for trees of orders 1 to 5

      t                  r(t) λ(α, t)
                 τ        1 τ
                ττ        2 ττ + α(τ )   τ
               τ τ ·τ     3 ττ· τ + 2α(τ )  τ τ + α(τ )2 τ
               τ ·τ τ     3 τ· τ τ + α(τ )τ τ + α(τ τ )  τ
             (τ τ ·τ )τ 4 (   τ τ·τ )
                                        τ + 3α(τ )  τ τ· τ + 3α(τ )2 ττ + α(τ )3 τ
              τ τ ·τ τ    4 ττ· τ τ + α(τ )τ τ·
                                                     τ + α(τ )  τ ·
                                                                    τ τ+
                                  (α(τ )2 + α(τ τ ))    τ τ + α(τ )α(τ τ )τ
             τ (τ τ ·τ ) 4 τ(  τ τ·τ ) + 2α(τ ) τ ·τ τ + α(τ ) ττ + α(τ τ ·τ )
                                                                     2
                                                                                        τ

             τ (τ ·τ τ )    4 τ(
                                 τ ·
                                    τ τ) + α(τ )
                                                 τ ·
                                                    τ τ + α(τ τ )
                                                                  τ τ + α(τ ·τ τ )
                                                                                   τ
            (τ τ ·τ )τ ·τ 5 ( τ τ·
                                    τ )τ ·
                                           τ + 4α(τ )(τ τ· τ )τ + 6α(τ )2 ττ·   τ+
                                  4α(τ ) ττ + α(τ ) τ
                                          3           4

            (τ τ ·τ )·τ τ 5 ( τ τ·
                                    τ )·τ τ + 2α(τ )
                                                      τ τ· τ τ + α(τ )(τ τ· τ )
                                                                                     τ+
                                  2α(τ )2 ττ·
                                               τ + (α(τ )2 + α(τ τ ))     τ τ· τ+
                                  (α(τ )3 + 2α(τ )α(τ τ ))      τ τ + α(τ )2 α(τ τ ) τ
            τ τ ·(τ τ ·τ ) 5 ττ·(τ τ·            τ τ·
                                          τ ) + 2α(τ )      τ τ + α(τ )τ (τ τ·τ )+
                                  α(τ )2 ττ·
                                              τ + 2α(τ )2 τ·   τ τ+
                                  (α(τ )3 + α(τ τ ·τ ))  τ τ + α(τ )α(τ τ ·τ )    τ
            τ τ ·(τ ·τ τ ) 5 ττ·(τ ·
                                       τ τ) + α(τ ) τ τ·τ τ + α(τ )    τ (τ ·
                                                                                    τ τ)+
                                 α(τ τ ) τ τ·
                                               τ + α(τ )2 τ·   τ τ+
                                 (α(τ )α(τ τ ) + α(τ ·τ τ ))       τ τ + α(τ )α(τ ·τ τ )   τ
            (τ ·τ τ )·τ τ 5 ( τ ·
                                  τ τ)·
                                        τ τ + 2α(τ )  τ τ·τ τ + α(τ ) ττ·
                                                                               2
                                                                                      τ+
                                 2α(τ τ )  τ ·
                                               τ τ + 2α(τ )α(τ τ )     τ τ + α(τ τ )2 τ
            τ ·(τ τ ·τ )τ 5 τ·( τ τ·
                                       τ )τ + 3α(τ )  τ (τ τ·τ ) + 3α(τ )2 τ·    τ τ+
                                 α(τ ) ττ + α((τ τ ·τ )τ )
                                       3
                                                                  τ
            τ (τ τ ·τ τ )   5 τ(
                                 τ τ·
                                      τ τ) + α(τ )  τ τ·
                                                   τ (     τ ) + α(τ )  τ ·
                                                                       τ (  τ τ)+
                                 (α(τ )2 + α(τ τ ))  τ ·
                                                         τ τ + α(τ )α(τ τ )τ τ + α(τ τ ·τ τ )
                                                                                                τ
            τ ·τ (τ τ ·τ ) 5 τ·  τ τ·
                                τ (    τ ) + 2α(τ )   τ ·
                                                     τ (   τ τ) + α(τ )2 τ·
                                                                              τ τ+
                                α(τ τ ·τ ) τ τ + α(τ (τ τ ·τ ))τ
            τ ·τ (τ ·τ τ ) 5 τ·  τ ·
                                τ (  τ τ) + α(τ )  τ ·
                                                   τ (  τ τ) + α(τ τ )
                                                                        τ ·
                                                                           τ τ+
                                    α(τ ·τ τ )
                                              τ τ + α(τ (τ ·τ τ ))
                                                                   τ


Q, and E is the union of the corresponding edge sets together with additional
edge connecting the two roots. Temporarily we write (V, E) = SQ. If R ˙S
       ˙ then the set of subgraphs related to SQ by the relation X SQ
and P Q                                                             ˙    are
of the form X = RP or of the form X = R. Hence,


            Table 386(II)    Formulae for (αβ)(ti ) up to trees of order 5

 i r(ti )     ti (αβ)(ti )
 0 0            ∅ β0
 1 1              β1 + α1 β0
 2 2              β2 + α1 β1 + α2 β0
 3 3              β3 + 2α1 β2 + α12 β1 + α3 β0
 4   3            β4 + α1 β2 + α2 β1 + α4 β0
 5   4            β5 + 3α1 β3 + 3α12 β2 + α13 β1 + α5 β0
 6   4            β6 + α1 β4 + α1 β3 + (α12 + α2 )β2 + α1 α2 β1 + α6 β0
 7   4            β7 + 2α1 β4 + α12 β2 + α3 β1 + α7 β0
 8   4            β8 + α1 β4 + α2 β2 + α4 β1 + α8 β0
 9   5            β9 + 4α1 β5 + 6α12 β3 + 4α13 β2 + α14 β1 + α9 β0
10   5            β10 + 2α1 β6 + α1 β5 + α12 β4 + (2α12 + α2 )β3 +
                      (2α1 α2 + α13 )β2 + α12 α2 β1 + α10 β0
11   5            β11 + α1 β7 + 2α1 β6 + 2α12 β4 + α12 β3 + (α13 + α3 )β2 +
                      α1 α3 β1 + α11 β0
12   5            β12 + α1 β8 + α1 β6 + α12 β4 + α2 β3 + (α1 α2 + α4 )β2 +
                      α1 α4 β1 + α12 β0
13   5            β13 + 2α1 β6 + 2α2 β4 + α12 β3 + 2α1 α2 β2 + α22 β1 + α13 β0
14   5            β14 + 3α1 β7 + 3α12 β4 + α13 β2 + α5 β1 + α14 β0

15   5            β15 + α1 β8 + α1 β7 + (α12 + α2 )β4 + α1 α2 β2 + α6 β1 + α15 β0

16   5            β16 + 2α1 β8 + α12 β4 + α3 β2 + α7 β1 + α16 β0

17   5            β17 + α1 β8 + α2 β4 + α4 β2 + α8 β1 + α17 β0



                                                          
          α(SQ \ X)
                   tX =                α(SQ \ P R)
                                                  tP R +           α(SQ \ R)
                                                                            tR
 X ˙ SQ                     P ˙Q R˙S                         R˙S
                                                                               
                       =           α(Q\P )tP         α(S \R)tR + α((S \R)Q)          tR
                            P ˙Q                R˙S                              R˙S

                       = λ(α, t)λ(α, u) + α(u)λ(α, t)
                       = λ(α, tu).                                                           


            Table 386(III)        Formulae for (α−1 )(ti ) up to trees of order 5

 i r(ti )      ti      (α−1 )(ti )
 1 1                   −α1
 2 2                   α12 − α2
 3 3                   2α1 α2 − α13 − α3
 4 3                   2α1 α2 − α13 − α4
 5 4                   3α1 α3 − 3α2 α12 + α14 − α5
 6 4                   α1 α3 + α1 α4 + α22 − 3α2 α12 + α14 − α6
 7    4                2α1 α4 + α1 α3 − 3α12 α2 + α14 − α7
 8    4                2α1 α4 + α22 − 3α12 α2 + α14 − α8
 9    5                4α1 α5 − 6α12 α3 + 4α13 α2 − α15 − α9
10    5                2α1 α6 + α1 α5 + α2 α3 − α12 α4 − 3α12 α3 + 4α1 α2 − α15 − α10
11    5                α1 α7 + 2α1 α6 + α2 α3 − 2α1 α22 − α12 α3 − 2α12 α4 +
                            4α13 α2 − α15 − α11
12    5                α1 α8 + α1 α6 + α2 α3 + α2 α4 − 3α1 α22 − α12 α3 − 2α12 α4 +
                            4α13 α2 − α15 − α12
13    5                2α1 α6 +2α2 α4 −α12 α3 −2α12 α4 −3α1 α22 +4α13 α2 −α15 −α13
14    5                3α1 α7 + α1 α5 − 3α12 α4 − 3α12 α3 + 4α13 α2 − α15 − α14
15    5                α1 α8 + α1 α7 + α1 α6 + α2 α4 − 2α1 α22 − α12 α3 − 3α12 α4 +
                            4α13 α2 − α15 − α15
16    5                2α1 α8 + α1 α7 + α2 α3 − 2α1 α22 − α12 α3 − 3α12 α4 +
                            4α13 α2 − α15 − α16
17    5                2α1 α8 + 2α2 α4 − 3α1 α22 + 4α13 α2 − α15 − α17



   As examples of the use of the algorithm for evaluating λ, and thence values
of the product on G1 × G, we find

                       λ(α, τ ) = τ,                                               (386a)
                      λ(α, τ τ ) = ττ + α(τ )τ,                                  (386b)
                    λ(α, τ τ ·τ ) = (
                                     τ τ + α(τ )
                                                 τ )·        τ τ + α(τ )
                                                     τ + α(t)(           τ)
                                  = ττ·
                                         τ + 2α(τ )τ τ + α(τ )2 τ,               (386c)
                    λ(α, τ ·τ τ ) = τ·(
                                        τ τ + α(τ )
                                                    τ ) + α(τ τ )
                                                                 τ
                                 = τ·
                                      τ τ + α(τ )
                                                  τ τ + α(τ τ )
                                                                τ.                  (386d)

The values of λ(α, t) are continued in Table 386(I) up to trees of order 5. For
convenience, each tree is given in product form as well as in pictorial form.
  From (386a)–(386d), we find

          (αβ)(τ ) = β(τ ) + α(τ )β(∅),
         (αβ)(τ τ ) = β(τ τ ) + α(τ )β(τ ) + α(τ τ )β(∅),
      (αβ)(τ τ · τ ) = β(τ τ · τ ) + 2α(τ )β(τ τ ) + α(τ )2 β(τ ) + α(τ τ · τ )β(∅),
      (αβ)(τ · τ τ ) = β(τ · τ τ ) + α(τ )β(τ τ ) + α(τ τ )β(τ ) + α(τ · τ τ )β(∅).

It will be convenient to extend these formulae up to trees of order 5, and we
present this in Table 386(II). For convenience, we denote the empty tree by
t0 and the trees of order 1 to 5 by ti , i = 1, 2, . . . , 17. We also write αi and βi
for α(ti ) and β(ti ), respectively. Note that α0 does not appear in this table
because it always has the value α(∅) = 1.
   Because Table 386(II) has reference value, we supplement the information
it contains with Table 386(III), which gives the formulae for (α−1 )(t) where
r(t) ≤ 5 and α ∈ G1 .
```
</details>

**References:**
- uses_equation: `eq:383a`
- uses_equation: `eq:386a`
- uses_equation: `eq:386b`
- uses_equation: `eq:386c`
- uses_equation: `eq:386d`

---

### Theorem 387A (p.320)
*Section 36, Subsection 387*

```
Theorem 387A If α ∈ G1 such that α(τ ) = 1, and m is an integer with
m ∈ {0, 1, −1}, then α(m) = αm implies that α = E.
```

<details><summary>Proof</summary>

```
Proof. For any tree t = τ , we have α(m) (t) = r(t)m α(t) + Q1 and αm (t) =
mα(t) + Q2 , where Q1 and Q2 are expressions involving α(u) for r(u) < r(t).
Suppose that α(u) has been proved equal to E(u) for all such trees. Then

                          α(m) (t) = r(t)m α(t) + Q1 ,
                           αm (t) = mα(t) + Q2 ,
                          E (m) (t) = r(t)m E(t) + Q1 ,
                           E m (t) = mE(t) + Q2 ,

so that α(m) (t) = αm (t) implies that

                        (r(t)m − m)(α(t) − E(t)) = 0,

implying that α(t) = E(t), because r(t)m = m whenever r(t) > 1 and
m ∈ {0, 1, −1}.                                                  

   Of the three excluded values of m in Theorem 387A, only m = −1
is interesting. Methods for which α(−1) = α−1 have a special property
which makes them of potential value as the source of efficient extrapolation

procedures. Consider the solution of an initial value problem over an interval
[x0 , x] using n steps of a Runge–Kutta method with stepsize h = (x − x0 )/n.
Suppose the computed solution can be expanded in an asymptotic series in h,
                                       ∞
                                       
                              y(x) +         Ci hi .                   (387e)
                                       i=1

If the elementary weight function for the method is α, then the method
corresponding to (α(−1) )−1 exactly undoes the work of the method but
with h reversed. This means that the asymptotic error expansion for this
reversed method would correspond to changing the sign of h in (387e). If
α = (α(−1) )−1 , this would give exactly the same expansion, so that (387e) is
an even function. It then becomes possible to extend the applicability of the
method by extrapolation in even powers only.
```
</details>

**References:**
- uses_equation: `eq:387e`

---

### Theorem 388A (p.321)
*Section 36, Subsection 388*

```
Theorem 388A Let α ∈ G1 , β ∈ G1 , γ ∈ G and δ ∈ G be such that
α = β + Hp and γ = δ + Hp . Then αγ = βδ + Hp .
```

<details><summary>Proof</summary>

```
Proof. Two members of G differ by a member of Hp if and only if they take
identical values for any t such that r(t) ≤ p. For any such t, the formula
for (αγ)(t) involves only values of α(u) and γ(u) for r(u) < r(t). Hence,
(αγ)(t) = (βδ)(t).                                                      

  An alternative interpretation of Hp is to use instead 1 + Hp ∈ G1 as a
subgroup of G1 . We have:
```
</details>

---

### Theorem 388B (p.321)
*Section 36, Subsection 388*

```
Theorem 388B Let α, β ∈ G1 ; then

                                 α = β + Hp                            (388a)

if and only if
                               α = β(1 + Hp ).                         (388b)
```

<details><summary>Proof</summary>

```
Proof. Both (388a) and (388b) are equivalent to the statement α(t) = β(t)
for all t such that r(t) ≤ p.                                          

  Furthermore, we have:
```
</details>

**References:**
- uses_equation: `eq:388a`
- uses_equation: `eq:388b`

**Referenced by:**
- `thm:388C` (uses_theorem)

---

### Theorem 388C (p.322)
*Section 36, Subsection 388*

```
Theorem 388C The subgroup 1 + Hp is a normal subgroup of G1 .
```

<details><summary>Proof</summary>

```
Proof. Theorem 388B is equally true if (388b) is replaced by α = (1 + Hp )β.
Hence, for any β ∈ G1 , (1 + Hp )β = β(1 + Hp ).                          

   Quotient groups of the form G1 /(1 + Hp ) can be formed, and we consider
their significance in the description of numerical methods. Suppose that m and
m are Runge–Kutta methods with corresponding elementary weight functions
α and α. If m and m are related by the requirement that for any smooth
problem the results computed by these methods in a single step differ by
O(hp+1 ), then this means that α(t) = α(t), whenever r(t) ≤ p. However, this
is identical to the statement that

                                       α ∈ (1 + Hp )α,

which means that α and α map canonically into the same member of the
quotient group G1 /(1 + Hp ).
  Because we also have the ideal Hp at our disposal, this interpretation of
equivalent computations modulo O(hp+1 ) can be extended to approximations
represented by members of G, and not just of G1 .
  The C(ξ) and D(ξ) conditions can also be represented using subgroups.
```
</details>

**References:**
- uses_theorem: `thm:388B`
- uses_equation: `eq:388b`

---

### Theorem 388E (p.322)
*Section 36, Subsection 388*

```
Theorem 388E The set C(ξ) is a normal subgroup of G1 .

A proof of this result, and of Theorem 388G below, is given in Butcher (1972).
  The D(ξ) condition is also represented by a subset of G1 , which is also
known to generate a normal subgroup.
```

**References:**
- uses_theorem: `thm:388G`

---

### Theorem 388G (p.322)
*Section 36, Subsection 388*

```
Theorem 388G The set D(ξ) is a normal subgroup of G1 .

   The importance of these semi-groups is that E is a member of each of them
and methods can be constructed which also lie in them. We first prove the
following result:
```

**Referenced by:**
- `thm:388E` (uses_theorem)

---

### Theorem 388H (p.323)
*Section 36, Subsection 388*

```
Theorem 388H For any real θ and positive integer ξ, E (θ) ∈ C(ξ) and
E (θ) ∈ D(ξ).
```

<details><summary>Proof</summary>

```
Proof. To show that E (θ) ∈ C(ξ), we note that E (θ) (t) = γ(t)−1 θ r(t) and that
if E (θ) is substituted for α in (388c), then both sides are equal to
                              θ r(t)+r(t1 )+···+r(tm )+1
                                                                          .
              (r(t) + r(t1 ) + · · · + r(tm ) + 1)γ(t)γ(t1 ) · · · γ(tm )
To prove that E (θ) ∈ D(ξ), substitute E into (388d). We find
                  r(t)                  r(u)            1    1
                              +                      =     ·     .             
         (r(t) + r(u))γ(t)γ(u) (r(t) + r(u))γ(t)γ(u)   γ(t) γ(u)
```
</details>

**References:**
- uses_equation: `eq:388c`
- uses_equation: `eq:388d`

---

## Lemmas (15)

### Lemma 310B (p.173)
*Section 31, Subsection 310*

```
Lemma 310B The value of (310i) is
                                            r(t)
                                      h F (t)(y0 ),
                                     θ(t)
                                          σ(t)
                               t∈T

where θ is defined by
                             
                             
                              1,         t = τ,
                      
                      θ(t) =   k
                             
                                 θ(ti ), t = [t1 t2 · · · tk ].
                                 i=1
                                                                                      m
                                                              1 t2 · · · tj ],
```

<details><summary>Proof</summary>

```
Proof. Use Theorem 306A. The case t = τ is obvious. For t = [tm 1 m2       j


where t1 , t2 , . . . , tj are distinct, the factor
                                
                                      j          −1
                                 σ(I)   σ(tj )mj     ,
                                         i=1

where I is the index set consisting of m1 copies of 1, m2 copies of 2, . . . and
mj copies of j, is equal to σ(t)−1 .                                           
```
</details>

**References:**
- uses_theorem: `thm:306A`
- uses_equation: `eq:310i`

**Referenced by:**
- `thm:311D` (uses_lemma)
- `lem:313A` (uses_lemma)

---

### Lemma 311A (p.174)
*Section 31, Subsection 311*

```
Lemma 311A Let S = S0 ∪ {s} be an ordered set, where every member of
S0 is less than s. Let t be a member of TS∗0 . Then
                                      d
                                        F (|t|)(y(x))
                                     dx
is the sum of F (|u|)(y(x)) over all u ∈ TS∗ such that the subtree formed by
removing s from the set of vertices is t.
```

<details><summary>Proof</summary>

```
Proof. If S = {s0 , s}, then the result is equivalent to
                             d
                               f (y(x)) = f  (y(x))f (y(x)).
                            dx
We now complete the proof by induction in the case S = {s0 } ∪ S1 ∪ S2 ∪ · · · ∪
Sk ∪ {s}, where {s0 }, S1 , S2 , . . . , Sk , {s} are disjoint subsets of the ordered
set S. By the induction hypothesis, assume that the result of the lemma is
true, when S is replaced by Si , i = 1, 2, . . . , k. If t ∈ TS∗0 , then
                                |t| = [|t1 | |t2 | · · · |tk |],
where ti ∈ TS∗i , i = 1, 2, . . . , k. Differentiate

  F (|t|)(y(x))
                                                                                 
           = f (k)(y(x)) F (|t1 |)(y(x)), F (|t2 |)(y(x)), . . . , F (|tk |)(y(x)) , (311a)

to obtain
                                  Q0 + Q1 + Q2 + · · · + Qk ,
where
                                                                                        
 Q0 = f (k+1) (y(x)) F (|t1 |)(y(x)), F (|t2 |)(y(x)), . . . , F (|tk |)(y(x)), f (y(x))
and, for i = 1, 2, . . . , k,
                                                d                                       
      Qi = f (k) (y(x)) F (|t1 |)(y(x)), . . . , F (|ti |)(y(x)), . . . , F (|tk |)(y(x)) .
                                                dx
The value of Q0 is
                                F ([|t1 | |t2 | · · · |tk | |t0 |])(y(x)),
where |t0 | is τ labelled with the single label s. For i = 1, 2, . . . , k, the value
of Qi is the sum of all terms of the form (311a), with F (|ti |)(y(x)) replaced
by terms of the form F (|ui |)(y(x)), where ui is formed from ti by adding an
additional leaf labelled by s. The result of the lemma follows by combining
all terms contributing to the derivative of (311a).                                
```
</details>

**References:**
- uses_equation: `eq:311a`

---

### Lemma 312B (p.179)
*Section 31, Subsection 312*

```
Lemma 312B Denote the vertex set V of the tree t by the set of index
symbols V = {j, k, l, . . . }, where j is the root of t. Let the corresponding edge
set be E. Form the expression

                                   bj             akl                                  (312e)
                                        (k,l)∈E


and sum this over each member of V ranging over the index set {1, 2, . . . , s}.

The resulting sum is the value of Φ(t). A similar formula for Φi (t), where i
is not a member of V , is found by replacing (312e) by

                                          aij             akl                     (312f)
                                                (k,l)∈E


and summing this as for Φ(t).

   Note that, although c does explicitly appear in Definition"    312A or Lemma
312B, it is usually convenient to carry out the summations sl=1 akl to yield
a result ck if l denotes a leaf (terminal vertex) of V . This is possible because
l occurs only once in (312e) and (312f).
   We illustrate the relationship between the trees and the corresponding
elementary weights in Table 312(I). For each of the four trees, we write Φ(t)
in the form given directly by Lemma 312B, and also with the summation
over leaves explicitly carried out. Finally, we present in Table 312(II) the
elementary weights up to order 5.
```

**References:**
- uses_equation: `eq:312e`
- uses_equation: `eq:312f`

---

### Lemma 313A (p.180)
*Section 31, Subsection 313*

```
Lemma 313A Let k = 1, 2, . . . ,. If
                                          1
              Yi = y0 +                        Φi (t)hr(t) F (t)(y0 ) + O(hk ),   (313a)
                                          σ(t)
                               r(t)≤k−1


then
                               1
         hf (Yi ) =                 (Φi D)(t)hr(t) F (t)(y0 ) + O(hk+1 ).         (313b)
                               σ(t)
                      r(t)≤k
```

<details><summary>Proof</summary>

```
Proof.
%n     Use Lemma 310B. The coefficient of σ(t)−1 F (t)(y0 )hr(t) in hf (Yi ) is
 j=1 i (tj ), where t = [t1 t2 · · · tk ].
    Φ                                                                      

   We are now in a position to derive the formal Taylor expansion for the
computed solution. The proof we give for this result is for a general Runge–
Kutta method that may be implicit. In the case of an explicit method, the
iterations used in the proof can be replaced by a sequence of expansions for
Y1 , for hf (Y1 ), for Y2 , for hf (Y2 ), and so on until we reach Ys , hf (Ys ) and
finally y1 .
```
</details>

**References:**
- uses_lemma: `lem:310B`
- uses_equation: `eq:313a`
- uses_equation: `eq:313b`

**Referenced by:**
- `thm:313B` (uses_lemma)

---

### Lemma 319A (p.188)
*Section 31, Subsection 319*

```
Lemma 319A Let f denote a function Rm → Rm , assumed to satisfy a
Lipschitz condition with constant L. Let y0 ∈ Rm and z0 ∈ Rm be two input
values to a step with the Runge–Kutta method (A, b , c), using stepsize h ≤ h0 ,
where h0 Lρ(|A|) < 1, and let y1 and z1 be the corresponding output values.
Then
                         y1 − z1 ≤ (1 + hL ) y0 − z0 ,
where
                               L = L|b |(I − h0 L|A|)−1 1.
```

<details><summary>Proof</summary>

```
Proof. Denote the stage values by Yi and  " Zi , i = 1, 2, . . . , s, respectively.
From the equation Yi − Zi = (y0 − z0 ) + h sj=1 aij (f (Yj ) − f (Zj )), we deduce
that
                                            s
               Yi − Zi ≤ y0 − z0 + h0 L         |aij | Yj − Zj ,
                                                  j=1

so that, substituting into
                                                  
                                                  s
                   y1 − z1 ≤ y0 − z0 + hL               |bj | Yj − Zj ,
                                                  j=1

we obtain the result.                                                                     

                                                                               y(xn )
                                                                    y(xn−1 )
                                                         y(xn−2 )                 δn
                                                                        δn−1
                                                             δn−2                 ∆n−1

                                                                                  ∆n−2
                                 y(x3 )
                      y(x2 )           δ3
           y(x1 )           δ2
y(x0 )
                 δ1
 y0                                                                               ∆3
            y1         y2         y3
                                                                                  ∆2
                                                          yn−2
                                                                     yn−1         ∆1
                                                                                yn

 x0         x1         x2         x3                      xn−2       xn−1       xn
 Figure 319(ii)       Growth of global errors from local errors referred to the exact
                                       solution


   To see how to use this result, consider Figures 319(i) and 319(ii). Each of
these shows the development of global errors generated by local truncation
errors in individual steps. In Figure 319(i), the local truncation errors are
referred to the computed solution. That is, in this figure, δk is the difference
between the exact solution defined by an initial value at the start of step k
and the numerical solution computed in this step. Furthermore, ∆k is the
contribution to the global error resulting from the error δk in step k. An
alternative view of the growth of errors is seen from Figure 319(ii), where
δk is now the difference between the exact solution at xk and the computed
solution found by using an input value yk−1 at the start of this step exactly
equal to y(xk−1 ). As in the previous figure, ∆k is the contribution to the
global error resulting from the local error δk . To obtain a bound on the global
truncation error we first need an estimate on δ1 , δ2 , . . . , δn using these bounds.
We then estimate by how much δk can " grow to ∆k , k = 1, 2, . . . , n. The global
error is then bounded in norm by nk=1 ∆k . We have a bound already from
(110c) on how much a perturbation in the exact solution can grow. If we were
basing our global error bound on Figure 319(i) then this would be exactly
what we need. However, we use Figure 319(ii), and in this case we obtain the
same growth factor but with L replaced by L . The advantage of using an
argument based on this figure, rather than on Figure 319(i), is that we can
then use local truncation error defined in the standard way, by comparing the
exact solution at step value xn with the numerically computed result over a
single step with initial value y(xn−1 ).
```
</details>

**References:**
- uses_equation: `eq:110c`

---

### Lemma 322A (p.197)
*Section 32, Subsection 322*

```
Lemma 322A If P and Q are each 3 × 3 matrices such that their product
has the form                           
                            r11 r12 0
                                       
                    P Q =  r21 r22 0  ,
                             0    0 0
where                                                          !
                                                 r11   r12
                                     det                               = 0,
                                                 r21   r22
then either the last row of P is zero or the last column of Q is zero.
```

<details><summary>Proof</summary>

```
Proof. Because P Q is singular, either P is singular or Q is singular. In the
first case, let u = 0 be such that u P = 0, and therefore u P Q = 0; in
the second case, let v = 0 be such that Qv = 0, and therefore P Qv = 0.
Because of the form of P Q, this implies that the first two components of u
(or, respectively, the first two components of v) are zero.                 

  To obtain the result that D(1) necessarily holds if s = p = 4, we apply
```
</details>

---

### Lemma 342A (p.236)
*Section 33, Subsection 342*

```
Lemma 342A There exist polynomials Pn∗ : [0, 1] → R, of degrees n, for
n = 0, 1, 2, . . . with the properties that
                      1
                           ∗
                         Pm  (x)Pn∗ (x)dx = 0, m = n,          (342a)
                      0
                                    Pn∗ (1) = 1,       n = 0, 1, 2, . . . .           (342b)

Furthermore, the polynomials defined by (342a) and (342b) have the following
additional properties:

   Pn∗ (1 − x) = (−1)n Pn∗ (x),     n = 0, 1, 2, . . . ,                              (342c)
   1
                    1
    Pn∗ (x)2dx =         ,      n = 0, 1, 2, . . . ,                                  (342d)
   0              2n + 1
                     n
        Pn∗ (x) =            (x2 − x)n ,          n = 0, 1, 2, . . . ,                (342e)
                  n! dx
      nPn∗ (x) = (2x−1)(2n−1)Pn−1
                              ∗             ∗
                                  (x)−(n−1)Pn−2 (x), n = 2, 3, 4, . . . ,
                                                                         (342f)
  Pn∗ has n distinct real zeros in the interval (0, 1),            n = 0, 1, 2, . . . . (342g)
```

<details><summary>Proof</summary>

```
Proof. We give only outline proofs of these well-known results. The
orthogonality property (342a), of the polynomials defined by (342e), follows
by repeated integration by parts. The value at x = 1 follows by substituting
x = 1 + ξ in (342e) and evaluating the coefficient of the lowest degree term.
The fact that Pn∗ is an even or odd polynomial in 2x − 1, as stated in (342c),
follows from (342e). The highest degree coefficients in Pn∗ and Pn−1 ∗
                                                                       can be
                      ∗                       ∗
compared so that nPn (x) − (2x − 1)(2n − 1)Pn−1 (x) is a polynomial, Q say,
of degree less than n. Because Q has the same parity as n, it is of degree

less than n − 1. A simple calculation shows that Q is orthogonal to Pk∗ for
                                                               ∗
k < n − 2. Hence, (342f) follows except for the value of the Pn−2  coefficient,
which is resolved by substituting x = 1. The final result (342g) is proved by
supposing, on the contrary, that Pn∗ (x) = Q(x)R(x), where the polynomial
factors Q and R have degrees m < n and   1 n − m, respectively, and where R
has no zeros in (0, 1). We now find that 0 Pn∗ (x)Q(x)dx = 0, even though the
integrand is not zero and has a constant sign.                             

    In preparation for constructing a Runge–Kutta method based on the zeros
ci , i = 1, 2, . . . , s of Ps∗ , we look at the associated quadrature formula.
```
</details>

**References:**
- uses_equation: `eq:342a`
- uses_equation: `eq:342b`
- uses_equation: `eq:342c`
- uses_equation: `eq:342d`
- uses_equation: `eq:342e`
- uses_equation: `eq:342f`
- uses_equation: `eq:342g`

---

### Lemma 342B (p.237)
*Section 33, Subsection 342*

```
Lemma 342B Let c1 , c2 , . . . denote the zeros of Ps∗ . Then there exist positive
numbers b1 , b2 , . . . , bs such that
                                1          
                                            s
                                   φ(x)dx =   bi φ(ci ),                   (342h)
                              0                 i=1

for any polynomial of degree less than 2s. The bi are unique.
```

<details><summary>Proof</summary>

```
Proof. Choose bi , i = 1, 2, . . . , s, so that (342h) holds for any φ of degree less
than s. Because the ci are distinct the choice of the bi is unique. To prove
that (342h) holds for degree up to 2s − 1, write

                           φ(x) = Ps∗ (x)Q(x) + R(x),

where the quotient Q and the remainder R have degrees not exceeding s − 1.
We now have
 1           1                  1              
                                                  s             
                                                                s
    φ(x)dx =     Ps∗ (x)Q(x)dx +     R(x)dx = 0 +   bi R(ci ) =   bi φ(ci ).
 0              0                     0                  i=1            i=1

To prove the bi are positive, let φ(x) denote the square of the polynomial
formed by dividing Ps∗ (x) by x − ci . Substitute into (342h), and the result
follows.                                                                   

   We note that the choice of the ci as the zeros of Ps∗ is the only one possible
for (342h) to hold for φ of degree as high as 2s − 1. If this were not the case,
let
                                       s
                              S(x) =      (x − ci )
                                          i=1

and substitute φ(x) = S(x)Q(x) for any polynomial Q of degree less than s.
It is found that S is orthogonal to all polynomials of lower degree and hence,
apart from a scale factor, is identical to Ps∗ .
   We now consider the possibility of constructing an s-stage implicit Runge–
Kutta method with order 2s. If such a method exists, then the values of the

vectors c and b are known. In the case s = 2 we can explore the possibility
of choosing the only free parameters that remain, to satisfy four additional
order conditions. Surprisingly, this can be done. Write the tableau in the form
                        √                           √
                    2 − √6                      2 − 6 − a11
                    1     3                     1     3
                                     a11
                                     √
                                 2 + 6 − a22
                    1     3      1    3
                    2 + 6                           a22                      (342i)
                                                               .
                                       1             1
                                       2             2

For the trees , , , , the order conditions are satisfied. These are just the
B(4) conditions introduced in Subsection 321. The remaining trees and the
conditions that result from substituting the values from (342i) and simplifying
are:

                                                          a11 = a22 ,
                                          √            √        1
                                      (1 − 3)a11 + (1 + 3)a22 = ,
                                                                2
                                                              a11 = a22 ,
                        √               √         √                 1
                 (1 +       3)a11 + (1 − 3)a22 + 2 3(a211 − a222 ) = .
                                                                    2
These are all satisfied by a11 = a22 = 14 .
   We also notice that C(2) and D(2) are satisfied by these values, and
it is natural to ask if it is possible, in general, to satisfy both C(s) and
D(s) assuming that the b and c vectors have been chosen to satisfy the
quadrature conditions. A crucial link in the chain connecting these conditions
is E(s, s), given by (321c), and we present a result which expresses the essential
connections between them. It will be convenient to write G(η) to represent
the fact that a given Runge–Kutta method has order η.
```
</details>

**References:**
- uses_equation: `eq:342h`
- uses_equation: `eq:342i`
- uses_equation: `eq:321c`
- uses_section: `sec:321`

---

### Lemma 351A (p.251)
*Section 36, Subsection 351*

```
Lemma 351A Let (A, b, c) denote a Runge–Kutta method. Then its stability
function is given by
                                    det (I + z(1b − A))
                           R(z) =                       .
                                         det(I − zA)


                               40i




                          α

                          α                            50




                               −40i


          Figure 350(i)   A(α) stability region for the method (350c)
```

<details><summary>Proof</summary>

```
Proof. Because a rank 1 s × s matrix uv has characteristic polynomial
det(Iw − uv ) = ws−1 (w − v u), a matrix of the form I + uv has characteristic
polynomial (w−1)s−1 (w−1−v u) and determinant of the form 1+v u. Hence,
                                  
          det I + z1b (I − zA)−1 = 1 + zb (I − zA)−1 1 = R(z).

We now note that
                                               
              I + z(1b − A) = I + z1b (I − zA)−1 (I − zA),

so that
                   det (I + z(1b − A)) = R(z) det(I − zA).                  
  Now write the stability function of a Runge–Kutta method as the ratio of
two polynomials
                                        N (z)
                               R(z) =
                                        D(z)
and define the E-polynomial by

                    E(y) = D(iy)D(−iy) − N (iy)N (−iy).
```
</details>

**References:**
- uses_equation: `eq:350c`

---

### Lemma 359A (p.277)
*Section 36, Subsection 359*

```
Lemma 359A Let
                                   XG = W BAW,
where A and B = diag(b) are as for the Gauss method of order 2s. Also let
                          1
                   ξk = √        ,               k = 1, 2, . . . , s − 1.
                       2 4k2 − 1
Then
                                                                                 
                   1
                   2     −ξ1       0         0          ···         0       0
                                                                                 
              ξ1         0       −ξ2        0          ···         0       0     
                                                                                 
              0          ξ2       0        −ξ3         ···         0       0     
                                                                                 
        XG =  .           ..       ..        ..                    ..      ..    .
              ..           .        .         .                     .       .    
                                                                                 
                                                                                 
              0          0        0         0          ···         0     −ξs−1   
               0          0        0         0          ···        ξs−1      0
```

<details><summary>Proof</summary>

```
Proof. From linear combinations of identities included in the condition
E(s, s), given by (321c), we have
               
               s 
                 s                                1           u
                         bi φ(ci )aij ψ(cj ) =         φ(u)         ψ(v)dvdu,
               i=1 j=1                            0            0


for polynomials φ and ψ each with degree less than s. Use the polynomials
φ = Pk−1 , ψ = Pl−1 and we have a formula for the (k, l) element of XG . Add
to this the result for k and l interchanged and use integration by parts. We
have                            1             1
          (XG )kl + (XG )lk =      Pk−1 (u)du     Pl−1 (v)dv = δk1 δl1 .
                                   0                    0
This result determines the diagonal elements of XG , and also implies the
skew-symmetric form of XG − 12 e1 e1 . We now determine u     the form of the
lower triangular elements. If k > l + 1, the integral 0 Pl−1 (v)dv has lower
degree than Pk−1 and is therefore orthogonal to it. Thus, in this case,
         u 0. It remains to evaluate (XG )k,k−1 for k = 1, 2, . . . , s − 1. The
(XG )kl =
integral 0 Pk−1 (v)dv is a polynomial in u of degree k and can be written in the
form θPk (u) added to a polynomial of degree less than k. The integral of Pk (u)
multiplied by the polynomial of degree less than k is zero, by orthogonality,
and the integral reduces to
                               1
                                  θPk (u)2 du = θ.
                                   0

                                                             k−1
The
  √ value of θ can
          2k−2  be found by noting that the coefficient of v     in Pk−1 (v)
is 2k − 1 k−1 , with a similar formula for the leading coefficient of Pk (u).

Hence,                                           √           
                                             1
                                                  2k − 1 2k−2      1
                   (XG )k,k−1 = θ =          k
                                                 √        = √
                                                          k−1
                                                                         .                        
                                                  2k + 1 2k     2 4k 2−1
                                                          k
  The computation of elements of X = W BAW for any Runge–Kutta
method, for which W makes sense, will lead to the same (k, l) elements as
in XG as long as k + l ≤ p + 1. We state this formally.
```
</details>

**References:**
- uses_equation: `eq:321c`

---

### Lemma 383A (p.309)
*Section 36, Subsection 383*

```
Lemma 383A Let α and β be multiplicative mappings from the forests to
the real numbers. Then αβ is multiplicative.
```

<details><summary>Proof</summary>

```
Proof. It will be sufficient to consider the value of (αβ)(S), where S = S1 ∪S2 .
Each R  S can be written as R = R1 ∪ R2 , where R1  S1 and R2  S2 . We
now have
                      
          (αβ)(S) =       α(S \ R)β(R)
                       R S
                                                  
                   =           α(S1 \ R1 )β(R1 )           α(S2 \ R2 )β(R2 )
                       R1 S1                       R2 S2

                   = (αβ)(S1 )(αβ)(S2 ).                                       
  We next show that the product we have defined is associative.
```
</details>

---

### Lemma 383B (p.309)
*Section 36, Subsection 383*

```
Lemma 383B Let α, β and γ be multiplicative mappings from forests to
reals. Then
                        (αβ)γ = α(βγ).
```

<details><summary>Proof</summary>

```
Proof. If Q  R  S then (R \ Q)  (S \ Q). Hence, we find
                     
      ((αβ)γ)(S) =      (αβ)(S \ Q)γ(Q)
                       Q S
                               
                   =                     α((S \ Q) \ (R \ Q))β(R \ Q)γ(Q)
                       Q S (R\Q) (S\Q)
                       
                   =            α(S \ R)β(R \ Q)γ(Q)
                       Q RR S
                       
                   =         α(S \ R)(βγ)(R)
                       R S
                   = (α(βγ))(S).                                               

   We can now restrict multiplication to trees, and we note that associativity
still remains. The semi-group that has been constructed on the set G1 is
                                                                           −1
actually a group because we can construct both left and right inverses, αleft
       −1
and αright  say, for any α ∈ G1 , which must be equal because
                                             
                −1      −1      −1        −1      −1       −1
               αleft = αleft  ααright  = αleft α αright = αright .
```
</details>

---

### Lemma 383C (p.310)
*Section 36, Subsection 383*

```
Lemma 383C Given α ∈ G1 , there exist a left inverse and a right inverse.
```

<details><summary>Proof</summary>

```
Proof. We show, by induction on the order of t, that it is possible to
construct β such that (αβ)(t) = 0 or (βα)(t) = 0, for all t ∈ T . Because
(αβ)(τ ) = (βα)(τ ) = α(τ ) + β(τ ), the result is clear for order 1. Suppose the
result has been proved for all trees of order less than that of t = τ ; then we
note that
                      (αβ)(t) = α(t) + β(t) + φ(t, α, β)
and
                         (βα)(t) = α(t) + β(t) + φ(t, β, α),
where φ(t, α, β) involves the values of α and β only for trees with orders less
than r(t). Hence, it is possible to assign a value to β(t) so that (αβ)(t) = 0
or that (βα)(t) = 0, respectively. Thus it is possible to construct β as a left
inverse or right inverse of α.                                               

   Having established the existence of an inverse for any α ∈ G1 , we find a
convenient formula for α−1 . We write S for a tree t, written in the form (V, E),
and P(S) for the set of all partitions of S. This means that if P ∈ P(S), then
P is a forest formed by possibly removing some of the edges from E. Another
way of expressing this is that the components of P are trees (Vi , Ei ), for
i = 1, 2, . . . , n, where V is the union of V1 , V2 , . . . , Vn and each Ei is a subset
of E. The integer n, denoting the number of components of P , will be written
as #P . We write ti as the tree represented by (Vi , Ei ).
```
</details>

---

### Lemma 383D (p.310)
*Section 36, Subsection 383*

```
Lemma 383D Given α ∈ G1 and t ∈ T , written in the form (V, E), then

                                              
                                                #P
                                −1
                            α        (t) =             (−α(ti )).                (383b)
                                             P ∈P(S) i=1
```

<details><summary>Proof</summary>

```
Proof. Construct a mapping β ∈ G1 equal to the right-hand side of (383b).
We show that for any t ∈ T , (αβ)(t) = 0 so that αβ = 1. Let t = (V, E).
For any partition P with components (Vi , Ei ), for i = 1, 2, . . . , n, we consider
the set of possible combinations of {1, 2, . . . , n}, with the restriction that if
C is such a combination, then no edge (v1 , v2 ) ∈ E exists with v1 ∈ Vi and
v2 ∈ Vj , with i and j distinct members of C. Let C(P ) denote the set of all

such combinations of P ∈ P(t). Given C ∈ P , denote by C the complement
of C in P .
   The value of (αβ)(t) can be written in the form
                     
                                    α(ti )(−1)#C   α(tj ).
                   P ∈P(t) C∈C(P ) i∈C                   j∈C

For any particular partition P , the total contribution is
                            
                                                #P
                                     (−1)n−#C         α(ti ).
                           C∈C(P )              i=1
                       "
This is zero because    C∈C(P ) (−1)
                                       n−#C
                                              = 0.                            
```
</details>

**References:**
- uses_equation: `eq:383b`

---

### Lemma 389A (p.323)
*Section 36, Subsection 389*

```
Lemma 389A A Runge–Kutta method with corresponding group element α
has effective order p if and only if (389a) holds, where β is such that β(τ ) = 0.
```

<details><summary>Proof</summary>

```
Proof. Suppose that (389a) holds with β replaced by β. Let β = E (− 
                                                                    β(τ )) 
                                                                          β,
so that β(τ ) = 0. We then find
                                                  
                                             )  −1
                                         E −β(τ
                      βαβ −1 = E −β(τ ) βα       β
                                           β−1 E 
                                = E −β(τ ) βα      β(τ )

                                               
                                ∈ E −β(τ ) EE β(τ ) (1 + Hp )
                                = E(1 + Hp ).                                  

   Once we have found effective order conditions on α and found a
corresponding choice of β for α satisfying these conditions, we can use Lemma
389A in reverse to construct a family of possible perturbing methods.
   To obtain the conditions we need on α we have constructed Table 389(I)
based on Table 386(II). In this table, the trees up to order 5 are numbered, just
as in the earlier table, and βαβ −1 ∈ E(1+Hp ) is replaced by βα ∈ Eβ(1+Hp ),
for convenience. In the order conditions formed from Table 389(I), we regard
β2 , β3 , . . . as free parameters. Simplifications are achieved by substituting
values of α1 , α2 , . . . , as they are found, into later equations that make use of
them. The order conditions are
                 α1 = 1,
                 α2 = 12 ,
                 α3 = 2β2 + 13 ,
                 α4 = 16 ,
                 α5 = 3β2 + 3β3 + 14 ,
                 α6 = β2 + β3 + β4 + 18 ,
                 α7 = β2 − β3 + 2β4 + 12
                                       1
                                         ,
                       1
                 α8 = 24 ,
                 α9 = 4β2 + 6β3 + 4β5 + 15 ,
                α10 = 53 β2 + 52 β3 + β4 + β5 + 2β6 + 10
                                                       1
                                                         ,
                α11 = 43 β2 + 12 β3 + 2β4 + 2β6 + β7 + 15
                                                        1
                                                          ,
                α12 = 13 β2 − 2β22 + 12 β3 + 12 β4 + β6 + β8 + 30
                                                                1
                                                                  ,
                α13 = 23 β2 − β22 + β3 + β4 + 2β6 + 20
                                                     1
                                                       ,
                α14 = β2 + 3β4 − β5 + 3β7 + 20
                                             1
                                               ,
                α15 = 13 β2 + 32 β4 − β6 + β7 + β8 + 40
                                                      1
                                                        ,
                α16 = 13 β2 − 12 β3 + β4 − β7 + 2β8 + 60
                                                       1
                                                         ,
                       1
                α17 = 120 .
  For explicit Runge–Kutta methods with fourth (effective) order, four stages
are still necessary, but there is much more freedom than for methods with the
same classical order. For fifth effective order there is a real saving in that only
five stages are necessary. For the fourth order case, we need to choose the
coefficients of the method so that
                                     α1 = 1,
                                     α2 = 12 ,
                                     α4 = 16 ,
                                           1
                                     α8 = 24 ,


                        Table 389(I)      Effective order conditions

      i r(ti ) (βα)(ti )                           (Eβ)(ti )
   1      1   α1                                   1
   2      2   α2 + β2                              β2 + 12
   3      3   α3 + β3                              β3 + 2β2 + 13
   4      3   α4 + β2 α1 + β4                      β4 + β2 + 16
   5      4   α5 + β5                              β5 + 3β3 + 3β2 + 14
   6      4   α6 + β2 α2 + β6                      β6 + β4 + β3 + 32 β2 + 18
                                                                    1
   7      4   α7 + β3 α1 + β7                      β7 + 2β4 + β2 + 12
   8      4   α8 + β2 α2 + β4 α1 + β8              β8 + β4 + 12 β2 + 24
                                                                      1

   9      5   α9 + β9                              β9 + 4β5 + 6β3 + 4β2 + 15
 10       5   α10 + β2 α3 + β10                    β10 +2β6 +β5 +β4 + 52 β3 +2β2 + 10
                                                                                    1

 11       5   α11 + β3 α2 + β11                    β11 +β7 +2β6 +2β4 +β3 + 43 β2 + 15
                                                                                    1

 12       5   α12 + β2 α3 + β4 α2 + β12            β12 +β8 +β6 +β4 + 12 β3 + 23 β2 + 30
                                                                                      1

                                                                               1
 13       5   α13 + 2β2 α4 + β22 α1 + β13          β13 + 2β6 + β4 + β3 + β2 + 20
                                                                           1
 14       5   α14 + β5 α1 + β14                    β14 + 3β7 + 3β4 + β2 + 20
 15       5   α15 + β2 α4 + +β6 α1 + β15           β15 + β8 + β7 + 32 β4 + 12 β2 + 40
                                                                                    1

 16       5   α16 + β3 α2 + β7 α1 + β16            β16 + 2β8 + β4 + 13 β2 + 60
                                                                             1

 17       5   α17 +β2 α4 +β4 α2 +β8 α1 +β17 β17 + β8 + 12 β4 + 16 β2 + 120
                                                                        1




and so that the equation formed by eliminating the various β values from the
equations for α3 , α5 , α6 an α7 is satisfied. This final effective order condition
is
                            α3 − α5 + 2α6 − α7 = 14 ,
and the five condition equations written in terms of the coefficients in a four-
stage method are

                                                                b1 + b2 + b3 + b4 = 1,
                                                               b2 c2 + b3 c3 + b4 c4 = 12 ,
                                                  b3 a32 c2 + b4 a42 c2 + b4 a43 c3 = 16 ,
                                                                                         1
                                                                        b4 a43 a32 c2 = 24 ,
      b2 c22 (1 − c2 ) + b3 c23 (1 − c3 ) + b4 c24 (1 − c4 )
            + b3 a32 c2 (2c3 − c2 ) + b4 a42 c2 (2c4 − c2 ) + b4 a43 c3 (2c4 − c3 ) = 14 .


Table 389(II)       Group elements associated with a special effective order 4 method

                t    E(t) α(t)          β(t)        (β −1 E)(t) (β −1 Eβ (r) )(t)
                       1      1          0               1                    1
                       1      1                           1                   1
                       2      2          0                2                   2
                       1      1                           1                   1
                       3      3          0                3                   3
                       1      1           1              11                 11+r 3
                       6      6          72              72                   72
                       1      1           1              13                 26+r 4
                       4      4          108             54                  108
                       1       5          1               13             26+3r 3 +r 4
                       8      36         216             108                216
                                                                         19+6r 3 −r 4
                        1
                       12
                              1
                              9        − 216
                                          1               19
                                                         216                216
                        1      1                          1                 2+r 3
                       24     24         0               36                  72




  We do not attempt to find a general solution to these equations, but instead
explore a mild deviation from full classical order. In fact, we assume that the
perturbing method has β2 = β3 = 0, so that we now have the conditions
                                                               b1 + b2 + b3 + b4 = 1,
                                                              b2 c2 + b3 c3 + b4 c4 = 12 ,
                                                              b2 c22 + b3 c23 + b4 c24 = 13 ,
                                               b3 a32 c2 + b4 a42 c2 + b4 a43 c3 = 16 ,
                                                              b2 c32 + b3 c33 + b4 c34 = 14 ,
       b3 a32 c2 (2c3 − c2 ) + b4 a42 c2 (2c4 − c2 ) + b4 a43 c3 (2c4 − c3 ) = 14 ,
                                                                                        1
                                                                       b4 a43 a32 c2 = 24 .
  Methods satisfying these more general conditions do not need to have c4 = 1
and we can find, for example, the tableau

                                   0
                                   1      1
                                   3      3
                                   2      1     1
                                   3      6     2
                                                                                                (389b)
                                   5      5          5
                                                0
                                   6     24          8           .
                                          1     1         2
                                         10     2    0    5

  A suitable starting method, which does not advance the solution forward
but introduces the correct perturbation so that (389b) faithfully reproduces
this perturbation to within order 4, is given by the tableau

                          0
                          1         1
                          2         2
                          3         3           0                                             (389c)
                          1
                                    0         − 13         2
                          3                                 3               .
                                  − 24
                                     1           1
                                                24       − 18           1
                                                                        8

The freedom that lay at our disposal in selecting this starting procedure was
used to guarantee a certain simplicity in the choice of finishing procedure.
This was in fact decided on first, and has a tableau identical with (389b)
except for the b vector. The reason for this choice is that no extra work is
required to obtain an output value because the stages in the final step will
already have been completed. The tableau for this final step is

                                    0
                                    1     1
                                    3     3
                                    2     1      1
                                    3     6      2
                                                                                              (389d)
                                    5     5          5
                                                 0
                                    6    24          8             .
                                          3      1   1       4
                                         20      3   4      15

  This example method has not been optimized in any way, and is therefore
not proposed for a practical computation. On the other hand, it shows that
the search for efficient methods need not be restricted to the class of Runge–
Kutta methods satisfying classical order conditions. It might be argued that
methods with only effective order cannot be used in practice because stepsize
change is not possible without carrying out a finishing step followed by a new
start with the modified stepsize. However, if, after carrying out a step with the
method introduced here, a stepsize change from h to rh is required, then this
can be done by simply adding one additional stage and choosing the vector
b which depends on r. The tableau for this h-adjusting step is

      0
      1       1
      3       3
      2       1               1
      3       6               2
                                                                                              (389e)
      5        5                                 5
      6       24              0                  8
      1
      2
              13
              40
                              1
                              6
                                                 1
                                                24               − 30
                                                                    1
                                                                                          .
          3+r 3 −2r 4   2−3r 3 +4r 4     1−3r 3 +2r 4       4+3r 3 −r 4
             20              6                4                15               r3 − r4

Rather than carry out detailed derivations of the various tableaux we have
introduced, we present in Table 389(II) the values of the group elements in
G1 /(1 + H4 ) that arise in the computations. These group elements are β,
corresponding to the starting method (389c), α for the main method (389b),

β −1 E corresponding to the finishing method (389d) and, finally, β −1 Eβ (r)
for the stepsize-adjusting method (389e). For convenience in checking the
computations, E is also provided.
```
</details>

**References:**
- uses_equation: `eq:389a`
- uses_equation: `eq:389b`
- uses_equation: `eq:389c`
- uses_equation: `eq:389d`
- uses_equation: `eq:389e`

---

## Corollaries (3)

### Corollary 342D (p.240)
*Section 33, Subsection 342*

```
Corollary 342D A Runge–Kutta method has order 2s if and only if its
coefficients are chosen as follows:
  (i) Choose c1 , c2 , . . . , cs as the zeros of Ps∗ .
 (ii) Choose b1 , b2 , . . . , bs to satisfy the B(s) condition.
(iii) Choose aij , i, j = 1, 2, . . . , s, to satisfy the C(s) condition.
```

<details><summary>Proof</summary>

```
Proof. If the method has order 2s then B(2s) is satisfied. This implies (i)
and (ii). Because the order is 2s, E(s, s) is satisfied and this, together with
B(2s), implies (iii). Conversely, if (i) and (ii) are satisfied, then B(2s) holds
and this in turn implies E(s, s). This fact, together with B(2s), implies D(s).
Finally, use (342l) to complete the proof.                                    

  We conclude this introduction to the Gauss methods by listing the tableaux
for s = 1, 2, 3 and orders 2, 4, 6, respectively:
       s = 1, p = 2,
                                                 1    1
                                                 2    2
                                                            ;
                                                      1


       s = 2, p = 4,                   √                             √
                                   2 − √6                       4 − 6
                                   1     3           1          1      3
                                                     4√
                                   1     3    1    3               1
                                   2 + 6      4 + 6                4
                                                 1                 1       ;
                                                 2                 2


       s = 3, p = 6,
                               √                           √                √
                          2 − 10                      9 − 15          36 − √30
                          1      15        5          2      15        5      15
                                          36 √

                                                                      36 − 24
                             1          5     15         2             5      15
                             2√        36 + √24          9√
                          1      15     5     15      2      15           5
                          2 + 10       36 + 30        9 +   15           36        .
                                           5             4                5
                                          18             9               18
```
</details>

**References:**
- uses_equation: `eq:342l`

---

### Corollary 356D (p.269)
*Section 36, Subsection 356*

```
Corollary 356D Under the same conditions of Theorem 356C, with the
additional assumption that the method is DJ-irreducible,

                             bj > 0,      j = 1, 2, . . . , s.
```

<details><summary>Proof</summary>

```
Proof. Suppose that for i ≤ s, bi > 0, but that for i > s, bi = 0. In this case,
M can be written in partitioned form as

                                          M      N
                                 M=

and this cannot be positive semi-definite unless N = 0. This implies that

                        aij = 0,       whenever i ≤ s < j,
implying that the method is reducible to a method with only s stages.         
```
</details>

**References:**
- uses_theorem: `thm:356C`

**Referenced by:**
- `def:356B` (uses_corollary)

---

### Corollary 359B (p.278)
*Section 36, Subsection 359*

```
Corollary 359B Let (A, b, c) denote a Runge–Kutta method for which B =
diag(b) is positive definite and for which the abscissae are distinct. Define
W by (359b) and X by X = W BAW . Then Xkl = (XG )kl , as long as
k + l ≤ p + 1.

 The W transformation is related in an interesting way to the C(m) and
D(m) conditions, which can be written in the equivalent forms
               s                 ci
   C(m) :         aij Pk−1 (cj )=     Pk−1 (x)dx, k≤m, i=1, 2, . . . , s,
                     j=1                         0
                   
                   s                                  1
     D(m) :              bi Pk−1 (ci )aij =bj              Pk−1 (x)dx, k≤m, j=1, 2, . . . , s.
                   i=1                                cj

It follows from these observations that, if B(m) and C(m) are true, then the
first m columns of X will be the same as for XG . Similarly, if B(m) and D(m),
then the first m rows of X and XG will agree.
   Amongst the methods known to be algebraically stable, we have already
encountered the Gauss and Radau IIA methods. We can extend this list to
include further methods.
```

**References:**
- uses_equation: `eq:359b`

---
