# Chapter 4: Linear Multistep Methods

Pages 317-371

## Sections

- **40** Preliminaries
- **41** The Order of Linear Multistep Methods
- **42** Errors and Error Growth
- **43** Stability Characteristics
- **44** Order and Stability Barriers
- **45** One-Leg Methods and G-stability
- **46** Implementation Issues

## Definitions (8)

### Definition 402A (p.340)
*Section 40, Subsection 402*

```
Definition 402A Consider a linear multistep method used with a starting
method as described in the previous discussion. Let Ym denote the
approximation to y(x) found using m steps with h = (x−x0 )/m. The function
f is assumed to be continuous and to satisfy a Lipschitz condition in its second
variable. The linear multistep method is said to be ‘convergent’ if, for any such
initial value problem,

                         Ym − y(x) → 0,       as m → ∞.
```

---

### Definition 403A (p.341)
*Section 40, Subsection 403*

```
Definition 403A A linear multistep method [α, β] is ‘stable’ if the difference
equation (403a) has only bounded solutions.

Because stability concepts of one sort or another abound in the theory of
initial value problems, ‘stability’ is often referred to as ‘zero-stability’ – for
example, in Lambert (1991)) – or as ‘stability in the sense of Dahlquist’.
```

**References:**
- uses_equation: `eq:403a`

---

### Definition 404A (p.341)
*Section 40, Subsection 404*

```
Definition 404A A linear multistep method satisfying (404a) is said to be
‘preconsistent’.

  Now consider the differential equation

                             y  (x) = 1,        y(x0 ) = 0,

with exact solution at the step values

                                        yi = hi.

If this solution has been found for i = n − k, n − k + 1, . . . , n − 1, then it is
also correct for i = n if and only if
                                                                               
 nh = α1 (n − 1)h + α2 (n − 2)h + · · · + αk (n − k)h + h β0 + β1 + · · · + βk .

Assuming the method is preconsistent, the factor h can be cancelled and then
n times (404a) can be subtracted. We then find

                   α1 + 2α2 + · · · + kαk = β0 + β1 + · · · + βk .                (404b)

This leads to the following definition:
```

**References:**
- uses_equation: `eq:404a`
- uses_equation: `eq:404b`

---

### Definition 404B (p.342)
*Section 40, Subsection 404*

```
Definition 404B A linear multistep method satisfying (404a) and (404b) is
said to be ‘consistent’.

  Another way of looking at the consistency conditions is to suppose that yi =
y(xi )+O(h2 ) and that f (xi , yi ) = y  (xi )+O(h), for i = n−k, n−k+1, . . . , n−1,
and to consider the computation of yn using the equation

  yn − hβ0 f (xn , yn )
        = α1 yn−1 + α2 yn−2 + · · · + αk yn−k
         + h(β1 f (xn−1 , yn−1 ) + β2 f (xn−2 , yn−2 ) + · · · + βk f (xn−k , yn−k ))
        = α1 y(xn−1 ) + α2 y(xn−2 ) + · · · + αk y(xn−k )
         + h(β1 y  (xn−1 ) + β2 y  (xn−2 ) + · · · + βk y  (xn−k )).

Expand the right-hand side by Taylor’s theorem about xn , and we find
                      
   α1 + α2 + · · · + αk y(xn )
                                                           
                  + β1 + · · · + βk − α1 − 2α2 − · · · − kαk hy  (xn ) + O(h2 ).

This will give the correct answer of

                                  y(xn ) − hβ0 y  (xn ),

to within O(h2 ), if and only if

                                α1 + α2 + · · · + αk = 1

and
                   α1 + 2α2 + · · · + kαk = β0 + β1 + · · · + βk .
Hence, we can view the two requirements of consistency as criteria that the
computed solution is capable of maintaining accuracy to within O(h2 ) over
one step, and therefore over several steps.
```

**References:**
- uses_equation: `eq:404a`
- uses_equation: `eq:404b`

---

### Definition 406A (p.345)
*Section 40, Subsection 406*

```
Definition 406A Let [α, β] be a consistent linear multistep method. The
‘local truncation error’ associated with a differentiable function y at a point x
with stepsize h is the value of

                                 
                                 k                        
                                                          k
           L(y, x, h) = y(x) −         αi y(x − ih) − h         βi y  (x − ih).
                                 i=1                      i=0

   We estimate the value of L(y, x, h) when y is the exact solution to (406a),
and where not only x but also each x − hi, for i = 1, 2, . . . , k, lies in the
interval [x0 , x].
```

**References:**
- uses_equation: `eq:406a`

---

### Definition 422B (p.359)
*Section 42, Subsection 422*

```
Definition 422B Corresponding to a linear multistep method [α, β], the
member of G1 represents the ‘underlying one-step method’.
  As we have already remarked, the mapping Φ in (422b), if it exists in more
than a notional sense, is really the object of interest and this really is the
underlying one-step method.
```

**References:**
- uses_equation: `eq:422b`

---

### Definition 442A (p.377)
*Section 44, Subsection 441*

```
Definition 442A The function Φ is A-stable if RΦ has no intersection with
the product set

                   {w ∈ C : |w| > 1} × {z ∈ C : Re(z) ≤ 0}.

This definition is equivalent to the requirement that for any z in the left half
complex plane, all eigenvalues of the stability matrix are in the closed unit
disc. Just as in the case of Runge–Kutta methods, for which the Riemann
surface has only a single sheet, scaling the eigenvalues by exp(−z) does not
affect the behaviour on the imaginary axis or introduce or remove any poles.




         Figure 442(i)     Order star for the second order BDF method




          Figure 442(ii)    Order star for the third order BDF method


Hence we can consider a modified Riemann surface based on the function
Φ(w exp(z), z). Just as for the Runge–Kutta case, one of the sheets, known as
the ‘principal sheet’, behaves like w = 1 + O(z p+1 ) and order stars appear.
  We illustrate this by considering the case of the second order backward
difference method, for which
                                  2                 4           1
           Φ(w exp(z), z) = 1 − z exp(2z)w2 − exp(z)w + ,
                                   3                  3           3
and the third order backward difference method, for which
                       6              18               9          2
 Φ(w exp(z), z) = 1 − z exp(3z)w3 −        exp(2z)w2 +     exp(z)w − .
                       11               11              11          11
For the second order case, shown in Figure 442(i), a pole at z = 32 is marked,
together with a branch point at z = − 12 . Note that for z ∈ (∞, − 21 ), the two
roots of the equation Φ(w exp(z), z) = 0, for all z in this real interval, have
equal magnitudes. In this figure, light shading grey indicates that a region

has exactly one of the sheets with magnitude greater than 1. A darker grey is
used to indicate that both sheets have magnitudes greater than 1.
   This method is A-stable, as we already know. This can be seen from the
order star by noting that the only pole is in the right half-plane, and that the
fingers do not intersect the imaginary axis. On the other hand, the third order
method (Figure 442(ii)) is not A-stable because, in this case, the intersection
of the imaginary axis with one the fingers is now not empty. Note that for
the third order case, there is a single pole at z = 116 and that three shades
of grey are used to distinguish regions where one, two or three sheets have
magnitudes greater than 1.
   Although A-stable Runge–Kutta methods can have arbitrarily high orders,
the order of A-stable linear multistep methods is restricted to 2. This was first
proved using order stars (Wanner, Hairer and Nørsett, 1978), but we will use
the closely related approach of order arrows (Butcher, 2002). These will be
introduced in the Riemann surface case in the next subsection.

Given a relationship between complex numbers z and w defined by an equation
of the form
                              Φ(w exp(z), z) = 0,

we can define order arrows as the set of points for which w is real and positive.
In particular, the order arrows that emanate from zero correspond to w with
increasing real parts (the up arrows) and, on these arrows, w ∈ (1, ∞), or
decreasing real parts (the down arrows) and for which w ∈ [0, 1).
   Order arrows on Riemann surfaces are illustrated for the BDF2 method
(Figure 443(i)) and for the BDF3 method (Figure 443(ii)). Just as for Runge–
Kutta methods, the up arrows either terminate at the pole z = β0−1 or at −∞,
and down arrows terminate at the zero z = −αk βk−1 or at +∞. In interpreting
these remarks, we need to allow for the possibility that the path traced out by
an up or down arrow meets another arrow at a branch point of the Riemann
surface. However, this special case is easily included in the general rule with a
possible freedom to choose between two continuations of the incoming arrow.
   The ‘principal sheet’ of the Riemann surface will refer to a neighbourhood
of (0, 1) for which the relationship between z and w is injective; that is,
it behaves as though w is a function of z. As long as Φ(w, 0) has only a
single zero with value w = 1, this idea makes sense. On the principal sheet,
w exp(z) = exp(z) + O(z p+1 ), and the behaviour at zero is similar to what
happens for one-step methods. These simple ideas are enough to prove the
Dahlquist second order bound:
```

---

### Definition 451A (p.385)
*Section 45, Subsection 451*

```
Definition 451A A one-leg method [α, β] is ‘G-stable’ if M given by (451e)
is positive semi-definite.

  We present the example of the BDF2 method with
                                     4   1      2
                    [α(z), β(z)] = 1 − z + z 2 ,   .
                                      3   3      3
Write
                                          g11     g12
                                   G=
                                          g12     g22
and we find                                                          
                                  3 − g11      − 89 − g12
                                  4                              2
                                                                 9
                                                                   
                     M =        − 89 − g12    g11 − g22        g12  ,
                                      2
                                      9            g12          g22
which is positive semi-definite if and only if G is the positive definite matrix
                                           10
                                             9    − 94
                                 G=                         .
                                          − 49      2
                                                    9


Denote the point at which the derivative is calculated in step n of a one-leg
method by yn . Also denote the corresponding x argument as x  n . Hence, we
have
                             "k
                                   iβi
                  xn = xn − "i=0
                                k
                                       h,                              (452a)
                                i=0 βi
                         k    −1 k
                   yn =     βi         βi yn−i ,                      (452b)
                             i=0          i=0
                           
                           k                    
                                                 k         
                    yn =         αn−i yn−i +                   xn , yn ).
                                                         βi f (             (452c)
                           i=1                   i=0

Form a linear combination of yn−i , i = 0, 1, . . . , k, given by (452b), based on
the coefficients in the α polynomial, and note that the operators α(E −1 ) and
β(E −1 ) are commutative. We have

                                   
                                   k                     
                                                         k
                           yn −         αi yn−i = h                xn , yn ).
                                                               βi f (                   (452d)
                                   i=1                   i=1


The relationship between the y and y sequences given by (452b) and (452d)
was suggested by Dahlquist (1976) as an indication that stability questions
for a linear multistep method can be replaced by similar questions for the
corresponding one-leg method.
```

**References:**
- uses_equation: `eq:451e`
- uses_equation: `eq:452a`
- uses_equation: `eq:452b`
- uses_equation: `eq:452c`
- uses_equation: `eq:452d`

---

## Theorems (16)

### Theorem 405A (p.343)
*Section 40, Subsection 405*

```
Theorem 405A A convergent linear multistep method is stable.
```

<details><summary>Proof</summary>

```
Proof. If the method were not stable, there would exist an unbounded
sequence η satisfying the difference equation

                    ηn = α1 ηn−1 + α2 ηn−2 + · · · + αk ηn−k .

Define the sequence ζ by
                                         n
                                  ζn = max |ηi |,
                                        i=0

so that ζ converges monotonically to ∞. Consider the solution of the initial
value problem
                         y  (x) = 0,  y(0) = 0,
with x = 1. Assuming that n steps are to be performed, we use a stepsize
h = 1/n and initial values yi = ηi /ζn , for i = 0, 1, . . . , k − 1. The condition
that yi → 0 for 0 ≤ i ≤ k − 1 is satisfied because ζn → ∞. The approximation
computed for y(x) is equal to ηn /ζn . Because the ζ sequence is unbounded,
there will be an infinite number of values of n for which |ζn | is greater than
the greatest magnitude amongst previous members of this sequence. For such
values of n, |ηn /ζn | = 1, and therefore the sequence n → ηn /ζn cannot
converge to 0.                                                                    
```
</details>

**Referenced by:**
- `thm:405B` (uses_theorem)

---

### Theorem 405B (p.343)
*Section 40, Subsection 405*

```
Theorem 405B A convergent linear multistep method is preconsistent.
```

<details><summary>Proof</summary>

```
Proof. By Theorem 405A, we can assume that the method is stable. Let η
be defined as the solution to the difference equation

                    ηn = α1 ηn−1 + α2 ηn−2 + · · · + αk ηn−k ,

with initial values η0 = η1 = · · · = ηk−1 = 1. The computed solution of the
problem
                      y  (x) = 0,   y(0) = 1,    x = 1,
using n steps, is equal to yn = ηn . Since this converges to 1 as n → ∞, it
follows that, for any > 0, there exists an n sufficiently large so that |yi −1| ≤

for i = n − k, n − k + 1, . . . , n. Hence,

        &                         & &        
                                             k         &      
                                                               k      
        &1 − α1 − α2 − · · · − αk & ≤ &&ηn −           &
                                               αi ηn−i & + 1 +   |αi |
                                                i=1                     i=1
                                         
                                          k      
                                     = 1+   |αi | .
                                               i=1

Because this can be arbitrarily small, it follows that

                            1 − α1 − α2 − · · · − αk = 0.                         
```
</details>

**References:**
- uses_theorem: `thm:405A`

---

### Theorem 405C (p.344)
*Section 40, Subsection 405*

```
Theorem 405C A convergent linear multistep is consistent.
```

<details><summary>Proof</summary>

```
Proof. We note first that

                            α1 + 2α2 + · · · + kαk = 0,

since, if the expression were zero, the method would not be stable. Define the
sequence η by

                        β0 + β1 + · · · + βk
                ηi =                          i,       i = 0, 1, 2, . . . .
                       α1 + 2α2 + · · · + kαk

Consider the numerical solution of the initial value problem

                              y  (x) = 1,       y(0) = 0,

with the output computed at x = 1, and with n steps computed with stepsize
h = 1/n. Choose starting approximations as

                                              1
                                      yi =      ηi ,                          (405a)
                                              n
for i = 0, 1, 2, . . . , k − 1, so that these values converge to zero as n → ∞. We
verify that the computed solution for all values of i = 0, 1, 2, . . . , n is given
also by (405a), and it follows that the approximation at x = 1 is

                                β0 + β1 + · · · + βk
                                                      ,
                               α1 + 2α2 + · · · + kαk

independent of n. Because convergence implies that the limit of this is 1, it
follows that
                β0 + β1 + · · · + βk = α1 + 2α2 + · · · + kαk .            
```
</details>

**References:**
- uses_equation: `eq:405a`

---

### Theorem 406C (p.347)
*Section 40, Subsection 406*

```
Theorem 406C Let           n denote the vector


                                       n = y(xn ) − yn .


Then for h0 sufficiently small so that h0 |β0 |L < 1 and h < h0 , there exist
constants C and D such that
                                  
                          k
                                    
                       n−   αi n−i 
                                            k
                                    ≤ Ch max
                                           i=1
                                                           n−i       + Dh2 .              (406c)
                           i=1

                          "                "
```

<details><summary>Proof</summary>

```
Proof. The value of n − ki=1 αi n−i − h ki=0 βi (f (y(xn−i )) − f (yn−i )) is
the difference of two terms, of which the first can be bounded by a constant
times h2 , by Theorem 406B, and the second is zero. This means that

                                 
                                 k

                           n−          αi n−i = T1 + T2 + T3 ,                            (406d)
                                 i=1

where

      T1 = h|β0 | f (y(xn )) − f (yn )                ≤ hL|β0 | ·       n   ,             (406e)
                                                   
               k                                    k
      T2      
           = h   βi (f (y(xn−i )) − f (yn−i )) ≤ hL
                                                               k
                                                        |βi | max                     ,   (406f)
                                                                        i=1
                                                                                n−i
                i=1                                            i=1

and T3 can be bounded in terms of a constant times h2 . We now use (406d)
twice. First, assuming h ≤ h0 , obtain a bound on (1 − hL|β0 |) n in terms
of maxki=1 n−i and terms that are bounded by a constant times h2 . Hence,
obtain a bound on n . Then, by inserting this preliminary result in the
bound on T1 , we obtain the result of the theorem.                       
```
</details>

**References:**
- uses_equation: `eq:406c`
- uses_equation: `eq:406d`
- uses_equation: `eq:406e`
- uses_equation: `eq:406f`

**Referenced by:**
- `thm:406D` (uses_theorem)

---

### Theorem 406D (p.347)
*Section 40, Subsection 406*

```
Theorem 406D A stable consistent linear multistep method is convergent.
```

<details><summary>Proof</summary>

```
Proof. Write (406c) in the form

                                         
                                         k

                                 n =           αi n−i + ψn ,
                                         i=1

where, according to Theorem 406C,
                                               k
                            ψn ≤ Ch max             n−i   + Dh2 ,
                                           i=1

for h sufficiently small. Define θ1 , θ2 , . . . as in Subsection 141, and note that,
because the method is convergent, the θ sequence is bounded. From Theorem
141A, we have
                             
                             k−1               n
                         n =      θ     
                                    n−i i   +      θn−i ψi ,
                                       i=0           i=k

where i , for i = 0, 1, . . . , k − 1, are linear combinations of the errors in yi and
tend to zero as h → 0. Hence we have

                           
                           k−1                     
                                                   n−1

                  n   ≤Θ          i + ΘChk                i   + ΘD(n − k)h2 ,       (406g)
                           i=0                     i=k

where Θ = sup∞i=1 |θi | and the factor k is introduced in the second summation
in (406g) because the same maximum value of n−i may arise in up to k
adjacent terms. We rewrite (406g) in the form

                                         
                                         n−1
              n   ≤ φ(h) + ΘChk                i   + ΘDnh2 ,          0   ≤ φ(h),
                                         i=1

where φ(h) takes positive values and will converge to zero as h → 0. It now
follows that n ≤ un , where the sequence u is defined by

                                 
                                 n−1
                 un = ΘChk             ui + ΘDnh2 + φ(h),          u0 = φ(h).        (406h)
                                 i=1

By subtracting (406h) with n replaced by n − 1, we find that
                                                     
                       Dh                          Dh
                  un +     = (1 + ΘChk) un−1 +          ,
                       Ck                          Ck

which leads to the bound
                                                                                Dh
             n    ≤ un = (1 + ΘChk)n φ(h) + ((1 + ΘChk)n − 1)
                                                                                Ck
                                                                             Dh
                       ≤ exp(ΘCknh)φ(h) + (exp(ΘCknh) − 1)                      .
                                                                             Ck
To complete the proof, substitute n = m where mh = x − x0 , so that the error
in the approximation at x = x using m steps with stepsize h is bounded by

                                                                      Dh
             exp(ΘCk(x − x0 ))φ(h) + exp(ΘCk(x − x0 ))                   → 0.            
                                                                      Ck
```
</details>

**References:**
- uses_theorem: `thm:406C`
- uses_theorem: `thm:141A`
- uses_equation: `eq:406c`
- uses_equation: `eq:406g`
- uses_equation: `eq:406h`
- uses_section: `sec:141`

---

### Theorem 410A (p.350)
*Section 40, Subsection 410*

```
Theorem 410A The constants C0 , C1 , C2 , . . . in (410b) are given by

         α(exp(−z)) − zβ(exp(−z)) = C0 + C1 z + C2 z 2 + · · · .                  (410c)
```

<details><summary>Proof</summary>

```
Proof. The coefficient of y(xn ) in the Taylor expansion of (410a) is equal to
    "
1 − ki=1 αi , and this equals the constant term in the Taylor expansion of
α(exp(−z)) − zβ(exp(−z)). Now suppose that j = 1, 2, . . . and calculate the
coefficient of y (j) (xn ) in the Taylor expansion of (410a). This equals

                               
                               k
                                          (−i)j  (−i)j−1 ,
                                                  k
                           −         αi        −     βi
                               i=1
                                            j!   i=0
                                                        (j − 1)!

where the coefficient of β0 is −1 if j = 1 and zero for j > 1. This is identical
to the coefficient of z j in the Taylor expansion of α(exp(−z)) − zβ(exp(−z)).
                                                                            

   Altering the expression in (410c) slightly, we can state without proof a
criterion for order:
```
</details>

**References:**
- uses_equation: `eq:410b`
- uses_equation: `eq:410c`
- uses_equation: `eq:410a`

---

### Theorem 410B (p.351)
*Section 40, Subsection 410*

```
Theorem 410B A linear multistep method [α, β] has order p (or higher) if
and only if
                     α(exp(z)) + zβ(exp(z)) = O(z p+1 ).

 Because we have departed from the traditional (ρ, σ) formulation for linear
multistep methods, we restate this result in that standard notation:
```

**Referenced by:**
- `thm:410C` (uses_theorem)

---

### Theorem 410C (p.351)
*Section 40, Subsection 410*

```
Theorem 410C A linear multistep method (ρ, σ) has order p if and only if

                     ρ(exp(z)) − zσ(exp(z)) = O(z p+1 ).

  Return now to Theorem 410B and replace exp(z) by (1 + z)−1 . It is found
that
              α((1 + z)−1 ) − log(1 + z)β((1 + z)−1 ) = O(z p+1 ),     (410d)

where log(1 + z) is defined only in {z ∈ C : |z| < 1} by its power series

                     log(1 + z) = z − 12 z 2 + 13 z 3 − · · · .

Because both α(1 + z) and log(1 + z) vanish when z = 0, it is possible to
rearrange (410d) in the form given in the following result, which we present
without further proof.
```

**References:**
- uses_theorem: `thm:410B`
- uses_equation: `eq:410d`

---

### Theorem 410D (p.351)
*Section 40, Subsection 410*

```
Theorem 410D A linear multistep formula [α, β] has order p if and only if

                       z      α(1 + z)
                                       + β(1 + z) = O(z p ).
                   log(1 + z)    z
```

---

### Theorem 422A (p.358)
*Section 42, Subsection 422*

```
Theorem 422A For any preconsistent, stable linear multistep method [α, β],
there exists a member of the group G1 satisfying (422a).

                             "
```

<details><summary>Proof</summary>

```
Proof. By preconsistency, ki=1 αi = 1. Hence, (422a) is satisfied in the case
of t = ∅, in the sense that if both sides are evaluated for the empty tree, then
they each evaluate to zero. Now consider a tree t with r(t) > 0 and assume

that

  1(u) − α1 η −1 (u) − α2 η −2 (u) − · · · − αk η −k (u)
                − β0 D(u) − β1 η −1 D(u) − β2 η −2 D(u) − · · · − βk η −k D(u) = 0,
is satisfied for every tree u satisfying r(u) < r(t). We will prove that there
exists a value of η(t) such that this equation is also satisfied if u is replaced by
t. The coefficient of η(t) in η −i (t) is equal to i(−1)r(t) and there are no other
terms in η −i (t) with orders greater than r(t) − 1. Furthermore, all terms on
the right-hand side contain only terms with orders less than r(t). Hence, to
satisfy (422a), with both sides evaluated at t, it is only necessary to solve the
equation
                                        k
                           (−1)r(t)−1      iαi η(t) = C,
                                           i=1
where C depends only on lower order trees. The proof by induction on r(t) is
now complete, because the coefficient of η(t) is non-zero, by the stability of
the method.                                                               
```
</details>

**References:**
- uses_equation: `eq:422a`

---

### Theorem 422C (p.359)
*Section 42, Subsection 422*

```
Theorem 422C Let [α, β] denote a preconsistent, stable linear multistep
method and let η denote a solution of (422a). Suppose that yi is represented
by η i for i = 0, 1, 2, . . . , k − 1; then yi is represented by η i for i = k, k + 1, . . . .
```

<details><summary>Proof</summary>

```
Proof. The proof is by induction, and it will only be necessary to show that
yk is represented by η k , since this is a typical case. Multiply (422a) on the left
by η k and we find that

  η k − α1 η k−1 − α2 η k−2 − · · · − αk
                              − β0 η k D − β1 η k−1 D − β2 η k−2 D − · · · − βk D = 0,
so that yk is represented by η k .                                                         

  The concept of an underlying one-step method was introduced by
Kirchgraber (1986). Although the underlying method cannot be represented
as a Runge–Kutta method, it can be represented as a B-series or, what is
equivalent, in the manner that has been introduced here. Of more recent
developments, the extension to general linear methods (Stoffer, 1993) is of
particular interest. This generalization will be considered in Subsection 535.
```
</details>

**References:**
- uses_equation: `eq:422a`
- uses_section: `sec:535`

---

### Theorem 431A (p.366)
*Section 43, Subsection 431*

```
Theorem 431A A polynomial Pn , given by

                Pn (w) = a0 wn + a1 wn−1 + · · · + an−1 w + an ,

where a0 = 0 and n ≥ 2, is strongly stable if and only if

                                  |a0 |2 > |an |2                           (431e)

and Pn−1 is strongly stable, where

  Pn−1 (w)
    = (a0 a0 − an an )wn−1 + (a0 a1 − an an−1 )wn−2 + · · · + (a0 an−1 − an a1 ).
```

<details><summary>Proof</summary>

```
Proof. First note that (431e) is necessary for strong stability because if it
were not true, the product of the zeros could not have a magnitude less than
1. Hence, we assume that this is the case and it remains to prove that Pn is
strongly stable if and only if the same property holds for Pn−1 . It is easy to
verify that
                    wPn−1 (w) = a0 Pn (w) − an wn Pn (w−1 ).
By Rouché’s theorem, wPn−1 (w) has n zeros in the open unit disc if and only
if the same property is true for Pn (w), and the result follows.           

  The result of this theorem is often referred to as the Schur criterion. In the
case of n = 2, it leads to the two conditions

                                           |a0 |2 − |a2 |2 > 0,              (431f)
                     (|a0 | − |a2 | ) − |a0 a1 − a2 a1 | > 0.
                          2       2 2                  2
                                                                            (431g)

  To apply the Schur criterion to the determination of the stability region for
a k-step method, we need to ask for which z the polynomial given by

                        P (w) = wk (α(w−1 ) − zβ(w−1 ))

is strongly stable. We present some examples of the use of this test in
Subsection 433.


  Algorithm 432α      Boundary locus method for low order Adams–Bashforth
                                  methods

  % Second order
  % ------------
  w = exp(i*linspace(0,2*pi));
  z = 2*w.*(w-1)./(3*w-1);
  plot(z)

  % Third order
  % -----------
  w=exp(i*linspace(0,2*pi));
  z=12*(1-w)./(23*w-16*w.^2+5*w.^3);
  plot(z)

  % Fourth order
  % ------------
  w=exp(i*linspace(0,2*pi));
  z=24*(1-w)./(55*w-59*w.^2+37*w.^3-9*w.^4);
  plot(z)
```
</details>

**References:**
- uses_equation: `eq:431e`
- uses_equation: `eq:431f`
- uses_equation: `eq:431g`
- uses_section: `sec:433`

---

### Theorem 441C (p.376)
*Section 44, Subsection 441*

```
Theorem 441C Let [α, β] denote a stable linear multistep method with order
p. Then                    
                             k + 1, k odd,
                      p≤
                             k + 2, k even.
```

<details><summary>Proof</summary>

```
Proof. Consider first the case k odd and evaluate the coefficient of z k+1 in
(441b). This equals
                       ak c2 + ak−2 c4 + · · · + a1 ck+1
and, because no term is positive, the total can be zero only if each term is zero.
However, this would mean that a1 = 0, which is inconsistent with stability.
  In the case k even, we evaluate the coefficient of z k+2 in (441b). This is

                        ak−1 c4 + ak−3 c6 + · · · + a1 ck+2 .

Again, every term is non-positive and because the total is zero, it again follows
that a1 = 0 which contradicts the assumption of stability.                     

  There is some interest in the methods with maximal order 2k + 2, for k
even. For these methods, α has all its zeros on the unit circle. This evidently
gives the methods a symmetry that suggests it might be advantageous to use
them for problems whose behaviour is dominated by linear terms with purely
imaginary eigenvalues. Against this possible advantage is the observation that
the stability regions necessarily have empty interiors.

In their historic paper, Wanner, Hairer and Nørsett (1978) introduced order
stars on Riemann surfaces. Suppose that Φ(w, z) is a polynomial function of
two complex variables, w ∈ W and z ∈ Z. We assume that Z = W = C.
The subset RΦ of W × Z defined by the relation Φ(w, z) = 0 is a Riemann
surface. Suppose that Φ has degree r in w and s in z. We may interpret R
as a mapping from the Z plane which takes z ∈ Z to the set of zeros of the
equation Φ(w, z) = 0 or as a mapping which takes w ∈ W to the set of zeros
of this same equation, but with z now the unknown. The main interpretation
will be that Φ(w, z) is the characteristic polynomial det(wI − M (z)) of the
stability matrix of a multivalue method. If this method has order p then
Φ(exp(z), z) = O(z p+1 ). For ease of notation, we carry over concepts such as
A-stability from multivalue methods, such as linear multistep methods, to the
functions Φ used to characterize their stability.
```
</details>

**References:**
- uses_equation: `eq:441b`

---

### Theorem 443A (p.379)
*Section 44, Subsection 441*

```
Theorem 443A An A-stable linear multistep method cannot have order
greater than 2.




             Figure 443(i)    Order arrows for order 2 BDF method




            Figure 443(ii)     Order arrows for order 3 BDF method
```

<details><summary>Proof</summary>

```
Proof. If the order were greater than 2, there would be more than three up
arrows emanating from the origin. At least three of these up arrows would
come out in the positive direction (or possibly would be tangential to the
imaginary axis). Since there is only one pole, at least two of these arrows
would cross the imaginary axis (or be tangential to it). Hence, the stability
region does not include all of the imaginary axis and the method is not A-
stable.                                                                    

  We can make this result more precise by obtaining a bound on the error
constant for second order A-stable methods. The result yields an optimal role
for the second order Adams–Moulton method, for which the error constant is
− 12
   1
     , because
                              1 + 12 z    1 3
                     exp(z) −      1 = − 12 z + O(z ).
                                                     4
                              1 − 2z
It is not possible to obtain a positive error constant amongst A-stable second
order methods, and it is not possible to obtain an error constant smaller in
magnitude than for the one-step Adams–Moulton method. To prove the result
we use, in place of exp(z), the special stability function (1 + 12 z)/(1 − 12 z) in
forming a relative stability function.
```
</details>

**Referenced by:**
- `thm:443B` (uses_theorem)

---

### Theorem 443B (p.381)
*Section 44, Subsection 441*

```
Theorem 443B Let C denote the error constant for an A-stable second order
linear multistep method. Then
                                          1
                                      C≤−    ,
                                          12
with equality only in the case of the second order Adams–Moulton method.
```

<details><summary>Proof</summary>

```
Proof. Consider the relation
                                              
                                   1 + 12 z
                               Φ w          , z = 0.
                                   1 − 12 z
On the principal sheet, w = 1 − (C + 12  1
                                           )z 3 + O(z 4 ). It is not possible that
      1
C + 12 = 0, because there would then be at least four up arrows emanating
from 0 and, as in the proof of Theorem 443A, this is impossible because there
                                                                           1
is at most one pole in the right half-plane. On the other hand, if C + 12     > 0,
there would be at least two up arrows emanating from zero in the positive
direction and these must cross the imaginary axis.                              
```
</details>

**References:**
- uses_theorem: `thm:443A`

---

### Theorem 454A (p.387)
*Section 45, Subsection 454*

```
Theorem 454A A G-stable linear multistep method is A-stable.
```

<details><summary>Proof</summary>

```
Proof. We use the criterion that if |w| < 1, then z = α(w)/β(w) is in the right
half-plane. Form the inner product W ∗ M W , where M is the matrix given by
(451e) and
                                            
                                         1
                                       w 
                                            
                                       2 
                               W =      w .
                                            
                                       .. 
                                       . 
                                         wk
We find that
                                                        
                                                        k
      α(w)β(w) + α(w)β(w) = W ∗ M W + (1 − |w|2 )               gjl wj−1 wl−1 > 0,
                                                        j,l=1
                   
so that Re α(w)/β(w) > 0.                                                            
```
</details>

**References:**
- uses_equation: `eq:451e`

---

## Lemmas (3)

### Lemma 406B (p.346)
*Section 40, Subsection 406*

```
Lemma 406B If y is the exact solution to the standard initial value problem
and x ∈ [x0 + kh, x], then
                            k                          
                                 1 2
               L(y, x, h) ≤        i |αi | + i|iαi − βi | LM h2 .
                            i=1
                                 2
```

<details><summary>Proof</summary>

```
Proof. We first estimate y(x) − y(x − ih) − ihy  (x) using the identity
                                        0
      y(x) − y(x − ih) − hiy  (x) = h     (f (y(x + hξ)) − f (y(x))) dξ,
                                               −i

so that
                                                     0
          y(x) − y(x − ih) − ihy  (x) ≤ hL               y(x + hξ) − y(x) dξ,
                                                     −i

and noting, that for ξ ≤ 0,
                                        0
           y(x + hξ) − y(x) ≤ h              f (x + hξ) dξ ≤ h|ξ|M,                   (406b)
                                        ξ

so that
                      y(x) − y(x − ih) − ihy  (x) ≤ 12 i2 h2 LM.
From (406b), we see also that

                            f (y(x)) − f (y(x − ih)) ≤ ihLM.
                                                            "k
Because of the consistency of the method, we have
"k                                                           i=1 αi = 1 and
  i=1 (iαi − βi ) = β0 . We now write L(y, x, h) in the form

                      
                      k
       L(y, x, h) =         αi (y(x) − y(x − ih) − ihy  (x))
                      i=1
                                             
                                             k
                                       +h      (iαi − βi )(y  (x) − y  (x − ih));
                                             i=1

this is bounded by

                      1 2                 
                         k                  k
                            i |αi |LM h2 +     i|iαi − βi |LM h2
                      2 i=1                i=1

and the result follows.                                                                   
```
</details>

**References:**
- uses_equation: `eq:406b`

---

### Lemma 441A (p.375)
*Section 44, Subsection 441*

```
Lemma 441A If the method under consideration is stable then a1 > 0 and
ai ≥ 0, for i = 2, 3, . . . , k.
```

<details><summary>Proof</summary>

```
Proof. Write the polynomial a in the form

  a(z) = (1+z)k −α1 (1+z)k−1 (1−z)−α2 (1+z)k−2 (1−z)2 − · · · −αk (1−z)k .

We calculate the value of a1 , the coefficient of z, to be

      k − (k − 2)α1 − (k − 4)α2 − · · · − (−k)αk = kα(1) − 2α (1) = −2α (1),

because α(1) = 0. The polynomial ρ, which we recall is defined by

                      ρ(z) = z k − α1 z k−1 − α2 z k−2 − · · · − αk ,

has no real zeros greater than 1, and hence, because ρ(1) = 0 and because
limz−>∞ ρ(z) = ∞, it is necessary that ρ (1) > 0. Calculate this to be

               ρ (1) = k − (k − 1)α1 − (k − 2)α2 − · · · − αk−1 = a1 .

This completes the proof that a1 > 0.

  Write ζ for a possible zero of a so that, because of the relationship between
this polynomial and α, it follows that
                                               1−ζ
                                               1+ζ
is a zero of α, unless it happens that ζ = −1, in which case there is a drop in
the degree of α. In either case, we must have Re(ζ) ≤ 0. Because all zeros of
a are real, or occur in conjugate pairs, the polynomial a can be decomposed
into factors of the form z − ξ or of the form z 2 − 2ξz + (ξ 2 + η 2 ), where the
real number ξ cannot be positive. This means that all factors have only terms
with coefficients of the same sign, and accordingly this also holds for a itself.
These coefficients must in fact be non-negative because a1 > 0.                  
```
</details>

---

### Lemma 441B (p.376)
*Section 44, Subsection 441*

```
Lemma 441B The coefficients c2 , c4 , . . . are all negative.
                                                 
```

<details><summary>Proof</summary>

```
Proof. Using the series for log (1 + z)/(1 − z) /z, we see that c0 , c2 , c4 , . . .
satisfy
                2       2         
              2 + z 2 + z 4 + · · · (c0 + c2 z 2 + c4 z 4 + · · · ) = 1.  (441c)
                 3       5
It follows that c0 = 12 , c2 = − 16 . We prove c2n < 0 by induction for n = 2,
n = 3, . . . . If c2i < 0 for i = 1, 2, . . . , n − 1 then we multiply (441c) by
2n + 1 − (2n − 1)z 2 . We find
                    ∞
                                   ∞
                                    
                          d2i z ·
                              2i
                                          c2i z 2i = 2n + 1 − (2n − 1)z 2 ,   (441d)
                    i=0             i=0

where, for i = 1, 2, . . . , n,

                        2(2n + 1) 2(2n − 1)        8(n − i)
                d2i =            −          =−                  ,
                          2i + 1    2i − 1     (2i + 1)(2i − 1)

so that d2i < 0, for i = 1, 2, . . . , n − 1, and d2n = 0. Equate the coefficients of
z 2n in (441d) and we find that

                            c2 d2n−2 + c4 d2n−4 + · · · + c2n−2 d2
                  c2n = −                                          < 0.           
                                             d0
  We are now in a position to prove the Dahlquist barrier result.
```
</details>

**References:**
- uses_equation: `eq:441c`
- uses_equation: `eq:441d`

---
