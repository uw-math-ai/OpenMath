# Chapter 5: General Linear Methods

Pages 373-451

## Sections

- **50** Representing Methods in General Linear Form
- **51** Consistency, Stability and Convergence
- **52** The Stability of General Linear Methods
- **53** The Order of General Linear Methods
- **54** Methods with Runge–Kutta stability
- **55** Methods with Inherent Runge–Kutta Stability

## Definitions (15)

### Definition 510A (p.406)
*Section 51, Subsection 510*

```
Definition 510A A general linear method (A, U, B, V ) is ‘preconsistent’ if
there exists a vector u such that
                                       V u = u,                              (510a)
                                       U u = 1.                              (510b)
The vector u is the ‘preconsistency vector’.
```

**References:**
- uses_equation: `eq:510a`
- uses_equation: `eq:510b`

---

### Definition 510B (p.406)
*Section 51, Subsection 510*

```
Definition 510B A general linear method (A, U, B, V ) is ‘consistent’ if it is
preconsistent with preconsistency vector u and there exists a vector v such that
                                   B1 + V v = u + v.                          (510c)

  Just as for linear multistep methods, we need a concept of stability. In the
general linear case this is defined in terms of the power-boundedness of V and,
as we shall see, is related to the solvability of the problem y  = 0.
```

**References:**
- uses_equation: `eq:510c`

---

### Definition 510C (p.407)
*Section 51, Subsection 510*

```
Definition 510C A general linear method (A, U, B, V ) is ‘stable’ if there
exists a constant C such that, for all n = 1, 2, . . . , V n ≤ C.
```

---

### Definition 512A (p.409)
*Section 51, Subsection 512*

```
Definition 512A A general linear method (A, U, B, V ), is ‘convergent’ if for
any initial value problem

                         y  (x) = f (y(x)),       y(x0 ) = y0 ,

subject to the Lipschitz condition f (y) − f (z) ≤ L y − z , there exist a non-
zero vector u ∈ Rr , and a starting procedure φ : (0, ∞) → Rr , such that for
all i = 1, 2, . . . , r, limh→0 φi (h) = ui y(x0 ), and such that for any x > x0 , the
sequence of vectors y [n] , computed using n steps with stepsize h = (x − x0 )/n
and using y [0] = φ(h) in each case, converges to uy(x).

The necessity of stability and consistency, as essential properties of convergent
methods, are proved in the next two subsections, and this is followed by the
converse result that all stable and consistent methods are convergent.
```

**Referenced by:**
- `thm:513A` (uses_definition)

---

### Definition 520A (p.418)
*Section 51, Subsection 520*

```
Definition 520A For a general linear method (A, U, B, V ), the ‘stability
matrix’ M (z) is defined by

                         M (z) = V + zB(I − zA)−1 U.

As we have anticipated, we have the following result:
```

---

### Definition 520C (p.419)
*Section 51, Subsection 520*

```
Definition 520C Let (A, U, B, V ) denote a general linear method and M (z)
the corresponding stability matrix. The ‘stability function’ for the method is
the polynomial Φ(w, z) given by
                           Φ(w, z) = det(wI − M (z)),
and the ‘stability region’ is the subset of the complex plane such that if z is in
this subset, then
                                 ∞
                                sup M (z)n < ∞.
                               n=1

  We refer to the ‘instability region’ as the complement of the stability region.
  Note that in applications of these definitions, Φ(w, z) may be a rational
function. Quite often, the essential properties will be contained in just the
numerator of this expression. We equally refer to the numerator of this rational
function as the stability function.
  We state the following obvious result without proof.
```

---

### Definition 520E (p.419)
*Section 51, Subsection 520*

```
Definition 520E A general linear method is ‘A-stable’ if M (z) is power-
bounded for every z in the left half complex plane.
  Just as for Runge–Kutta and linear multistep methods, A-stability is the
ideal property for a method to possess for it to be applicable to stiff problems.
Corresponding to the further requirement for Runge–Kutta methods that
R(∞) = 0, we have the generalization of L-stability to general linear methods.
```

---

### Definition 520F (p.419)
*Section 51, Subsection 520*

```
Definition 520F A general linear method is L-stable if it is A-stable and
ρ(M (∞)) = 0.
```

---

### Definition 521A (p.420)
*Section 51, Subsection 521*

```
Definition 521A A method with stability function Φ(w, z) has ‘stability
order’ p if
                    Φ(exp(z), z) = O(z p+1 ).

  Suppose the stability function is given by

                                          
                                          k               
                                                          νj
                                                    k−j
                          Φ(w, z) =             w               αjl z j ,
                                          j=0             l=0


where k is the w-degree of Φ and νj is the z-degree of the coefficient of wk−j .
We can regard the sequence of integers

                                 ν = [ν0 , ν1 , . . . , νk ],

as representing the complexity of the stability function Φ. To include all
sensible cases without serious redundancies, we always assume that νj ≥ −1
for j = 0, 1, 2, . . . , k with strict inequality in the cases j = 0 and j = k.
  It is interesting to ask the question: ‘For a given sequence ν, what is the
highest possible stability order?’. The question can be looked at in two parts.
First, there is the question of determining for what p it is possible to find
a function Φ with a given complexity and with stability order p. Secondly,
there is the question of finding a general linear method corresponding to a
given Φ, with order p as close as possible to p. The first half of the question
can be firmly answered and is interesting since it gives rise to speculations
about possible generalizations of the Ehle results on rational approximations
to the exponential function. The definitive result that we have referred to is
as follows:
```

---

### Definition 525A (p.429)
*Section 51, Subsection 525*

```
Definition 525A A general linear method (A, U, B, V ) is G-symplectic if
there exists a positive semi-definite symmetric r × r matrix G and an s × s
diagonal matrix D such that

                                      G = V GV,                          (525a)
                                  DU = B GV,                             (525b)
                             DA + A D = B GB.                            (525c)

The following example of a G-symplectic method was presented in Butcher
(2006):
                                     √                       √ 
                                   3+ 3
                                     6       0     1 − 3+23 3
                                √3            √
                                                        3+2 3 
                                                             √
                    A U         − 3       3+ 3
                                                   1            
                             =     1
                                              6
                                              1
                                                           3    .
                                                                         (525d)
                    B V             2        2    1       0    
                                     1
                                     2     − 12    0    −1
                                                                            √
It can be verified that (525d) satisfies (525a)–(525c) with G = diag(1, 1+ 23 3)
and D = diag( 21 , 12 ).
   Although this method is just one of a large family of such methods which
the author, in collaboration with Laura Hewitt and Adrian Hill of Bath
University, is trying to learn more about, it is chosen for special attention
here. An analysis in Theorem 534A shows that it has order 4 and stage order
2. Although it is based on the same stage abscissae as for the order 4 Gauss
Runge–Kutta method, it has a convenient structure in that A is diagonally
implicit.
   For the harmonic oscillator, the Hamiltonian is supposed to be conserved,
and this happens almost exactly for solutions computed by this method for
any number of steps. Write the problem in the form y  = iy so that for stepsize
h, y [n] = M (ih)y [n−1] where M is the stability matrix. Long term conservation


 1+




 1−
                20        40          60             80        100       120
                                                           n
                                       [n]
       Figure 525(i)   Variation in |y1 | for n = 0, 1, . . . , 140, with h = 0.1;
                                     note that  = 0.000276


requires that the characteristic polynomial of M (ih) has both zeros on the unit
circle. This characteristic polynomial is:
                           √ 2      √                   √ 2
              w2 1 − ih 3+6 3 + w 23 i 3 h − 1 + ih 3+6 3 .

Substitute                                       √
                                     1 + ih 3+6 3
                                w=               √   iW,
                                     1 − ih 3+6 3

and we see that                              √
                            2           2 33
                         W +h                 √     W + 1.
                                  1 + h2 ( 3+6 3 )2
                                 √        √
The coefficient of W lies in (− 3 + 1, 3 − 1) and the zeros of this equation
are therefore on the unit circle for all real h. We can interpret this as saying
that the two terms in
                      [n] 2           √  [n] 2  [n] 2 
                 [n] 2
                p1     + q1        + 1 + 23 3        p2    + q2

are not only conserved in total but are also approximately conserved
individually, as long as there is no round-off error. The justification for this
                                                               [n]
assertion is based on an analysis of the first component of y1 as n varies.
Write the eigenvalues of M (ih) as λ(h) = 1 + O(h) and µ(h) = −1 + O(h)
and suppose the corresponding eigenvectors, in each case scaled with first
component equal to 1, are u(h) and v(h) respectively. If the input y [0] is
                        [n]
au(h) + bv(h) then y1 = aλ(h)n + bµ(h)n with absolute value
                    [n]
                                                     1/2
                  |y1 | = a2 + b2 + 2abRe (λ(h)µ(h))n        .

If |b/a| is small, as it will be for small h if a suitable starting method is used,
  n]
|y1 | will never depart very far from its initial value. This is illustrated in
Figure 525(i) in the case h = 0.1.
```

**References:**
- uses_theorem: `thm:534A`
- uses_equation: `eq:525a`
- uses_equation: `eq:525b`
- uses_equation: `eq:525c`
- uses_equation: `eq:525d`

---

### Definition 530A (p.432)
*Section 51, Subsection 530*

```
Definition 530A A starting method S defined by the generalized Runge–
                                                                   (i)
Kutta methods (530a), for i = 1, 2, . . . , r, is ‘degenerate’ if b0 = 0, for
i = 1, 2, . . . , r, and ‘non-degenerate’ otherwise.
```

**References:**
- uses_equation: `eq:530a`

---

### Definition 530B (p.432)
*Section 51, Subsection 530*

```
Definition 530B Consider a general linear method M and a non-degenerate
starting method S. The method M has order p relative to S if the results found
from SM and ES agree to within O(p+1 ).
```

**Referenced by:**
- `def:530C` (uses_definition)

---

### Definition 530C (p.432)
*Section 51, Subsection 530*

```
Definition 530C A general linear method M has order p if there exists a
non-degenerate starting method S such that M has order p relative to S.

                                                               y [1]
                                 y [0]
                                                                   T
                                                   M

                                         SM
                             S                         F   S
                                           ES


                                    E         T
                 y(x0 )                       y(x1 )
            Figure 531(i)   Representation of local truncation error



   In using Definition 530C, it is usually necessary to construct, or at
least to identify the main features of, the starting method S which gives
the definition a practical meaning. In some situations, where a particular
interpretation of the method is decided in advance, Definition 530B is used
directly. Even though the Taylor series expansions, needed to analyse order,
are straightforward to derive, the details can become very complicated. Hence,
in Subsection 532, we will build a framework for simplifying the analysis. In
the meantime we consider the relationship between local and accumulated
error.
```

**References:**
- uses_definition: `def:530B`
- uses_section: `sec:532`

---

### Definition 542A (p.445)
*Section 54, Subsection 542*

```
Definition 542A A general linear method (A, U, B, V ) has ‘Runge–Kutta
stability’ if the characteristic polynomial given by (542a) has the form

                         Φ(w, z) = wr−1 (w − R(z)).

For a method with Runge–Kutta stability, the rational function R(z) is known
as the ‘stability function’ of the method.

  We will usually abbreviate ‘Runge–Kutta stability’ by ‘RK stability’. We
present two examples of methods satisfying this condition with p = q = r =
s = 2 and with c = [ 0 1 ] . The first is of type 1 and is assumed to have the
form                                                      
                                  0     0       1      0
                               a                      1 
                  A U          21 0            0          
                             =                            .
                  B V          b11 b12 1 − V12 V12 
                                  b11   b12   1 − V12   V12
The assumption that U = I is not a serious restriction because, if U is non-
singular, an equivalent method can be constructed with U = I and B and V
replaced by U B and U V U −1 , respectively. The form chosen for V makes it of
rank 1 and preconsistent for the vector c = [ 1 1 ] .
   By the stage order conditions, it is found that

                                                    1
            φ(z) = (I − zA) exp(cz) =                                .
                                          1 + (1 − a21 )z + 12 z 2

To find B, we have

                  Bz exp(cz) = (exp(z)I − V )φ(z) + O(z 3 ).

Write the coefficients of z and z 2 in separate columns and we deduce that
                                 1 − V12 + a21 V12               2 (1 − V12 )
                                                                 1
                  1 0
          B             =                                                             ,
                  1 1         2 − V12 − a21 + a21 V12          2 − a21 − 12 V12
so that
                            2 − 2 V12 + a21 V12       2 (1 − V12 )
                            1      1                  1
                   B=                                                          .
                              − 12 V12 + a21 V12    2 − a21 − 12 V12
To achieve RK stability, impose the requirement that the stability function
V + zB(I − zA)−1 has zero determinant and it is found that a21 = 2 and
V12 = 12 .
  This gives the method
                                                  
                                    0     0 1 0
                                   2     0 0 1 
                       A U                        
                               = 5              1 
                                                     .               (542b)
                       B V          4
                                           1
                                           4
                                              1
                                              2  2
                                                   
                                     3
                                     4  − 14 12 12
  To derive a type 2 method with RK stability, carry out a similar calculation
but with
                                    λ 0
                             A=               .
                                   a21 λ
In this case, the method is
                                                                                        
                                λ                    0                  1            0
                            2
                                                                                     1 
      A       U                                     λ                  0                
                   =  5−2λ+12λ
                           1+2λ
                                2
                                  +8λ3                                                   ,
      B       V           4+8λ                    4 −λ
                                                   1    2             1
                                                                      2 +λ
                                                                                   1
                                                                                   2 − λ 
                        3−2λ+20λ2 +8λ3      −1+10λ−12λ2 −8λ3
                                                                                   2 −λ
                                                                      1            1
                            4+8λ                 4+8λ                 2 +λ
                   √
or, with λ = 1 − 12 2, for L-stability,
                              √                                           
                           1 − √22       0√              1           0
                        6+2 2                                          
            A U                      1 −   2
                                                         0           1  
                     =       7 √       √ 2                √      √     .                (542c)
                        73−34 2       4 2−5            3− 2        2−1 
            B V             28     √    4  √             2√      √2    
                               87−48 2    34 2−45       3− 2         2−1
                                  28         28           2          2

  Type 3 and type 4 methods do not exist with RK stability, and will not be
explored in detail in this section. We do, however, give a single example of
each. For the type 3 method we have
                                                      
                                      0    0    1 0
                                   0           0 1 
                      A U                 0           
                                = 3                   .             (542d)
                      B V          − 8 − 38 − 34 74 
                                          − 78      9
                                                    8   − 34     7
                                                                 4

This method is designed for parallel computation in the sense that the two
stages do not depend on each other, because A = 0, and hence they can be
evaluated in parallel. Is there any advantage in the use of methods like this?
Of course, the answer will depend on the specific coefficients in the method
but, in the case of (542d), we might wish to compare it with the type 1 method
given by (542b) whose error constant has magnitude 16 . In contrast, (542d) has
error constant 19                           19
                24 which is equivalent to 96 when adjusted for the sequential
cost of one f evaluation per step. Thus, in this case, the type 3 method is less
efficient even under the assumption of perfect speed-up.
  The type 4 method
                               √                              
                              3− 3
                                          0      1        0
                               2         √                    
             A U               0       3− 3
                                                 0        1    
                       =  18−11
                                  √
                                    3 7
                                       √2
                                         3−12  3−2
                                                  √
                                                    3   2
                                                         √
                                                           3−1
                                                               
                                                                        (542e)
             B V               √
                                4     √   4      √
                                                 2      √ 2    
                           22−13 3   9 3−12   3−2 3    2 3−1
                              4         4       2        2

is found to be A-stable with the additional property that its stability matrix
has zero spectral radius at infinity. Just as for the type 3 method we have
introduced, while the advantages of this type of method are not clear, results
found by Singh (1999) are encouraging.
   For type 1 and 2 methods, increasing order presents great challenges in the
solution of the order conditions combined with RK stability requirements. For
an account of the techniques used to find particular methods of orders up to
8, see Butcher and Jackiewicz (1996, 1998).

The characteristic feature of explicit Runge–Kutta methods, that only
minimal information computed in a step is passed on as input to the next
step, is a great advantage of this type of method but it is also a perceived
disadvantage. The advantage lies in excellent stability properties, while the
disadvantage lies in the low stage order to which the second and later stages
are restricted. Almost Runge–Kutta methods (ARK) are an attempt to retain
the advantage but overcome some of the disadvantages.
  Recall the method (505a). Evaluate its stability matrix and we find

 M (z) = V + zB(I − zA)−1 U
                                                                       
     1 + 56 z + 13 z 2 + 48
                          1 3
                            z    1   1      7 2    1 3
                                 6 + 6 z + 48 z + 48 z
                                                            1 2     1 3
                                                           48 z + 96 z
                                                                   1 4 
=  z + 56 z 2 + 13 z 3 + 48
                           1 4
                             z 1     1 2     7 3    1 4
                               6 z + 6 z + 48 z + 48 z     48 z + 96 z 
                                                            1 3
                                                                          .
    z + 2 z + 12 z + 24 z −1 + 2 z − 12 z + 24 z + 24 z
        1 2       7 3      1 4     1     1 2    5 3    1 4      1 4
                                                               48 z

The eigenvalues of this matrix are
                          ;                            <
                                   1  1      1
              σ(M (z)) = 1 + z + z 2 + z 3 + z 4 , 0, 0 ,
                                   2  6     24

Table 543(I)        Calculation of stages and stage derivatives for the method (505a)

                                                                                              
       α     α(∅) α( ) α( ) α( )             α         α( )         α          α               α
       1        1      0     0         0      0             0           0          0               0
      D         0      1     0         0      0             0           0          0               0
      ξ3        0      0     1         θ3     θ4            θ5          θ6         θ7              θ8
                             1         θ3     θ4            θ5        θ6          θ7              θ8
      η1        1      1     2         2       2            2          2           2               2
                                               1                       1          θ3              θ4
     η1 D       0      1     1         1       2            1          2           2               2
                       1     1        1+θ3   1+2θ4      1+θ5        1+2θ6      θ3 +2θ7         θ4 +2θ8
      η2        1      2     8         16     32         16           32          32              32
                             1          1      1          1            1        1+θ3           1+2θ4
     η2 D       0      1     2          4      8          8           16          16              32
      η3        1      1     1
                             2
                                      1−θ3
                                        4
                                             1−2θ4
                                               8       − θ45        − θ46       1−2θ7
                                                                                   8
                                                                                                1−4θ8
                                                                                                  16
                                               1                       1        1−θ3            1−2θ4
     η3 D       0      1     1         1       2            1          2           4               8
                             1         1       1            1          1           1               1
      η4        1      1     2         3       6            4          8          12              24
                                               1                       1           1               1
     η4 D       0      1     1         1       2            1          2           3               6
     E ξ1      1      1     1
                             2
                                       1
                                       3
                                               1
                                               6
                                                            1
                                                            4
                                                                       1
                                                                       8
                                                                                   1
                                                                                  12
                                                                                                   1
                                                                                                  24
     E ξ2      0      1     1     1           1
                                               2            1          1
                                                                       2
                                                                                   1
                                                                                   3
                                                                                                   1
                                                                                                   6
     E ξ3      0      0     1     1           1
                                               2            1          1
                                                                       2
                                                                                   1
                                                                                   2
                                                                                                   1
                                                                                                   4
      ξ1       1      0     0     0             0          0           0          0               0
      ξ2       0      1     0     0             0          0           0          0               0
      ξ3       0      0     1    −1         − 12           1           1
                                                                        2
                                                                                       1
                                                                                       2
                                                                                                   1
                                                                                                   4


so that it is RK stable. Other features of the method are that the minimal
information passed between steps is enough to push the stage order up to
2, and that the third input and output vector need not be evaluated to
great accuracy because of what will be called ‘annihilation conditions’. These
                                                               [n−1]
conditions ensure that errors like O(h3 ) in the input vector y3     only affect
the output results by O(h5 ).
   Assume that the three input approximations are represented by ξ1 = 1,
ξ2 = D and ξ3 , where we assume only that
                       ξ3 (∅) = ξ3 ( ) = 0           and         ξ3 ( ) = 1.

                                    = hy  (xn−1 ), y3  = h2 y  (xn−1 ) + O(h3 ). The
        [n−1]                 [n−1]                        [n−1]
Thus, y1          = y(xn−1 ), y2
output approximations are computed by first evaluating the representations
of the stage values and stage derivatives. Since we are only working to order
5 accuracy in the output results, it will be sufficient to evaluate the stages
only up to order 4. Denote the representations of the four stage values by ηi ,
i = 1, 2, 3, 4. Also, denote the values of ξ3 (t) for trees of orders 3 and 4 by θi ,
i = 3, 4, . . . , 8. Details of the calculation of stage values are shown in Table
543(I).

Table 543(II)             Output and input values for (505a) evaluated at fifth order trees

                                                                                                       
                                                                       
   α      α(     )α              α            α         α             α           α         α           α
   ξ3      θ9         θ10          θ11          θ12      θ13            θ14         θ15      θ16         θ17
   ξ1      1
           120
                       1
                      240       − 1+5θ
                                   240
                                       3
                                             − 1+10θ
                                                480
                                                    4        1
                                                            480       − 120
                                                                          1
                                                                                  − 240
                                                                                      1     1+5θ3
                                                                                             240
                                                                                                        1+10θ4
                                                                                                         480
   ξ2     0          0             0            0          0            0           0          0           0
   ξ3    −1      − 12            − 13         − 16     − 14           − 12        − 14     − 14        − 18


  The output results are intended to represent approximations to Eξ1 , Eξ2
and Eξ3 . Write the representation of yi by E ξi , for i = 1, 2, 3. We calculate ξi
                                                  [n]

up to order 5 trees so that we not only verify fourth order behaviour, but also
obtain information on the principal terms in the local truncation error. As a
first step in this analysis, we note that, to order 4, E ξ1 = E and hence ξ1 = 1.
Similarly ξ2 = D to fourth order. Up to fourth order, we have calculated the
value of E ξ3 = − 13 η1 D − 23 η3 D + 2η4 D − ξ2 and ξ3 is also given in Table
543(I).
  If the calculations are repeated using the specific values [θ3 , θ4 , θ5 , θ6 , θ7 , θ8 ]
= [−1, − 12 , 1, 12 , 12 , 14 ], then we have ξi = ξi + H4 so that, relative to a starting
method defined by ξi , i = 1, 2, 3, the method has order 4. However, a starting
value defined for arbitrary values of θ3 , θ4 , . . . , θ8 produces the specific choice
given by the components of ξ3 after a single step. To investigate this method
more precisely, the values of ξ1 , ξ2 and ξ3 have been calculated also for fifth
order trees and these are shown in Table 543(II).
  A reading of this table suggests that the method not only exhibits fourth
order behaviour but also has reliable behaviour in its principal error terms.
This is in spite of the fact that the starting method provides incorrect
contributions of third and higher order elementary differentials, because these
inaccuracies have no long term effect. The components of the error terms in
the first output component depend on θ3 and θ4 after a single step, but this
effect disappears in later steps.
  In Subsection 544 we consider order 3 ARK methods, and we then return
in Subsection 545 to a more detailed study of order 4 methods. However, we
first discuss some questions which apply to both orders.
  Because we will require methods in these families to have stage order 2, the
matrix U will need to be of the form
                                     U = [ 1 c − A1         2 c − Ac
                                                            1 2
                                                                     ]                                  (543a)
and we will assume this throughout. We also note that the stability matrix
M (z) = V +zB(I −zA)−1 U is always singular because ze1 −e2 is an eigenvalue
of this matrix. We see this by observing that zep (I − zA) = (−ze1 + e2 )B and
(ze1 − e2 )V = zep U .
```

**References:**
- uses_equation: `eq:542a`
- uses_equation: `eq:542b`
- uses_equation: `eq:542c`
- uses_equation: `eq:542d`
- uses_equation: `eq:542e`
- uses_equation: `eq:505a`
- uses_equation: `eq:543a`
- uses_section: `sec:544`
- uses_section: `sec:545`

---

### Definition 551A (p.460)
*Section 55, Subsection 551*

```
Definition 551A A general linear method (A, U, B, V ) is ‘inherently Runge–
Kutta stable’ if V is of the form (551a) and the two matrices

                  BA − XB         and         BU − XV + V X

are zero except for their first rows, where X is some matrix.

  The significance of this definition is expressed in the following.
```

**References:**
- uses_equation: `eq:551a`

**Referenced by:**
- `thm:553A` (uses_definition)

---

## Theorems (16)

### Theorem 513A (p.409)
*Section 51, Subsection 513*

```
Theorem 513A A general linear method (A, U, B, V ) is convergent only if
it is stable.
```

<details><summary>Proof</summary>

```
Proof. Suppose, on the contrary, that { V n : n = 1, 2, 3, . . . } is unbounded.
This implies that there exists a sequence of vectors w1 , w2 , w3 , . . . such that
 wn = 1, for all n = 1, 2, 3, . . . , and such that the sequence { V n wn : n =
1, 2, 3, . . . } is unbounded. Consider the solution of the initial value problem

                              y  (x) = 0,       y(0) = 0,

using (A, U, B, V ), where n steps are taken with stepsize h = 1/n, so that the
solution is approximated at x = 1. Irrespective of the choice of the vector u
in Definition 512A, the convergence of the method implies that the sequence
of approximations converges to zero. For the approximation carried out with
n steps, use as the starting approximation
                            1          1
                           φ    =                wn .
                             n    maxni=1 V i wi
                                                       −1
This converges to zero, because φ(1/n) = maxni=1 V i wi     . The result,
computed after n steps, will then be
                             1               1
                       V nφ        =                        V n wn ,
                              n        maxni=1     V i wi

with norm                    
                        n 1        V n wn
                       V φ     =                 .                               (513a)
                           n      max n    V i wi   i=1

Because the sequence n → V n wn is unbounded, an infinite set of n values
will have the property that the maximum value of V i wi , for i ≤ n, will
occur with i = n. This means that (513a) has value 1 arbitrarily often, and
hence is not convergent to zero as n → ∞.                                 
```
</details>

**References:**
- uses_definition: `def:512A`
- uses_equation: `eq:513a`

---

### Theorem 514A (p.410)
*Section 51, Subsection 514*

```
Theorem 514A Let (A, U, B, V ) denote a convergent method which is,
moreover, covariant with preconsistency vector u. Then there exists a vector
v ∈ Rr , such that (510c) holds.
```

<details><summary>Proof</summary>

```
Proof. Consider the initial value problem

                              y  (x) = 1,       y(0) = 0,

with constant starting values φ(h) = 0 and x = 1. The sequence of
approximations, when n steps are to be taken with h = 1/n, is given by
                            1
                  y [i] =     B1 + V y [i−1] ,         i = 1, 2, . . . , n.
                            n
This means that the error vector, after the n steps have been completed, is
given by
                        1                            
             y [n] − u =   I + V + V 2 + · · · + V n−1 B1 − u
                        n
                        1                            
                      =    I + V + V 2 + · · · + V n−1 (B1 − u).
                        n
Because V has bounded powers, it can be written in the form

                               V = S −1                    S,
                                             0   W

where I is r× r for r ≤ r and W is power-bounded and is such that 1 ∈ σ(W ).
This means that

          y [n] − u = S −1                    −1
                                                                      S(B1 − u),
                                    n (I − W ) (I − W )
                               0

whose limit as n → ∞ is
                           S −1              S(B1 − u).
                                   0   0

If y [n] − u is to converge to 0 as n → ∞, then S(B1 − u) has only zero in its
first r components. Write this vector in the form
                                            0
                      S(B1 − u) =
                                        (I − W )
                                                v
                                                          !
                                   =   I−                     Sv
                                               0   W

                                   = S(I − V )v,
where
                                               0
                                  v = S −1         .
                                              v
Thus B1 + V v = u + v.                                                           
```
</details>

**References:**
- uses_equation: `eq:510c`

---

### Theorem 515D (p.417)
*Section 51, Subsection 515*

```
Theorem 515D A stable and consistent general linear method is convergent.
```

---

### Theorem 520B (p.418)
*Section 51, Subsection 520*

```
Theorem 520B Let M (z) denote the stability matrix for a general linear
method. Then, for a linear differential equation (520a), (520b) holds with
z = hq.
```

<details><summary>Proof</summary>

```
Proof. For the special problem defined by f (y) = qy, the vector of stage
derivatives F is related to the vector of stage values Y by F = qY . Hence,
(500c) reduces to the form

                          Y             A    U         zY
                                  =                            .
                         y [n]          B    V       y [n−1]

It follows that Y = (I − zA)−1 U y [n−1] , and that

                     y [n] = zBY + V y [n−1] = M (z)y [n−1] .                   

  If the method is stable, in the sense of Section 51, then M (0) = V will be
power-bounded. The idea now is to extend this to values of z in the complex
plane where M (z) has bounded powers.
  Just as for Runge–Kutta and linear multistep methods, associated with
each method is a stability region. This, in turn, is related to the characteristic
polynomial of M (z).
```
</details>

**References:**
- uses_equation: `eq:520a`
- uses_equation: `eq:520b`
- uses_equation: `eq:500c`
- uses_section: `sec:51`

---

### Theorem 520D (p.419)
*Section 51, Subsection 520*

```
Theorem 520D The instability region for (A, U, B, V ) is a subset of the set
of points z, such that Φ(w, z) = 0, where |w| ≥ 1. The instability region is a
superset of the points defined by Φ(w, z) = 0, where |w| > 1.
   The unanswered question in this result is: ‘Which points on the boundary
of the stability region are actually members of it?’ This is not always a crucial
question, and we quite often interpret the stability region as the ‘strict stability
region’, consisting of those z for which
                                lim M (z)n = 0.
                               n→∞

This will correspond to the set of z values such that |w| < 1, for any w
satisfying Φ(w, z) = 0.
  In particular, we can define A-stability.
```

---

### Theorem 521B (p.420)
*Section 51, Subsection 521*

```
Theorem 521B For given ν, the maximum possible stability order is given
by
                            
                            k
                       p =   (νj + 1) − 2.                      (521a)
                                        j=0
```

<details><summary>Proof</summary>

```
Proof. If order higher than p given by (521a) is possible, then

          
          k                     
                                νj
                exp((k − j)z)         αjl z l = Cp+2 z p+2 + Cp+3 z p+3 + · · · ,
          j=0                   l=0

where the right-hand side is convergent for any z. Differentiate νk + 1 times
and multiply the result by exp(−z). We now have a stability function with
complexity [ν0 , ν1 , . . . , νk−1 ], where the w-degree can be reduced even further
if νk−1 = −1. Furthermore, the new approximation also has a stability order
contrary to the bound we are trying to prove. Thus, by an induction argument

we reduce to the case k = 0, and it remains to prove that there does not exist
a non-zero polynomial P of degree ν0 such that

                                P (z) = O(z ν0 +1 ).

To show that an approximation with stability order p given by (521a) exists, it
is possible to reverse the non-existence argument and to construct the required
stability function recursively, but we use a different approach.
   Consider the rational function


                                         k
                             φ(t) =          (t + j)−νj −1 ,                (521b)
                                         j=0

with partial fraction expansion which can be written in the form

                                       
                                       k νj
                                                    l!αjl
                           φ(t) =                           .
                                       j=0 l=0
                                                 (j + t)l+1

Calculate the integral             5
                              1
                                         φ(t) expp(tz)dt,                  (521c)
                             2πi     C

where
                                                 
                                                 
                                                 p
                                                   zj
                                expp(z) =
                                                 j=0
                                                       j!

is the polynomial of degree p approximating the exponential function to within
O(z p+1 ) and C is a circular counter-clockwise contour, centred at 0 and with
radius R > k. Using the partial fraction form of φ, (521c) is found to be

                           
                           k 
                             νj
                                       αjl z l expp−l (−zj),               (521d)
                           j=0 l=0


but using (521b), the integral can be bounded in terms of R−1 for large R, and
is therefore zero. Use the fact that z l expp−l (−zj) = z l exp(−zj) + O(z p+1 )
and the result follows.                                                        

  Because of the maximal order properties of these approximations, they will
be known as ‘generalized Padé approximations’. Some examples are given in
Table 521(I). In each case, Φ(w, z) is scaled so that the coefficient of wk z 0 is 1.
Some of these functions correspond to A-stable methods, and this is indicated
in the table. The entry for ν = [1, 0, 1] is reducible, in the sense that Φ(w, z)
factorizes into the approximation for [1, 1] multiplied by w − 1; the order 3
suggested for this method is, of course, an illusion.

            Table 521(I)            Some generalized Padé approximations

        ν      p                            Φ(w, z)                        Remarks
     [1, 0, 0] 2                     (1 − 23 z)w2 − 43 w + 13               A-stable
     [1, 0, 1] 3                (1 − 12 z)w2 − 2w + 1 + 12 z                A-stable
     [1, 1, 0] 3             (1 − 25 z)w2 − ( 45 + 45 z)w − 15
     [2, 0, 0] 3             (1 − 67 z + 27 z 2 )w2 − 87 w + 17             A-stable
     [2, 0, 1] 4        (1 − 11
                              8
                                       z )w2 − 16
                                     2 2
                                z + 11                 5    2
                                               11 w + 11 + 11 z             A-stable

                            17 z + 17 z )w − ( 17 + 17 z)w − 17
                       (1 − 10      2 2   2    16    8        1
     [2, 1, 0] 4                                                            A-stable
     [2, 0, 2] 5       (1 − 58 z + 18 z 2 )w2 − 2w + 1 + 58 z + 18 z 2      see text
     [2, 1, 2] 6    (1 − 15
                          7
                                   z )w2 − 16
                                 1 2
                            z + 15         15 zw − 1 − 15 z − 15 z
                                                        7      1 2


     [3, 0, 0] 4        (1 − 14
                             15 z + 5 z − 45 z )w − 15 w + 15
                                    2 2    4 3   2  16      1
                                                                            A-stable

                         31 z + 31 z − 31 z + 93 z )w − 31 w + 31
                    (1 − 30     14 2    4 3    2 4   2  32      1
     [4, 0, 0] 5



  The approximation based on ν = [2, 0, 2] is especially interesting. According
to the result formerly known as the Daniel–Moore conjecture (Daniel and
Moore, 1970), it cannot correspond to an A-stable method and also have order
p = 5, because it does not satisfy the necessary condition p ≤ 2s. However,
the solutions to the equation Φ(w, z) = 0 for z = iy satisfy
                                &                &
                                & 8 ± iy 9 + y 2 &2
                                &                &
                          |w| = &
                                2
                                                 & = 1.
                                & 8 − y 2 − 5iy &

By the maximum modulus principle, the bound |w| ≤ 1 holds in the left half-
plane and the only point in the closed left half-plane where the two w roots
have equal values on the unit circle is when z = 0. For Obreshkov methods we
have to regard this as representing instability in the sense of Dahlquist. On
the other hand, general linear methods with this stability function exist with
V = I and therefore convergent methods are definitely possible. A possible
method satisfying this requirement is
                                                            
                                     5        107
                                    16         48      1 0
                                                          
                               − 1712
                                    21          5
                                                       0 1 
                                              16          .
                                                          
                            
                                   775
                                   856       − 99
                                                8      1 0 
                                − 91592
                                   459        295
                                              856      0 1

Although Φ(exp(z), z) = O(z 6 ), the order is only 4 because the solution to
Φ(w, z) = 0 which is ‘principal’ in the sense that it is a good approximation
to exp(z), is
                          
                  1 + 38 z 1 − 19 z 2             1 5
              w=                      = exp(z) −     z + O(z 6 ).
                    1 − 8z + 8z
                         5    1 2                270

  In Butcher and Chipman (1992), the search for possible ν corresponding
to A-stable methods was focused on the cases 2ν0 − p ∈ {0, 1, 2}. For k = 1
(the one-step case), this is necessary and sufficient for A-stability. It seems to
be the case that, even for k > 1, those methods for which 2ν0 − p > 2 cannot
be A-stable. This proposition has become known as the ‘Butcher–Chipman
conjecture’. A partial proof was given in Butcher (2002), restricted to the
cases 2ν0 − p = 3, 4, 7, 8, 11, 12, . . . , and a complete proof is given in Butcher
(2008). An outline of the argument will be given in Subsection 522.
```
</details>

**References:**
- uses_equation: `eq:521a`
- uses_equation: `eq:521b`
- uses_equation: `eq:521c`
- uses_equation: `eq:521d`
- uses_section: `sec:522`

---

### Theorem 523A (p.427)
*Section 51, Subsection 523*

```
Theorem 523A Let Y denote the vector of stage values, F the vector of
stage derivatives and y [n−1] and y [n] the input and output respectively from
a single step of a general linear method (A, U, B, V ). Assume that M is a
positive semi-definite (s + r) × (s + r) matrix, where

                               DA + A D − B GB                DU − B GV
                    M=                                                       ,            (523b)
                                 U D − V GB                   G − V GV
with G a positive semi-definite r × r matrix and D a positive semi-definite
diagonal s × s matrix. Then
                  y [n] 2G = y [n−1] 2G + 2hF, Y D − hF ⊕ y [n−1] 2M .
```

<details><summary>Proof</summary>

```
Proof. The result is equivalent to the identity

                   0     0   B            #        $  D #            $  A          #      $
           M=              −             G B      V +    A          U +             D    0 .         
                   0     G   V                        0                 U
We are now in a position to extend the algebraic stability concept to the
general linear case.
```
</details>

**References:**
- uses_equation: `eq:523b`

---

### Theorem 523B (p.428)
*Section 51, Subsection 523*

```
Theorem 523B If M given by (523b) is positive semi-definite, then
                                         y [n] 2G ≤ y [n−1] 2G .


We consider the possibility of analysing the possible non-linear stability of
linear multistep methods without using one-leg methods. First note that a
linear k-step method, written as a general linear method with r = 2k inputs,
is reducible to a method with only k inputs. For the standard k-step method
written in the form (400b), we interpret hf (xn−i , yn−i ), i = 1, 2, . . . , k, as
having already been evaluated from the corresponding yn−i . Define the input
vector y [n−1] by

       [n−1]
                   
                   k
                                                                   
      yi       =            αj yn−j+i−1 + βj hf (xn−j+i , yn−j+i−1 ) ,       i = 1, 2, . . . , k,
                   j=i

so that the single stage Y = yn satisfies
                                                               [n−1]
                                     Y = hβ0 f (xn , Y ) + y1
and the output vector can be found from
                         [n]         [n−1]      [n]
                       yi      = αi y1       + yi+1 + (β0 αi + βi )hf (xn , Y ),
                            [n]
where the term yi+1 is omitted when i = k. The reduced method has the
defining matrices
                                                          
                         β0          1   0 0 ··· 0 0
                  β α +β                1 0 ··· 0 0 
                      0 1    1     α1                     
                                                          
                  β0 α2 + β2       α    0  1  · · · 0  0  
                                      2                   
       A U        β α +β           α          · · ·       
               =      0 3    3        3 0  0        0  0  ,  (524a)
      B V                .          .   .   .       .   . 
                         ..         ..  .. ..       .. .. 
                                                          
                                                          
                  β0 αk−1 + βk−1 αk−1 0 0 · · · 0 1 
                                   β0 αk + βk          αk    0 0 ···       0 0
and was shown in Butcher and Hill (2006) to be algebraically stable if it is
A-stable.
```

**References:**
- uses_equation: `eq:523b`
- uses_equation: `eq:400b`
- uses_equation: `eq:524a`

---

### Theorem 532A (p.435)
*Section 51, Subsection 532*

```
Theorem 532A Let M = (A, U, B, V ) denote a general linear method and
let ξ denote the algebraic representation of a starting method S. Assume that
(532e) and (532f) hold in G/Hp . Denote

                         = Eξ − BηD − V ξ,          in G.

Then the Taylor expansion of S(y(x0 + h)) − M (S(y(x0 ))) is
                                   (t) r(t)
                                        h F (t)(y(x0 )).                 (532g)
                                   σ(t)
                          r(t)>p
```

<details><summary>Proof</summary>

```
Proof. We consider a single step from initial data given at x0 and consider the
Taylor expansion of various expressions about x0 . The input approximation,
computed by S, has Taylor series represented by ξ. Suppose the Taylor
expansions for the stage values are represented by η so that the stage
derivatives will be represented by ηD and these will be related by (532e). The
Taylor expansion for the output approximations is represented by BηD + V ξ,
and this will agree with the Taylor expansion of S(y(x0 + h)) up to hp terms
if (532f) holds. The difference from the target value of S(y(x0 + h)) is given
by (532g).                                                                   
```
</details>

**References:**
- uses_equation: `eq:532e`
- uses_equation: `eq:532f`
- uses_equation: `eq:532g`

---

### Theorem 534A (p.437)
*Section 51, Subsection 534*

```
Theorem 534A The following method has order 4 and stage order 2:
                                    √                                           √   
                                  3+ 3
                                   √6
                                                   0√             1    − 3+23√ 3
                                − 33      − 3+6 3                          3+2 3    
                A    U                                           1                  
                          =                                                  3
                                                                                     .   (534a)
                B    V             1
                                    2
                                                 1
                                                  2               1          0       
                                    1
                                    2          − 12               0         −1

Before verifying this result we need to specify the nature of the starting
method S and the values of the stage abscissae, c1 and c2 . From an initial
point (x0 , y0 ), the starting value is given by

          [0]
         y1 = y0 ,
                √                √                                    √
                                                      3 4 ∂f (3)
         y2 = 123 h2 y  (x0 ) − 108
                                    3 4 (4)
                                      h y (x0 ) + 9+5
          [0]
                                                   216 h ∂y y (x0 ),

                                 '1        √                  √ (
                                                   2 − 6
                                       1           1   1
and the abscissa vector is c =     2 + 6       3               3 .
                                                            [0]       [0]
```

<details><summary>Proof</summary>

```
Proof. Write ξ1 , ξ2 as the representations of y1 , y2 and η1 , η2 to represent
the stages. The stages have to be found recursively and only the converged
values are given in Table 534(I), which shows the sequence of quantities
occurring in the calculation. The values given for ξi are identical to those
for Eξi , i = 1, 2, verifying that the order is 4. Furthermore ηi (t) = E (ci ) (t),
i = 1, 2, for r(t) ≤ 2, showing stage order 2.                                    


             Table 534(I)     Calculations to verify order p = 4 for (534a)

       i     0    1      2      3       4       5         6        7          8

       ti    ∅
       ξ1    1    0      0      0       0       0         0        0          0
                         √                      √         √         √          √
       ξ2    0    0      12
                           3
                               0         0     − 183   − 363     3+ 3
                                                                  36
                                                                           3+ 3
                                                                             72
                    √      √      √        √       √        √       √          √
                 3+ 3   2+ 3 9+5 3    9+5 3 11+6 3    11+6 3     2+ 3      2+ 3
      η1     1     6     12    36       72      36       72       36         72
                           √     √        √        √        √        √          √
                        3+ 3 2+ 3      2+ 3 11+6 3    11+6 3    9+5 3      9+5 3
      η1 D   0    1       6     6       12      36       72       36         72
                   √      √       √        √       √        √        √          √
      η2     1   3− 3
                   6         −
                        2− 3 3+5 3
                         12    36            −
                                      3+5 3 7+6 3
                                        72      36   − 7+6 3
                                                         72   − 4+3 3
                                                                  36     − 4+3
                                                                             72
                                                                                  3
                          √     √        √        √        √         √          √
      η2 D   0    1     3− 3 2− 3
                          6     6
                                       2− 3 9−5 3
                                        12      36
                                                       9−5 3
                                                         72   − 3+5 3
                                                                  36     − 3+5
                                                                             72
                                                                                  3


       ξ1   1    1       1
                          2
                                1
                                3
                                         1
                                         6
                                                 1
                                                 4
                                                          1
                                                          8
                                                                   1
                                                                  12
                                                                              1
                                                                             24
                         √     √        √       √        √           √          √
       ξ2   0    0      12
                           3
                                6
                                 3
                                        12
                                          3    7 3
                                                36
                                                        7 3
                                                         72
                                                                3+4 3
                                                                  36
                                                                           3+4 3
                                                                             72
```
</details>

**References:**
- uses_equation: `eq:534a`

**Referenced by:**
- `def:525A` (uses_theorem)

---

### Theorem 535A (p.439)
*Section 51, Subsection 535*

```
Theorem 535A Let (A, U, B, V ) denote a consistent general linear method
such that u = e1 and such that

                                        ],                 1 v
                          U = [1       U          V =                     ,
                                                            0 V

where 1 ∈ σ(V ). Then there exists a unique solution to (535a) and (535b) for
which ξ1 = 1.
```

<details><summary>Proof</summary>

```
Proof. By carrying out a further transformation if necessary, we may assume
without loss of generality that V is lower triangular. The conditions satisfied
by ξi (t) (i = 2, 3, . . . , r), ηi (t) (i = 1, 2, . . . , s) and θ(t) can now be written in
the form
                                    
                                    s                     
                                                          i−1
             (1 − Vi,i )ξi (t) =         bij (ηD)(t) +         Vi−1,j−1 ξj (t),
                                    j=1                   j=2

                                    
                                    s                               
                                                                    r
                        ηi (t) =          aij (ηD)(t) + 1(t) +            i,j−1 ξj (t),
                                                                          U
                                    j=1                             j=2

                                    
                                    s                               
                                                                    r
                          θ(t) =          b1j (ηD)(t) + 1(t) +            vj−1 ξj (t).
                                    j=1                             j=2

In each of these equations, the right-hand sides involve only trees with order
lower than r(t) or terms with order r(t) which have already been evaluated.
Hence, the result follows by induction on r(t).                             

   The extension of the concept of underlying one-step method to general
linear methods was introduced in Stoffer (1993).

   Although the underlying one-step method is an abstract structure, it has
practical consequences. For a method in which ρ(V ) < 1, the performance
of a large number of steps, using constant stepsize, forces the local errors
to conform to Theorem 535A. When the stepsize needs to be altered, in
accordance with the behaviour of the computed solution, it is desirable to
commence the step following the change, with input approximations consistent
with what the method would have expected if the new stepsize had been
used for many preceding steps. Although this cannot be done precisely, it
is possible for some of the most dominant terms in the error expansion to
be adjusted in accordance with this requirement. With this adjustment in
place, it becomes possible to make use of information from the input vectors,
as well as information computed within the step, in the estimation of local
truncation errors. It also becomes possible to obtain reliable information that
can be used to assess the relative advantages of continuing the integration
with an existing method or of moving onto a higher order method. These
ideas have already been used to good effect in Butcher and Jackiewicz (2003)
and further developments are the subject of ongoing investigations.
```
</details>

**References:**
- uses_equation: `eq:535a`
- uses_equation: `eq:535b`

---

### Theorem 541A (p.443)
*Section 54, Subsection 541*

```
Theorem 541A A method

                                             A     U
                                                         ,
                                             B     V

has order and stage order p if and only if there exists a function

                                          φ : C → Cr ,

analytic in a neighbourhood of 0, such that

                     exp(cz) = zA exp(cz) + U φ(z) + O(z p+1 ),                                (541a)
                                                                             p+1
                 exp(z)φ(z) = zB exp(cz) + V φ(z) + O(z                            ),          (541b)

where exp(cz) denotes the vector in Cs for which component i is equal to
exp(ci z).
```

<details><summary>Proof</summary>

```
Proof. Assume that (541a) and (541b) are satisfied and that the components
of φ(z) have Taylor series
                                          
                                          p
                               φi (z) =         αij z j + O(z p+1 ).
                                          j=0

Furthermore, suppose starting method i is chosen to give the output
                               
                               p
                                     αij hj y (j) (x0 ) + O(hp+1 ),
                               j=0

where y denotes the exact solution agreeing with a given initial value at x0 .
Using this starting method, consider the value of
                         
                         s                             
                                                       r           
                                                                   p
      y(x0 + hck ) − h         aki y  (x0 + hci ) −         Uki         αij hj y (j) (x0 ).   (541c)
                         i=1                           i=1         j=0

If this is O(hp+1 ) then it will follow that Yk − y(x0 + hck ) = O(hp+1 ). Expand
(541c) about x0 , and it is seen that the coefficient of hj y (j) (x0 ) is

                     1 j                             
                              s                        r
                                        1
                        ck −     aki          cij−1 −     Uki αij .
                     j!      i=1
                                     (j − 1)!         i=1

However, this is exactly the same as the coefficient of z j in the Taylor
expansion of the difference of the two sides of (541a). Given that the order

of the stages is p, and therefore that hf (Yi ) = hy  (x0 + hci ) + O(hp+1 ), we
can carry out a similar analysis of the condition for the kth output vector to
equal
                       p
                          αkj hj y [j] (x0 + h) + O(hp+1 ).               (541d)
                        j=0

Carry out a Taylor expansion about x0 and we find that (541d) can be written
as
                   p p
                                 1
                          αkj          hi y (i) (x0 ) + O(hp+1 ).    (541e)
                  j=0 i=j
                              (i − j)!

The coefficient of hi in (541e) is identical to the coefficient of z i in exp(z)φk (z).
Hence, combining this with the terms
                         
                         s
                                         1             r
                                bki            cij−1 +     Vki αij ,
                         i=1
                                      (j − 1)!         i=1

we find (541b).
   To prove necessity, use the definition of order given by (532e) and (532f)
and evaluate the two sides of each of these equations for the sequence of trees
t0 = ∅, t1 = τ , t2 = [t1 ], . . . , tp = [tp−1 ]. Use the values of αij given by

                                         αij = ξi (tj ),

so that
                                               
                                               j
                                                 1
                               (Eξi )(tj ) =              ξi (tj−k ),
                                                     k!
                                               k=0
                                                "p
which is the coefficient of z j in exp(z)              k=0 αik z
                                                                 k
                                                                     . We also note that

                               1 j                                1
                  ηi (tj ) =     c ,         (ηi D)(tj ) =             cj−1 ,
                               j! i                            (j − 1)! i

which are, respectively, the z j coefficients in exp(ci z) and in z exp(c
                                                                    " i z). Write
φ(z) as the vector-valued function with ith component equal to pk=0 αik z k ,
and we verify that coefficients of all powers of z up to z p agree in the two
sides of (541a) and (541b).                                                    
```
</details>

**References:**
- uses_equation: `eq:541a`
- uses_equation: `eq:541b`
- uses_equation: `eq:541c`
- uses_equation: `eq:541d`
- uses_equation: `eq:541e`
- uses_equation: `eq:532e`
- uses_equation: `eq:532f`

---

### Theorem 550A (p.457)
*Section 55, Subsection 550*

```
Theorem 550A The coefficients in the characteristic polynomial of X,
det(wI − X) = wn + γ1 wn−1 + γ2 wn−2 + · · · + γn , are given by

      1 + γ1 z + γ2 z 2 + · · · + γn z n = det(I − zX) = α(z)β(z) + O(z n+1 ).
```

<details><summary>Proof</summary>

```
Proof. We assume that the eigenvalues of X are distinct and non-zero. There
is no loss of generality in this assumption because, for given values of the
α coefficients, the coefficients in the characteristic polynomial are continuous
functions of the β coefficients; furthermore, choices of the β coefficients which
lead to distinct non-zero eigenvalues form a dense set.
   Let λ denote an eigenvalue of X, and let

         vk = λk + β1 λk−1 + β2 λk−2 + · · · + βk ,      k = 0, 1, 2, . . . , n.

By comparing components numbered n, n − 1, . . . , 2 of Xv and λv, where

                          V = [ vn−1    vn−2    ···   1] ,                         (550b)

we see that v is the eigenvector corresponding to λ. Now compare the first
components of λv and Xv and it is found that

                          λvn + α1 vn−1 + · · · + αn = 0

and contains all the terms with non-negative exponents in the product

                         vn (1 + α1 λ−1 + · · · + αn λ−n ).

Replace λ by z −1 and the result follows.                                              

  Write φ(z) for the vector (550b) with λ replaced by z. We now note that

                                             n
                         zφ(z) − Xφ(z) =         (z − λi )e1 ,                      (550c)
                                             i=1

because the expression vanishes identically except for the first component
which is a monic polynomial of degree n which vanishes when z is an
eigenvalue.
   We are especially interested in choices of α and β such that X has a single
n-fold eigenvalue, so that

                        α(z)β(z) = (1 − λz)n + O(z n+1 )                            (550d)

and so that the right-hand side of (550c) becomes (z − λ)n e1 . In this case it is
possible to write down the similarity that transforms X to Jordan canonical
form.
```
</details>

**References:**
- uses_equation: `eq:550b`
- uses_equation: `eq:550c`
- uses_equation: `eq:550d`

---

### Theorem 550B (p.458)
*Section 55, Subsection 550*

```
Theorem 550B Let the doubly companion matrix X be chosen so that
(550d) holds. Also let φ(z) denote the vector given by (550b) with λ replaced
by z, and let S the matrix given by
             ' 1                                       1 
                                                                    (
       Ψ = (n−1)!                 1
                    φ(n−1) (λ) (n−2)! φ(n−2) (λ) · · · 1! φ (λ) φ(λ) .

Then                                                          
                              λ         0    0 ···     0    0
                             1              0 ···          0 
                                       λ              0       
                                                              
                     Ψ XΨ = 
                      −1
                            
                              0         1    λ ···     0    0 .
                                                               
                             ..        ..   ..        ..   .. 
                             .          .    .         .    . 
                              0         0    0 ···     1    λ
```

<details><summary>Proof</summary>

```
Proof. From the special case of (550c), we have

                          Xφ(z) = zφ(z) − (z − λ)n e1 .                             (550e)

Differentiate k times, divide by k! and set z = λ, for k = 1, 2, . . . , n − 1. The
result is
       1 (k)        1              1
   X      φ (λ) = λI φ(k) (λ) +          φ(k−1) (λ),             k = 1, 2, . . . , n − 1.
       k!           k!          (k − 1)!
                        1        1                 1
Hence the vectors φ(λ), 1! φ (λ), 2! φ (λ), . . . , (n−1)! φ(n−1) (λ) form a sequence
of eigenvector and generalized eigenvectors, and the result follows.               

  The inverse of Ψ is easy to evaluate by interchanging the roles of rows and
columns of X. We present the following result without further proof.
```
</details>

**References:**
- uses_equation: `eq:550d`
- uses_equation: `eq:550b`
- uses_equation: `eq:550c`
- uses_equation: `eq:550e`

---

### Theorem 551B (p.460)
*Section 55, Subsection 551*

```
Theorem 551B Let (A, U, B, V ) denote an inherently RK stable general
linear method. Then the stability matrix

                        M (z) = V + zB(I − zA)−1 U

has only a single non-zero eigenvalue.
```

<details><summary>Proof</summary>

```
Proof. Calculate the matrix

                          (I − zX)M (z)(I − zX)−1 ,

which has the same eigenvalues as M (z). We use the notation ≡ to denote
equality of two matrices, except for the first rows. Because BA ≡ XB and
BU ≡ XV − V X, it follows that

                      (I − zX)B ≡ B(I − zA),
                      (I − zX)V ≡ V (I − zX) − zBU,

so that
                        (I − zX)M (z) ≡ V (I − zX).
Hence (I − zX)M (z)(I − zX)−1 is identical to V , except for the first row.
Thus the eigenvalues of this matrix are its (1, 1) element together with the p
zero eigenvalues of V̇ .                                                    

  Since we are adopting, as standard r = p + 1 and a stage order q = p, it is
possible to insist that the vector-valued function of z, representing the input
approximations, comprises a full basis for polynomials of degree p. Thus, we
will introduce the function Z given by
                                      
                                    1
                                   z 
                                      
                                   2 
                                  
                                Z= z  ,                               (551b)
                                       
                                   .. 
                                   . 
                                         zp

which represents the input vector
                                                   
                                        y(xn−1 )
                                     hy  (x ) 
                                               n−1 
                                     2           
                          y [n−1] =   h y (xn−1 )  .                   (551c)
                                                   
                                            ..     
                                             .     
                                       p (p)
                                      h y (xn−1 )

This is identical, except for a simple rescaling by factorials, to the Nordsieck
vector representation of input and output approximations, and it will be
convenient to adopt this as standard.
  Assuming that this standard choice is adopted, the order conditions are

                    exp(cz) = zA exp(cz) + U Z + O(z p+1 ),              (551d)
                                                         p+1
                   exp(z)Z = zB exp(cz) + V Z + O(z            ).        (551e)

This result, and generalizations of it, make it possible to derive stiff methods
of quite high orders. Furthermore, Wright (2003) has shown how it is possible
to derive explicit methods suitable for non-stiff problems which satisfy the
same requirements. Following some more details of the derivation of these
methods, some example methods will be given.
```
</details>

**References:**
- uses_equation: `eq:551b`
- uses_equation: `eq:551c`
- uses_equation: `eq:551d`
- uses_equation: `eq:551e`

---

### Theorem 553A (p.463)
*Section 55, Subsection 553*

```
Theorem 553A If a general linear method with p = q = r − 1 = s − 1
has the property of IRK stability then the matrix X in Definition 551A is a
(p + 1) × (p + 1) doubly companion matrix.
```

<details><summary>Proof</summary>

```
Proof. Substitute (551d) into (551e) and compare (551d) with zX multiplied
on the left. We find

             exp(z)Z = z 2 BA exp(cz) + zBU Z + V Z + O(z p+1 ),                  (553a)
                              2                              p+1
         z exp(z)XZ = z XB exp(cz) + zXV Z + O(z                   ).             (553b)

Because BA ≡ XB and BU ≡ XV − V X, the difference of (553a) and (553b)
implies that
                      zXZ ≡ Z + O(z p+1 ).

Because zJZ ≡ Z + O(z p+1 ), it now follows that

                                   (X − J)Z ≡ O(z p ),

which implies that X − J is zero except for the first row and last column. 

  We will assume without loss of generality that βp+1 = 0.

  By choosing the first row of X so that σ(X) = σ(A), we can assume that
the relation BA = XB applies also to the first row. We can now rewrite the
defining equations in Definition 551A as
                           BA = XB,                                       (553c)
                           BU = XV − V X + e1 ξ ,                         (553d)

where ξ = [ ξ1 ξ2 · · · ξp+1 ] is a specific vector. We will also write
ξ(z) = ξ1 z + ξ2 z 2 + · · · + ξp+1 z p+1 . The transformed stability function in
```
</details>

**References:**
- uses_definition: `def:551A`
- uses_equation: `eq:551d`
- uses_equation: `eq:551e`
- uses_equation: `eq:553a`
- uses_equation: `eq:553b`
- uses_equation: `eq:553c`
- uses_equation: `eq:553d`

---

## Lemmas (3)

### Lemma 515A (p.412)
*Section 51, Subsection 515*

```
Lemma 515A Assume that h ≤ h0 , chosen so that h0 L A ∞ < 1. Define
as the vector in Rs satisfying

                        
                        s                                                   
                                                                            s
                              (δij − h0 L|aij |) j = 12 c2i +                     |aij cj |.
                        j=1                                                 j=1


                 = ui y(xn−1 ) + vi hy  (xn−1 ), yi = ui y(xn ) + vi hy  (xn ), for i =
      [n−1]                                                    [n]
Let yi
1, 2, . . . , r, and Yi = y(xn−1 + hci ), for i = 1, 2, . . . , s, where c = A1 + U v.
Also let Yi denote the value of Yi that would be computed exactly using y[n−1]
as input vector y [n−1] . Assume the function f satisfies a Lipschitz condition
with constant L and that the exact solution to the initial value problem satisfies
 y(x) ≤ M , y  (x) ≤ LM . Then
                                      
                                  [n−1] 
           s               r
  Yi − h          
             aij f (Yj ) −   Uij yj     
                                        
              j=1                  j=1
                                      
                                       s          
                    ≤ h2 L2 M 12 c2i +   |aij cj | ,                                             (515a)
                                               j=1
         
          s                
                           r             
   [n]                            [n−1] 
   yi − h
          bij f (Yj ) −   Vij yj     
               j=1                   j=1
                                                
                                                 s          
                    ≤ h2 L2 M 12 |ui | + |vi | +   |bij cj | ,                                   (515b)
                                                         j=1
         
          s                
                           r             
   [n]                            [n−1] 
   yi − h
          bij f (Yj ) −   Vij yj     
               j=1                   j=1
                                                
                                                 s                  
                                                                    s         
                    ≤ h2 L2 M 12 |ui | + |vi | +   |bij cj | + h0 L   |bij | j .                 (515c)
                                                         j=1                           j=1
```

<details><summary>Proof</summary>

```
Proof. We first note that
                                               ci                  
                                                                    
                                              
                y(xn−1 + hci ) − y(xn−1 ) = h       y (xn−1 + hξ)dξ 
                                                      
                                                                     
                                               c0i              
                                                                
                                          ≤h        y (xn−1 + hξ)dξ
                                                                     0
                                                        ≤ |ci |hLM.

We now have
                        
                        s                      
                                               r
              Yi − h         aij f (Yj ) −
                                                           [n−1]
                                                     Uij yj             = T1 + T2 + T3 + T4 ,
                        j=1                    j=1

where
                                           ci
        T1 = Yi − y(xn−1 ) − h                  f (y(xn−1 + hξ))dξ,
                                            0
                                                    
                                                    r                        
                                                                             s
        T2 = y(xn−1 ) + ci hy  (xn−1 ) −                                          aij hy  (xn−1 ),
                                                                 [n−1]
                                                          Uij yj        −
                                                    j=1                      j=1
                ci                               
        T3 = h       f (y(xn−1 + hξ)) − y  (xn−1 ) dξ,
                  0
                   
                   s                                           
        T4 = −h             aij f (y(xn−1 + hcj )) − y  (xn−1 ) .
                   j=1

Simplify and estimate these terms, and we find
                                            ci
        T1 = y(xn−1 + hci ) − y(xn−1 ) − h      y  (xn−1 + hξ)dξ = 0,
                                                             0
         T2 = y(xn−1 ) + ci hy  (xn−1 )
                  r                                     
                                                           s
                −      Uij uj y(xn−1 ) + hvj y  (xn−1 ) −   aij hy  (xn−1 )
                       j=1                                                    j=1

             = 0, because U u = 1 and U v + A1 = c,
                 ci                                   
                                                           
        T3      
             = h        f (y(xn−1 + hξ)) − f (y(xn−1 )) dξ 
                                                            
                 c0i                                
                                                     
             ≤h       f (y(xn−1 + hξ)) − f (y(xn−1 ))dξ
                   ci 
                  0
                                                 
                                                
             ≤ hL       y(xn−1 + hξ) − y(xn−1 )dξ
                    0
                         ci
             ≤h L M
                2 2
                             ξdξ
                               0

             = 12 h2 L2 M c2i ,
              s                                     
                                                       
        T4 = h   aij f (y(xn−1 + hcj )) − f (y(xn−1 )) 
                      j=1
                  
                  s
             ≤h         |aij | · f (y(xn−1 + hcj )) − f (y(xn−1 ))
                  j=1
                   s
             ≤ hL           |aij | · y(xn−1 + hcj ) − y(xn−1 )
                      j=1
                             
                             s
             ≤ h2 L2 M             |aij cj |,
                             j=1

so that, combining these estimates, we arrive at (515a).
  To verify (515b), we write
                             
                             s                       
                                                     r
                                    bij f (Yj ) −
                [n]                                              [n−1]
               yi − h                                     Vij yj       = T1 + T2 + T3 + T4 ,
                             j=1                     j=1

where
                                             1                  
          T1 = ui y(xn−1 + h) − y(xn−1 ) − h     y  (xn−1 + hξ)dξ ,
                                                                         0
                                        
                                         s       
                                                 r       
          T2 = vi hy  (xn−1 + h) + ui −   bij −   Vij vj hy  (xn−1 ),
                                                              j=1            j=1
                              1
                                                              
          T3 = hui                   y (xn−1 + hξ) − y  (xn−1 ) dξ,
                                0
                            
                            s
                                                                      
          T4 = −h                   bij y  (xn−1 + hcj ) − y  (xn−1 ) .
                            j=1
                                                "         "
We check that T1 = 0 and that, because sj=1 bij + rj=1 Vij vj = ui + vi , T2
simplifies to hvi (y  (xn−1 + h) − y  (xn−1 )) "
                                                so that T2 ≤ h2 L2 M |vi |. Similarly,
 T3 ≤ 2 h L M |ui | and T4 ≤ h L M sj=1 |bij cj |. To prove (515c) we first
        1 2 2                           2 2

need to estimate the elements of Y − Y by deducing from (515a) that
               
                  s                                  
                                                         s          
                                          
    Yi − Yi − h   aij f (Yj ) − f (Yj )  ≤ 12 c2i +   |aij cj | h2 L2 M,
                                j=1                                                 j=1

and hence that
                                            Yj − Yj ≤ h2 L2 M j .
Thus,
                       s                       
                                                        
                                                             s
                      h                      
                          bij f (Yj ) − f (Yj )  ≤ h L M h0
                                                     2 3
                                                               |bij | j .
                      
                            j=1                                                    j=1
                      "                           
                                                    
Add this estimate of h sj=1 bij f (Yj ) − f (Yj )  to (515b) to obtain (515c).
                                                                                

  The next step in the investigation is to find a bound on the local truncation
error.
```
</details>

**References:**
- uses_equation: `eq:515a`
- uses_equation: `eq:515b`
- uses_equation: `eq:515c`

**Referenced by:**
- `lem:515B` (uses_lemma)

---

### Lemma 515B (p.414)
*Section 51, Subsection 515*

```
Lemma 515B Under the conditions of Lemma 515A, the exact solution and
the computed solution in a step are related by
                                
                                r                         
         [n]          [n]                   [n−1]    [n−1]      [n]
        yi − yi            =         Vij yj     − yj       + Ki ,                  i = 1, 2, . . . , r,
                                j=1

where                                                
                                   r  [n−1]    [n−1] 
                       K [n] ≤ hα max 
                                       yi    − yi      + βh2 ,
                                               i=1

and α and β are given by
                                                         s
                                              α = L max | i |,
                                                       i=1

where    is given by

              
              s                                      
                                                     s
                    (δij − h0 L|aij |) j =                 |Uij |,           i = 1, 2, . . . , s,
              j=1                                    j=1

and
                     s
                                          
                                           s                  
                                                              s         
           β = L2 M max 21 |ui | + |vi | +   |bij cj | + h0 L   |bij | j ,
                          i=1
                                                         j=1                         j=1

where    is as in Lemma 515A.
```

<details><summary>Proof</summary>

```
Proof. From (515c), and the relation

                          [n]
                                        
                                        s                     
                                                              r
                                                                           [n−1]
                      yi − h                  bij f (Yj ) −         Vij yj         = 0,
                                        j=1                   j=1

we have
                                      
     [n]         
                  r
                                   [n−1] 
    y − y [n] −         [n−1]
                    Vij yj     − yj     
     i    i                             
                      j=1
                  
                  s                                
                                                   
             ≤h           |bij | f (Yj ) − f (Yj )
                    j=1
                                                      
                                                       s                  
                                                                          s          
                          + h2 L2 M 12 |ui | + |vi | +   |bij cj | + h0 L   |bij | j
                                                                    j=1                      j=1
                     
                     s                      
                                            
             ≤ hL           |bij | Yj − Yj 
                     j=1
                                                                                                            (515d)
                                                                 
                                                                  s                          
                                                                                             s              
                                              1
                                              2 |ui | + |vi | +           |bij cj | + h0 L          |bij | j .
                                2   2
                          +h L M
                                                                    j=1                      j=1


Bound ηj = Yj − Yj using the estimate
                                          
                   
                    r
                                       [n−1] 
                                                    
                                                    s
        Yj − Yj −   U    y
                             [n−1]
                                   − y        ≤ hL   |ajk | · Yk − Yk ,
                      jk    k        k      
                     k=1                                                     k=1

which leads to
           
           s                                       
                                                   r                               
                                                                 r  [n−1]    [n−1] 
                 (δjk − h0 L|ajk |)ηk ≤                  |Ujk | max 
                                                                     yk    − yk     
                                                                   k=1
           k=1                                     k=1

and to
                              Yj − Yj ≤ h j max Yk − Yk .
                                              s
                                                         k=1
Substitute this bound into (515d) and we obtain the required result.                             

   To complete the argument that stability and consistency imply convergence,
we estimate the global error in the computation of y(x) by carrying out n steps
from an initial value y(x0 ) using a stepsize equal to h = (x − x0 )/n.
```
</details>

**References:**
- uses_lemma: `lem:515A`
- uses_equation: `eq:515c`
- uses_equation: `eq:515d`

**Referenced by:**
- `lem:515C` (uses_lemma)

---

### Lemma 515C (p.416)
*Section 51, Subsection 515*

```
Lemma 515C Using notations already introduced in this subsection, together
with                [i]    [i] 
                     y1 − y1
                    [i]    [i] 
                    y2 − y2 
           E [i] =             ,     i = 0, 1, 2, . . . , n,
                        ..     
                         .     
                                     [i]     [i]
                                    yr − yr
for the accumulated error in step i, we have the estimate
           
             exp(αC(x − x0 )) E [0] + βh α (exp(αC(x − x0 )) − 1),                      α > 0,
   E [n] ≤
             exp(αC(x − x0 )) E   [0]
                                      + βC(x − x0 )h,                                   α = 0,

where C = supi=0,1,... V i ∞ and the norm of E [n] is defined as the maximum
of the norms of its r subvectors.
```

<details><summary>Proof</summary>

```
Proof. The result of Lemma 515B can be written in the form
                               E [i] = (V ⊗ I)E [i−1] + K [i] ,
from which it follows that
                                                       
                                                       i
                  E   [i]
                            = (V ⊗ I)E
                                i            [0]
                                                   +         (V j−1 ⊗ I)K [i+1−j] ,
                                                       j=1

and hence that
                                                             
                                                             i−1
                             E [i] ≤ C E [0] +                     C K [i−j] .
                                                             j=0

Insert the known bounds on the terms on the right-hand side, and we find
                                           
                                           i−1
                    E [i] ≤ αhC                    E [j] + Ciβh2 + C E [0] .
                                           j=0

This means that E [i] is bounded by ηi defined by

                           
                           i−1
                ηi = αhC         ηj + Ciβh2 + η0 ,     η0 = C E [0] .
                           j=0

To simplify this equation, find the difference of the formulae for ηi and ηi−1
to give the difference equation

                           ηi − ηi−1 = αhCηi−1 + Cβh2

with solution
                                            βh
                   ηi = (1 + hαC)i η0 +        ((1 + hαC)i − 1),
                                            α
or, if α = 0,
                                   ηi = η0 + iCβh2 .
Substitute i = n and we complete the proof.                                

  We summarize the implications of these results:
```
</details>

**References:**
- uses_lemma: `lem:515B`

---

## Corollaries (1)

### Corollary 550C (p.459)
*Section 55, Subsection 550*

```
Corollary 550C If

  χ(λ) = [ 1   λ + α1     λ2 + α1 λ + α2            ···   λn−1 + α1 λn−2 + · · · + αn−1 ],

then

       Ψ−1 = [ χ(λ)     1 
                        1! χ (λ)   ···          1
                                              (n−2)! χ
                                                       (n−2)
                                                             (λ)          1
                                                                        (n−1)! χ
                                                                                 (n−1)
                                                                                       (λ) ] .
```

---
