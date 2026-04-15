# Chapter 1: Differential and Difference Equations

Pages 1-49

## Sections

- **10** Differential Equation Problems
- **11** Differential Equation Theory
- **12** Further Evolutionary Problems
- **13** Difference Equation Problems
- **14** Difference Equation Theory

## Definitions (4)

### Definition 110A (p.43)
*Section 11, Subsection 110*

```
Definition 110A The function f : [a, b] × RN → RN is said to satisfy
a ‘Lipschitz condition in its second variable’ if there exists a constant L,
known as a ‘Lipschitz constant’, such that for any x ∈ [a, b] and Y, Z ∈ RN ,
 f (x, Y ) − f (x, Z) ≤ L Y − Z .
  We need a basic lemma on metric spaces known as the ‘contraction mapping
principle’. We present this without proof.
```

---

### Definition 112A (p.47)
*Section 11, Subsection 112*

```
Definition 112A The function f satisfies a ‘one-sided Lipschitz condition’,
with ‘one-sided Lipschitz constant’ l if for all x ∈ [a, b] and all u, v ∈ RN ,
                        f (x, u) − f (x, v), u − v ≤ l u − v 2 .
It is possible that the function f could have a very large Lipschitz constant
but a moderately sized, or even negative, one-sided Lipschitz constant. The
advantage of this is seen in the following result.
```

---

### Definition 142A (p.67)
*Section 14, Subsection 142*

```
Definition 142A A square matrix A is ‘stable’ if there exists a constant C
such that for all n = 0, 1, 2, . . . , An ≤ C.

     This property is often referred to as ‘power-boundedness’.
```

---

### Definition 142B (p.67)
*Section 14, Subsection 142*

```
Definition 142B A square matrix A is ‘convergent’ if limn→∞ An = 0.
```

---

## Theorems (12)

### Theorem 101A (p.26)
*Section 10, Subsection 101*

```
Theorem 101A The quantities
                     1 2       
                H=      y3 + y42 − (y12 + y22 )−1/2 ,
                     2
                A = y1 y4 − y2 y3
are constant.
```

<details><summary>Proof</summary>

```
Proof. We verify that the values of dH/dx and dA/dx are zero if y satisfies
(101a)–(101d). We have
      dH      dy3        dy4      dy1 2                    dy2 2
         = y3      + y4      + y1     (y + y22 )−3/2 + y2      (y + y22 )−3/2
      dx       dx         dx      dx 1                      dx 1
                  y1 y3            y2 y4            y1 y3            y2 y4
         =− 2                − 2             + 2               + 2
              (y1 + y22 )3/2  (y1 + y22 )3/2    (y1 + y22 )3/2   (y1 + y22 )3/2
          =0
and
                dA      dy4     dy1          dy3   dy2
                   = y1      +       y4 − y2     −      y3
                dx       dx     dx           dx     dx
                            y1 y2                    y2 y1
                   =− 2                + y3 y4 + 2              − y4 y3
                        (y1 + y22 )3/2           (y1 + y22 )3/2
                    = 0.                                                          
   The quantities H and A are the ‘Hamiltonian’ and    ‘angular
                                                               momentum’,
respectively. Note that H = T + V , where T = 12 y32 + y42 is the kinetic
energy and V = −(y12 + y22 )−1/2 is the potential energy.
   A further property of this problem is its invariance under changes of scale
of the variables:
                                    y1 = α−2 y 1 ,
                                    y2 = α−2 y 2 ,
                                    y3 = αy 3 ,
                                    y4 = αy 4 ,
                                     x = α−3 x.
The Hamiltonian and angular momentum get scaled to
                     1 2       
                H=      y + y 24 − (y 21 + y 22 )−1/2 = α−2 H,
                     2 3
                A = y1 y4 − y2 y3                     = αA.

  A second type of transformation is based on a two-dimensional orthogonal
transformation (that is, a rotation or a reflection or a composition of these)
Q, where Q−1 = Q . The time variable x is invariant, and the position and
velocity variables get transformed to
                                                 
                           y1                    y1
                          y        Q 0           
                          2                 y2 
                              =                  .
                          y3        0 Q  y3 
                           y4                    y4
   It is easy to see that A = 0 implies that the trajectory lies entirely in a
subspace defined by cos(θ)y1 = sin(θ)y2 , cos(θ)y3 = sin(θ)y4 for some fixed
angle θ. We move on from this simple case and assume that A = 0. The sign
of H is of crucial importance: if H ≥ 0 then it is possible to obtain arbitrarily
high values of y12 + y22 without y32 + y42 vanishing. We exclude this case for the
present discussion and assume that H < 0. Scale H so that it has a value
− 12 and at the same time A takes on a positive value. This value cannot
exceed 1 because we can easily verify an identity involving the derivative of
r = y12 + y22 . This identity is
                       2
                     dr
                   r       = 2Hr 2 + 2r − A2 = −r 2 + 2r − A2 .             (101e)
                     dx
Since the left-hand side cannot be negative, the quadratic function in r on
the right-hand
     √          side must have real roots. This implies that A ≤ 1. Write
A = 1 − e2 , for e ≥ 0, where we see that e is the eccentricity of an ellipse
on which the orbit lies. The minimum and maximum values of r are found to
be 1 − e and 1 + e, respectively. Rotate axes so that when r = 1 − e, which
we take as the starting point of time, y1 = 1 − e and y2 = 0. At this point we
find that y3 = 0 and y4 = (1 + e)/(1 − e).
  Change to polar coordinates by writing y1 = r cos(θ), y2 = r sin(θ). It is
found that
                            dy1   dr            dθ
                      y3 =      =    cos(θ) − r    sin(θ),
                             dx   dx            dx
                            dy2   dr            dθ
                      y4 =      =    sin(θ) + r    cos(θ),
                             dx   dx            dx
                                √
so that, because y1 y4 − y2 y3 = 1 − e2 , we find that
                                    dθ
                               r2      =   1 − e2 .                        (101f)
                                    dx
From (101e) and (101f) we find a differential equation for the path traced out
by the orbit
                    2
                      dr        1                    
                           =         r 2 e2 − (1 − r)2 ,
                      dθ      1 − e2

and we can verify that this is satisfied by
                              1 − e2
                                     = 1 + e cos(θ).
                                r
If we change back to Cartesian coordinates, we find that all points on the
trajectory lie on the ellipse
                                                y22
                                (y1 + e)2 +          = 1,
                                              1 − e2
with centre (−e, 0), eccentricity e, and major and minor axis lengths 1 and
√
  1 − e2 respectively.
   As we have seen, a great deal is known about this problem. However, much
less is known about the motion of a many-body gravitational system.
   One of the aims of modern numerical analysis is to understand the behaviour
of various geometrical properties. In some cases it is possible to preserve the
value of quantities that are invariant in the exact solution. In other situations,
such as problems where the Hamiltonian is theoretically conserved, it may be
preferable to conserve other properties, such as what is known as ‘symplectic
behaviour’.
   We consider further gravitational problems in Subsection 120.
```
</details>

**References:**
- uses_equation: `eq:101a`
- uses_equation: `eq:101d`
- uses_equation: `eq:101e`
- uses_equation: `eq:101f`
- uses_section: `sec:120`

---

### Theorem 110C (p.44)
*Section 11, Subsection 110*

```
Theorem 110C Consider an initial value problem

                               y  (x) = f (x, y(x)),                       (110a)
                                y(a) = y0 ,                                 (110b)

where f : [a, b] × RN → RN is continuous in its first variable and satisfies a
Lipschitz condition in its second variable. Then there exists a unique solution
to this problem.
```

<details><summary>Proof</summary>

```
Proof. Let M denote the complete metric space of continuous functions
y : [a, b] → RN , such that y(a) = y0 . The metric is defined by

                ρ(y, z) = sup exp(−K(x − a)) y(x) − z(x) ,
                          x∈[a,b]

where K > L. For given y ∈ M , define φ(y) as the solution Y on [a, b] to the
initial value problem

                              Y  (x) = f (x, Y (x)),
                              Y (a) = y0 .

This problem is solvable by integration as
                                       x
                      φ(y)(x) = y0 +       f (s, y(s))ds.
                                           a

This is a contraction because for any two y, z ∈ M , we have
                                          x                                 
                                                                          
   ρ(φ(y), φ(z)) ≤ sup exp(−K(x − a))           f (s, y(s)) − f (s, z(s)) ds
                                                                              
                    x∈[a,b]
                                          x a

                 ≤ sup exp(−K(x − a))           f (s, y(s)) − f (s, z(s)) ds
                    x∈[a,b]                a
                                             x
                 ≤ L sup exp(−K(x − a))            y(s) − z(s) ds
                      x∈[a,b]                 a
                                                      x
                 ≤ Lρ(y, z) sup exp(−K(x − a))           exp(K(s − a))ds
                             x∈[a,b]                    a
                  L
                 ≤ ρ(y, z).
                  K
The unique function y that therefore exists satisfying φ(y) = y, is evidently
the unique solution to the initial value problem given by (110a), (110b). 


  The third requirement for being well-posed, that the solution is not overly
sensitive to the initial condition, can be readily assessed for problems satisfying

a Lipschitz condition. If y and z each satisfy (110a) with y(a) = y0 and
z(a) = z0 , then
                      d
                         y(x) − z(x) ≤ L y(x) − z(x) .
                     dx
Multiply both sides by exp(−Lx) and deduce that
                        d                      
                            exp(−Lx) y(x) − z(x) ≤ 0,
                       dx
implying that
                                                     
                    y(x) − z(x) ≤ y0 − z0 exp L(x − a) .                   (110c)

This bound on the growth of initial perturbations may be too pessimistic in
particular circumstances. Sometimes it can be improved upon by the use of
‘one-sided Lipschitz conditions’. This will be discussed in Subsection 112.
```
</details>

**References:**
- uses_equation: `eq:110a`
- uses_equation: `eq:110b`
- uses_equation: `eq:110c`
- uses_section: `sec:112`

---

### Theorem 111A (p.45)
*Section 11, Subsection 111*

```
Theorem 111A If y is a solution to (111a) and y1 , y2 , . . . , yk are solutions
to (111b), then for any constants α1 , α2 , . . . , αk , the function y given by

                                            
                                            k
                           y(x) = y(x) +         αi yi (x),
                                            i=1

is a solution to (111a).
The way this result is used is to attempt to find the solution which matches
a given initial value, by combining known solutions.
  Many linear problems are naturally formulated in the form of a single high
order differential equation

 Y (m) (x) − C1 (x)Y (m−1) (x) − C2 (x)Y (m−2) (x) − · · · − Cm (x)Y (x) = g(x).
                                                                           (111c)

  By identifying Y (x) = y1 (x), Y  (x) = y2 (x), . . . , Y (m−1) = ym (x), we can
rewrite the system in the form
                                                     
                        y1 (x)               y1 (x)
                   d                     y (x) 
                      y2 (x)             2           
                          ..   = A(x)        ..       + φ(x),
                  dx       .                  .      
                        ym (x)               ym (x)
where the ‘companion matrix’ A(x) and the ‘inhomogeneous term’ φ(x) are
given by
                                                                 
             0       1         0      ···     0                  0
            0       0         1      ···     0              0 
                                                                 
            0       0         0      ···     0              0 
                                                                 
A(x) =      ..      ..        ..             ..  , φ(x) =  ..  .
             .       .         .              .             . 
            0       0         0      ···     1              0 
           Cm (x) Cm−1 (x) Cm−2 (x) · · ·            C1 (x)                 g(x)
When A(x) = A in (111b) is constant, then to each eigenvalue λ of A, with
corresponding eigenvector v, there exists a solution given by
                                 y(x) = exp(λx)v.                            (111d)
When a complete set of eigenvectors does not exist, but corresponding to λ
there is a chain of generalized eigenvectors
      Av1 = λv1 + v,     Av2 = λv2 + v1 ,     ...,    Avk−1 = λvk−1 + vk−2 ,
then there is a chain of additional independent solutions to append to (111d):
  y1 = x exp(λx)v1 ,    y2 = x2 exp(λx)v2 ,    ...,     yk−1 = xk−1 exp(λx)vk−1 .
In the special case in which A is a companion matrix, so that the system is
equivalent to a high order equation in a single variable, as in (111c), with
C1 (x) = C1 , C2 (x) = C2 , . . . , Cm (x) = Cm , each a constant, the characteristic
polynomial of A is
               P (λ) = λm − C1 λm−1 − C2 λm−2 − · · · − Cm = 0.
For this special case, P (λ) is also the minimal polynomial, and repeated
zeros always correspond to incomplete eigenvector spaces and the need
to use generalized eigenvectors. Also, in this special case, the eigenvector
corresponding to λ, together with the generalized eigenvectors if they exist,
are
                                                               
          1                     0                         0
       λ                     1                       0         
                                                               
 v=     λ  2               2λ                       1         , . . . .
           .   , v1 =         .       , v2 =           .        
          ..                 ..                       ..       
                                                   (m−1)(m−2) m−3
        λ m−1
                          (m − 1)λ  m−2
                                                        2     λ
```

**References:**
- uses_equation: `eq:111a`
- uses_equation: `eq:111b`
- uses_equation: `eq:111c`
- uses_equation: `eq:111d`

---

### Theorem 112B (p.47)
*Section 11, Subsection 112*

```
Theorem 112B If f satisfies a one-sided Lipschitz condition with constant
l, and y and z are each solutions of
                                  y  (x) = f (x, y(x)),
then for all x ≥ x0 ,
                 y(x) − z(x) ≤ exp(l(x − x0 )) y(x0 ) − z(x0 ) .
```

<details><summary>Proof</summary>

```
Proof. We have
           d                  d
             y(x) − z(x) 2 =    y(x) − z(x), y(x) − z(x)
          dx                 dx
                           = 2f (x, y(x)) − f (x, z(x)), y(x) − z(x)
                         ≤ 2l y(x) − z(x) 2 .
                            
Multiply by exp − 2l(x − x0 ) and it follows that
                d                                 
                    exp − 2l(x − x0 ) y(x) − z(x) 2 ≤ 0,
               dx
                        
so that exp − 2l(x − x0 ) y(x) − z(x) 2 is non-increasing.                   

   Note that the problem described in Subsection 102 possesses the one-sided
Lipschitz condition with l = 0.
   Even though stiff differential equation systems are typically non-linear,
there is a natural way in which a linear system arises from a given non-linear
system. Since stiffness is associated with the behaviour of perturbations to
a given solution, we suppose that there is a small perturbation Y (x) to a
solution y(x). The parameter is small, in the sense that we are interested only
in asymptotic behaviour of the perturbed solution as this quantity approaches
zero. If y(x) is replaced by y(x) + Y (x) in the differential equation
                              y  (x) = f (x, y(x)),                          (112a)
                                                               2
and the solution expanded in a series in powers of , with          and higher powers
replaced by zero, we obtain the system
                                                       ∂f
                   y  (x) + Y  (x) = f (x, y(x)) +      Y (x).             (112b)
                                                       ∂y
Subtract (112a) from (112b) and cancel out , and we arrive at the equation
governing the behaviour of the perturbation,
                                    ∂f
                        Y  (x) =      Y (x) = J(x)Y (x),
                                    ∂y
say. The ‘Jacobian matrix’ J(x) has a crucial role in the understanding of
problems of this type; in fact its spectrum is sometimes used to characterize
stiffness. In a time interval ∆x, chosen so that there is a moderate change
in the value of the solution to (112a), and very little change in J(x),
the eigenvalues of J(x) determine the growth rate of components of the
perturbation. The existence of one or more large and negative values of λ∆x,
for λ ∈ σ(J(x)), the spectrum of J(x), is a sign that stiffness is almost
certainly present. If J(x) possesses complex eigenvalues, then we interpret
this test for stiffness as the existence of a λ = Reλ + iImλ ∈ σ(J(x)) such
that Reλ∆x is negative with large magnitude.
```
</details>

**References:**
- uses_equation: `eq:112a`
- uses_equation: `eq:112b`
- uses_section: `sec:102`

---

### Theorem 123A (p.56)
*Section 12, Subsection 123*

```
Theorem 123A H(y(x)) is invariant.
```

<details><summary>Proof</summary>

```
Proof. Calculate ∂H/∂y to obtain the result
                         ∇(H) J∇(H) = 0.                                                  


  The Jacobian of this problem is equal to
                          ∂          ∂
                             f (y) =    (J∇(H)) = JW (y),
                          ∂y         ∂y
where W is the ‘Wronskian’ matrix defined as the 2N × 2N matrix with (i, j)
element equal to ∂ 2 H/∂yi ∂yj .
   If the initial value y0 = y(x0 ) is perturbed by a small number multiplied by
a fixed vector v0 , then, to within O( 2 ), the solution is modified by v + O( 2 )
where
                                     ∂f
                           v  (x) =    v(x) = JW (y)v(x).
                                     ∂y
For two such perturbations u and v, it is interesting to consider the value of
the scalar u Jv.
  This satisfies the differential equation
             d
               u Jv = u JJW v + (JW u) Jv = −u W v + u W v = 0.
            dx
Hence we have:




Figure 123(i) Illustration of symplectic behaviour for H(p, q) = p2 /2+q 2 /2 (left)
and H(p, q) = p2 /2 − cos(q) (right). The underlying image depicts the North Island
brown kiwi, Apteryx mantelli.
```
</details>

---

### Theorem 123B (p.57)
*Section 12, Subsection 123*

```
Theorem 123B u Jv is invariant with time.

  In the special case of a two-dimensional Hamiltonian problem, the value of
( u) J( v) can be interpreted as the area of the infinitesimal parallelogram
with sides in the directions u and v. As the solution evolves, u and v might
change, but the area u Jv remains invariant. This is illustrated in Figure
123(i) for the two problems H(p, q) = p2 /2 + q 2 /2 and H(p, q) = p2 /2 − cos(q)
respectively.
```

---

### Theorem 140A (p.66)
*Section 14, Subsection 140*

```
Theorem 140A The problem (140a), with initial value X0 given, has the
unique solution
              n
                            
                             n           
                                         n
      yn =          Ai X0 +     Ai φ1 +     Ai φ2 + · · · + An φn−1 + φn .
              i=1               i=2                 i=3
```

<details><summary>Proof</summary>

```
Proof. The result holds for n = 0, and the general case follows by induction.
                                                                           
```
</details>

**References:**
- uses_equation: `eq:140a`

---

### Theorem 141A (p.67)
*Section 14, Subsection 141*

```
Theorem 141A Using the notation introduced in this subsection, the
solution to (141a) with given initial values y0 , y1 , . . . , yk−1 is given by

                                   
                                   k−1                
                                                      n
                            yn =         θn−i yi +         θn−i ψi .                     (141c)
                                   i=0                i=k
```

<details><summary>Proof</summary>

```
Proof. Substitute n = m, for m = 0, 1, 2, . . . , k −1, into (141c), and we obtain
the value

            ym = ym + θ1 ym−1 + · · · + θm y0 ,          m = 0, 1, 2, . . . , k − 1.

This is equal to ym if (141b) holds. Add the contribution to the solution from
each of m = k, k + 1, . . . , n and the result follows.                      
```
</details>

**References:**
- uses_equation: `eq:141a`
- uses_equation: `eq:141c`
- uses_equation: `eq:141b`

**Referenced by:**
- `thm:406D` (uses_theorem)

---

### Theorem 142C (p.67)
*Section 14, Subsection 142*

```
Theorem 142C Let A denote an m × m matrix. The following statements
are equivalent:

   (i)   A is stable.
  (ii)   The minimal polynomial of A has all its zeros in the closed unit disc
         and all its multiple zeros in the open unit disc.
 (iii)   The Jordan canonical form of A has all its eigenvalues in the closed
         unit disc with all eigenvalues of magnitude 1 lying in 1 × 1 blocks.
 (iv)    There exists a non-singular matrix S such that S −1 AS ∞ ≤ 1.
```

<details><summary>Proof</summary>

```
Proof. We prove that (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i). If A is stable but
(ii) is not true, then either there exist λ and v = 0 such that |λ| > 1 and
Av = λv, or there exist λ, u = 0 and v such that |λ| = 1 and Av = λv + u,
with Au = λu. In the first case, An v = λn v and therefore An ≥ |λ|n
which is not bounded. In the second case, An v = λn v + nλn−1 u and therefore
 An ≥ n u / v − 1, which also is not bounded. Given (ii), it is not possible
that the conditions of (iii) are not satisfied, because the minimal polynomial
of any of the Jordan blocks, and therefore of A itself, would have factors that
contradict (ii). If (iii) is true, then S can be chosen to form J, the Jordan
canonical form of A, with the off-diagonal elements chosen sufficiently small
so that J ∞ ≤ 1. Finally, if (iv) is true then An = S(S −1 AS)n S −1 so that
 An ≤ S · S −1 AS n · S −1 ≤ S · S −1 .                                      
```
</details>

**Referenced by:**
- `thm:142F` (uses_theorem)

---

### Theorem 142D (p.68)
*Section 14, Subsection 142*

```
Theorem 142D Let A denote an m × m matrix. The following statements
are equivalent
   (i) A is convergent.
  (ii) The minimal polynomial of A has all its zeros in the open unit disc.
 (iii) The Jordan canonical form of A has all its diagonal elements in the
        open unit disc.
  (iv) There exists a non-singular matrix S such that S −1 AS ∞ < 1.
```

<details><summary>Proof</summary>

```
Proof. We again prove that (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) ⇒ (i). If A is convergent
but (ii) is not true, then there exist λ and u = 0 such that λ ≥ 1 and Au = λu.
Hence, An u = λn u and therefore An ≥ |λ|n , which does not converge to
zero. Given (ii), it is not possible that the conditions of (iii) are not satisfied,
because the minimal polynomial of any of the Jordan blocks, and therefore
of A itself, would have factors that contradict (ii). If (iii) is true, then S can
be chosen to form J, the Jordan canonical form of A, with the off-diagonal
elements chosen sufficiently small so that J ∞ < 1. Finally, if (iv) is true then
An = S(S −1 AS)n S −1 so that An ≤ S · S −1 · S −1 AS n → 0.                     

  While the two results we have presented here are related to the convergence
of difference equation solutions, the next is introduced only because of its
application in later chapters.
```
</details>

---

### Theorem 142E (p.69)
*Section 14, Subsection 142*

```
Theorem 142E If A is a stable m × m matrix and B an arbitrary m × m
matrix, then there exists a real C such that
                                      n 
                                          
                              A + 1 B  ≤ C,
                                    n     

for n = 1, 2, . . . .
```

<details><summary>Proof</summary>

```
Proof. Without loss of generality, assume that · denotes the norm                             ·   ∞.
Because S exists so that S −1 AS ≤ 1, we have
                   n                                 n 
                                                           
          A + 1 B  ≤ S · S −1 ·  S −1 AS + 1 S −1 BS 
                n                               n          
                                                     n
                                              1 −1
                          ≤ S · S −1 · 1 +      S BS
                                              n
                              ≤ S · S −1 exp( S −1 BS ).                                          
   In applying this result to sequences of vectors, the term represented by the
matrix B can be replaced by a non-linear function which satisfies suitable
conditions. To widen the applicability of the result a non-homogeneous term
is included.
```
</details>

---

### Theorem 142F (p.69)
*Section 14, Subsection 142*

```
Theorem 142F Let A be a stable m × m matrix and φ : Rm → Rm
be such that φ(x) ≤ L x , for L a positive constant and x ∈ Rm . If
w = (w1 , w2 , . . . , wn ) and v = (v0 , v1 , . . . , vn ) are sequences related by
                                   1
                    vi = Avi−1 +     φ(vi−1 ) + wi ,     i = 1, 2, . . . , n,                (142a)
                                   n
then                                                          !
                                                   
                                                   n
                            vn ≤ C        v0 +           wi       ,
                                                   i=1
where C is independent of n.
```

<details><summary>Proof</summary>

```
Proof. Let S be the matrix introduced in the proof of Theorem 142C. From
(142a), it follows that
                                                   1 −1
            (S −1 vi ) = (S −1 AS)(S −1 vi−1 ) +     (S φ(vi−1 )) + (S −1 wi )
                                                   n
and hence
                                                   1 −1
           S −1 vi ≤ S −1 AS · S −1 vi−1 +           S φ(vi−1 ) + S −1 wi ,
                                                   n
leading to the bound
                                                                                     !
                                                                     
                                                                       n
                             −1
            vn ≤ S · S            exp L S · S −1              v0 +              wi       .        
                                                                       i=1
```
</details>

**References:**
- uses_theorem: `thm:142C`
- uses_equation: `eq:142a`

---

## Lemmas (1)

### Lemma 110B (p.43)
*Section 11, Subsection 110*

```
Lemma 110B Let M denote a complete metric space with metric ρ and let
φ : M → M denote a mapping which is a contraction, in the sense that
there exists a number k, satisfying 0 ≤ k < 1, such that, for any η, ζ ∈ M ,
ρ(φ(η), φ(ζ)) ≤ kρ(η, ζ). Then there exists a unique ξ ∈ M such that φ(ξ) = ξ.

  We can now state our main result.
```

---
