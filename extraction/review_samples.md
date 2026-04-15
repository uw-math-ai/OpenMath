# LaTeX Conversion Review

10 sample statements for manual quality check.

For each statement: original pdftotext output, then DeepSeek LaTeX output.

---

## Theorem 101A  (Chapter 1, Section 10, Page 26)

### Original (pdftotext)

```
Theorem 101A The quantities
                     1 2       
                H=      y3 + y42 − (y12 + y22 )−1/2 ,
                     2
                A = y1 y4 − y2 y3
are constant.
```

### Original Proof (pdftotext)

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
                                   
... [truncated, full text in formal_statements.json]
```

### DeepSeek LaTeX Output

```latex
\begin{theorem}
The quantities
\[
H = \frac{1}{2} \left( y_3^2 + y_4^2 \right) - \left( y_1^2 + y_2^2 \right)^{-1/2}, \quad A = y_1 y_4 - y_2 y_3
\]
are constant.
\end{theorem}

\begin{proof}
We verify that the values of $dH/dx$ and $dA/dx$ are zero if $y$ satisfies \eqref{eq:101a}--\eqref{eq:101d}. We have
\begin{align*}
\frac{dH}{dx} &= y_3 \frac{dy_3}{dx} + y_4 \frac{dy_4}{dx} + y_1 \frac{dy_1}{dx} \left( y_1^2 + y_2^2 \right)^{-3/2} + y_2 \frac{dy_2}{dx} \left( y_1^2 + y_2^2 \right)^{-3/2} \\
&= -\frac{y_1 y_3}{\left( y_1^2 + y_2^2 \right)^{3/2}} - \frac{y_2 y_4}{\left( y_1^2 + y_2^2 \right)^{3/2}} + \frac{y_1 y_3}{\left( y_1^2 + y_2^2 \right)^{3/2}} + \frac{y_2 y_4}{\left( y_1^2 + y_2^2 \right)^{3/2}} \\
&= 0
\end{align*}
and
\begin{align*}
\frac{dA}{dx} &= y_1 \frac{dy_4}{dx} + \frac{dy_1}{dx} y_4 - y_2 \frac{dy_3}{dx} - \frac{dy_2}{dx} y_3 \\
&= -\frac{y_1 y_2}{\left( y_1^2 + y_2^2 \right)^{3/2}} + y_3 y_4 + \frac{y_2 y_1}{\left( y_1^2 + y_2^2 \right)^{3/2}} - y_4 y_3 \\
&= 0.
\end{align*}
The quantities $H$ and $A$ are the `Hamiltonian' and `angular momentum', respectively. Note that $H = T + V$, where $T = \frac{1}{2} \left( y_3^2 + y_4^2 \right)$ is the kinetic energy and $V = -\left( y_1^2 + y_2^2 \right)^{-1/2}$ is the potential energy.

A further property of this problem is its invariance under changes of scale of the variables:
\[
y_1 = \alpha^{-2} \overline{y}_1, \quad y_2 = \alpha^{-2} \overline{y}_2, \quad y_3 = \alpha \overline{y}_3, \quad y_4 = \alpha \overline{y}_4, \quad x = \alpha^{-3} \overline{x}.
\]
The Hamiltonian and angular momentum get scaled to
\[
\overline{H} = \frac{1}{2} \left( \overline{y}_3^2 + \overline{y}_4^2 \right) - \left( \overline{y}_1^2 + \overline{y}_2^2 \right)^{-1/2} = \alpha^{-2} H, \quad \overline{A} = \overline{y}_1 \overline{y}_4 - \overline{y}_2 \overline{y}_3 = \alpha A.
\]

A second type of transformation is based on a two-dimensional orthogonal transformation (that is, a rotation or a reflection or a composition of these) $Q$, where $Q^{-1} = Q^\top$. The time variable $x$ is invariant, and the position and velocity variables get transformed to
\[
\begin{bmatrix}
\overline{y}_1 \\
\overline{y}_2 \\
\overline{y}_3 \\
\overline{y}_4
\end{bmatrix}
=
\begin{bmatrix}
Q & 0 \\
0 & Q
\end{bmatrix}
\begin{bmatrix}
y_1 \\
y_2 \\
y_3 \\
y_4
\end{bmatrix}.
\]

It is easy to see that $A = 0$ implies that the trajectory lies entirely in a subspace defined by $\cos(\theta) y_1 = \sin(\theta) y_2$, $\cos(\theta) y_3 = \sin(\theta) y_4$ for some fixed angle $\theta$. We move on from this simple case and assume that $A \neq 0$. The sign of $H$ is of crucial importance: if $H \geq 0$ then it is possible to obtain arbitrarily high values of $y_1^2 + y_2^2$ without $y_3^2 + y_4^2$ vanishing. We exclude this case for the present discussion and assume that $H < 0$. Scale $H$ so that it has a value $-\frac{1}{2}$ and at the same time $A$ takes on a positive value. This value cannot exceed $1$ because we can easily verify an identity involving the derivative of $r = \sqrt{y_1^2 + y_2^2}$. This identity is
\[
r \left( \frac{dr}{dx} \right)^2 = 2H r^2 + 2r - A^2 = -r^2 + 2r - A^2. \tag{101e}
\]
Since the left-hand side cannot be negative, the quadratic function in $r$ on the right-hand side must have real roots. This implies that $A \leq 1$. Write $A = \sqrt{1 - e^2}$, for $e \geq 0$, where we see that $e$ is the eccentricity of an ellipse on which the orbit lies. The minimum and maximum values of $r$ are found to be $1 - e$ and $1 + e$, respectively. Rotate axes so that when $r = 1 - e$, which we take as the starting point of time, $y_1 = 1 - e$ and $y_2 = 0$. At this point we find that $y_3 = 0$ and $y_4 = \sqrt{(1 + e)/(1 - e)}$.

Change to polar coordinates by writing $y_1 = r \cos(\theta)$, $y_2 = r \sin(\theta)$. It is found that
\[
y_3 = \frac{dy_1}{dx} = \frac{dr}{dx} \cos(\theta) - r \frac{d\theta}{dx} \sin(\theta), \quad y_4 = \frac{dy_2}{dx} = \frac{dr}{dx} \sin(\theta) + r \frac{d\theta}{dx} \cos(\theta),
\]
so that, because $y_1 y_4 - y_2 y_3 = \sqrt{1 - e^2}$, we find that
\[
r^2 \frac{d\theta}{dx} = \sqrt{1 - e^2}. \tag{101f}
\]
From \eqref{eq:101e} and \eqref{eq:101f} we find a differential equation for the path traced out by the orbit
\[
\left( \frac{dr}{d\theta} \right)^2 = \frac{1}{1 - e^2} \left[ r^2 e^2 - (1 - r)^2 \right],
\]
and we can verify that this is satisfied by
\[
\frac{1 - e^2}{r} = 1 + e \cos(\theta).
\]
If we change back to Cartesian coordinates, we find that all points on the trajectory lie on the ellipse
\[
(y_1 + e)^2 + \frac{y_2^2}{1 - e^2} = 1,
\]
with centre $(-e, 0)$, eccentricity $e$, and major and minor axis lengths $1$ and $\sqrt{1 - e^2}$ respectively.

As we have seen, a great deal is known about this problem. However, much less is known about the motion of a many-body gravitational system.

One of the aims of modern numerical analysis is to understand the behaviour of various geometrical properties. In some cases it is possible to preserve the value of quantities that are invariant in the exact solution. In other situations, such as problems where the Hamiltonian is theoretically conserved, it may be preferable to conserve other properties, such as what is known as `symplectic behaviour'.

We consider further gravitational problems in Subsection~\ref{subsec:120}.
\end{proof}
```

---

## Definition 110A  (Chapter 1, Section 11, Page 43)

### Original (pdftotext)

```
Definition 110A The function f : [a, b] × RN → RN is said to satisfy
a ‘Lipschitz condition in its second variable’ if there exists a constant L,
known as a ‘Lipschitz constant’, such that for any x ∈ [a, b] and Y, Z ∈ RN ,
 f (x, Y ) − f (x, Z) ≤ L Y − Z .
  We need a basic lemma on metric spaces known as the ‘contraction mapping
principle’. We present this without proof.
```

### DeepSeek LaTeX Output

```latex
\begin{definition}
The function $f : [a, b] \times \mathbb{R}^N \to \mathbb{R}^N$ is said to satisfy a \emph{Lipschitz condition in its second variable} if there exists a constant $L$, known as a \emph{Lipschitz constant}, such that for any $x \in [a, b]$ and $Y, Z \in \mathbb{R}^N$,
\[
\| f(x, Y) - f(x, Z) \| \leq L \| Y - Z \|.
\]
We need a basic lemma on metric spaces known as the \emph{contraction mapping principle}. We present this without proof.
\end{definition}
```

---

## Lemma 110B  (Chapter 1, Section 11, Page 43)

### Original (pdftotext)

```
Lemma 110B Let M denote a complete metric space with metric ρ and let
φ : M → M denote a mapping which is a contraction, in the sense that
there exists a number k, satisfying 0 ≤ k < 1, such that, for any η, ζ ∈ M ,
ρ(φ(η), φ(ζ)) ≤ kρ(η, ζ). Then there exists a unique ξ ∈ M such that φ(ξ) = ξ.
DIFFERENTIAL AND DIFFERENCE EQUATIONS                                             23

  We can now state our main result.
```

### DeepSeek LaTeX Output

```latex
\begin{lemma}
Let \( M \) denote a complete metric space with metric \( \rho \) and let
\( \varphi : M \to M \) denote a mapping which is a contraction, in the sense that
there exists a number \( k \), satisfying \( 0 \leq k < 1 \), such that, for any \( \eta, \zeta \in M \),
\[
\rho(\varphi(\eta), \varphi(\zeta)) \leq k \rho(\eta, \zeta).
\]
Then there exists a unique \( \xi \in M \) such that \( \varphi(\xi) = \xi \).
\end{lemma}
```

---

## Theorem 110C  (Chapter 1, Section 11, Page 44)

### Original (pdftotext)

```
Theorem 110C Consider an initial value problem

                               y  (x) = f (x, y(x)),                       (110a)
                                y(a) = y0 ,                                 (110b)

where f : [a, b] × RN → RN is continuous in its first variable and satisfies a
Lipschitz condition in its second variable. Then there exists a unique solution
to this problem.
```

### Original Proof (pdftotext)

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
            
... [truncated, full text in formal_statements.json]
```

### DeepSeek LaTeX Output

```latex
\begin{theorem}[110C]
Consider an initial value problem
\[
y'(x) = f(x, y(x)), \tag{110a}
\]
\[
y(a) = y_0, \tag{110b}
\]
where \( f : [a, b] \times \mathbb{R}^N \to \mathbb{R}^N \) is continuous in its first variable and satisfies a Lipschitz condition in its second variable. Then there exists a unique solution to this problem.
\end{theorem}

\begin{proof}
Let \( M \) denote the complete metric space of continuous functions \( y : [a, b] \to \mathbb{R}^N \), such that \( y(a) = y_0 \). The metric is defined by
\[
\rho(y, z) = \sup_{x \in [a, b]} \exp(-K(x - a)) \| y(x) - z(x) \|,
\]
where \( K > L \). For given \( y \in M \), define \( \varphi(y) \) as the solution \( Y \) on \( [a, b] \) to the initial value problem
\[
Y'(x) = f(x, Y(x)), \quad Y(a) = y_0.
\]
This problem is solvable by integration as
\[
\varphi(y)(x) = y_0 + \int_a^x f(s, y(s)) \, ds.
\]
This is a contraction because for any two \( y, z \in M \), we have
\begin{align*}
\rho(\varphi(y), \varphi(z)) &\leq \sup_{x \in [a, b]} \exp(-K(x - a)) \left\| \int_a^x \bigl( f(s, y(s)) - f(s, z(s)) \bigr) \, ds \right\| \\
&\leq \sup_{x \in [a, b]} \exp(-K(x - a)) \int_a^x \| f(s, y(s)) - f(s, z(s)) \| \, ds \\
&\leq L \sup_{x \in [a, b]} \exp(-K(x - a)) \int_a^x \| y(s) - z(s) \| \, ds \\
&\leq L \rho(y, z) \sup_{x \in [a, b]} \exp(-K(x - a)) \int_a^x \exp(K(s - a)) \, ds \\
&\leq \frac{L}{K} \rho(y, z).
\end{align*}
The unique function \( y \) that therefore exists satisfying \( \varphi(y) = y \), is evidently the unique solution to the initial value problem given by \eqref{eq:110a}, \eqref{eq:110b}.
\end{proof}

The third requirement for being well-posed, that the solution is not overly sensitive to the initial condition, can be readily assessed for problems satisfying
```

---

## Theorem 111A  (Chapter 1, Section 11, Page 45)

### Original (pdftotext)

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
DIFFERENTIAL AND DIFFERENCE EQUATIONS                                              25

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

### DeepSeek LaTeX Output

```latex
\begin{theorem}
If $\hat{y}$ is a solution to \eqref{eq:111a} and $y_1, y_2, \dots, y_k$ are solutions to \eqref{eq:111b}, then for any constants $\alpha_1, \alpha_2, \dots, \alpha_k$, the function $y$ given by
\[
y(x) = \hat{y}(x) + \sum_{i=1}^k \alpha_i y_i(x),
\]
is a solution to \eqref{eq:111a}.

The way this result is used is to attempt to find the solution which matches a given initial value, by combining known solutions.

Many linear problems are naturally formulated in the form of a single high order differential equation
\[
Y^{(m)}(x) - C_1(x) Y^{(m-1)}(x) - C_2(x) Y^{(m-2)}(x) - \cdots - C_m(x) Y(x) = g(x). \tag{111c}
\]

By identifying $Y(x) = y_1(x)$, $Y'(x) = y_2(x)$, $\dots$, $Y^{(m-1)} = y_m(x)$, we can rewrite the system in the form
\[
\frac{d}{dx} \begin{bmatrix} y_1(x) \\ y_2(x) \\ \vdots \\ y_m(x) \end{bmatrix} = A(x) \begin{bmatrix} y_1(x) \\ y_2(x) \\ \vdots \\ y_m(x) \end{bmatrix} + \phi(x),
\]
where the `companion matrix' $A(x)$ and the `inhomogeneous term' $\phi(x)$ are given by
\[
A(x) = \begin{bmatrix}
0 & 1 & 0 & \cdots & 0 \\
0 & 0 & 1 & \cdots & 0 \\
0 & 0 & 0 & \cdots & 0 \\
\vdots & \vdots & \vdots & & \vdots \\
0 & 0 & 0 & \cdots & 1 \\
C_m(x) & C_{m-1}(x) & C_{m-2}(x) & \cdots & C_1(x)
\end{bmatrix}, \quad
\phi(x) = \begin{bmatrix} 0 \\ 0 \\ 0 \\ \vdots \\ 0 \\ g(x) \end{bmatrix}.
\]

When $A(x) = A$ in \eqref{eq:111b} is constant, then to each eigenvalue $\lambda$ of $A$, with corresponding eigenvector $v$, there exists a solution given by
\[
y(x) = \exp(\lambda x) v. \tag{111d}
\]

When a complete set of eigenvectors does not exist, but corresponding to $\lambda$ there is a chain of generalized eigenvectors
\[
A v_1 = \lambda v_1 + v, \quad A v_2 = \lambda v_2 + v_1, \quad \dots, \quad A v_{k-1} = \lambda v_{k-1} + v_{k-2},
\]
then there is a chain of additional independent solutions to append to \eqref{eq:111d}:
\[
y_1 = x \exp(\lambda x) v_1, \quad y_2 = x^2 \exp(\lambda x) v_2, \quad \dots, \quad y_{k-1} = x^{k-1} \exp(\lambda x) v_{k-1}.
\]

In the special case in which $A$ is a companion matrix, so that the system is equivalent to a high order equation in a single variable, as in \eqref{eq:111c}, with $C_1(x) = C_1$, $C_2(x) = C_2$, $\dots$, $C_m(x) = C_m$, each a constant, the characteristic polynomial of $A$ is
\[
P(\lambda) = \lambda^m - C_1 \lambda^{m-1} - C_2 \lambda^{m-2} - \cdots - C_m = 0.
\]

For this special case, $P(\lambda)$ is also the minimal polynomial, and repeated zeros always correspond to incomplete eigenvector spaces and the need to use generalized eigenvectors. Also, in this special case, the eigenvector corresponding to $\lambda$, together with the generalized eigenvectors if they exist, are
\[
v = \begin{bmatrix} 1 \\ \lambda \\ \lambda^2 \\ \vdots \\ \lambda^{m-1} \end{bmatrix}, \quad
v_1 = \begin{bmatrix} 0 \\ 1 \\ 2\lambda \\ \vdots \\ (m-1)\lambda^{m-2} \end{bmatrix}, \quad
v_2 = \begin{bmatrix} 0 \\ 0 \\ 1 \\ \vdots \\ \frac{(m-1)(m-2)}{2} \lambda^{m-3} \end{bmatrix}, \quad \dots.
\]
\end{theorem}
```

---

## Definition 112A  (Chapter 1, Section 11, Page 47)

### Original (pdftotext)

```
Definition 112A The function f satisfies a ‘one-sided Lipschitz condition’,
with ‘one-sided Lipschitz constant’ l if for all x ∈ [a, b] and all u, v ∈ RN ,
                        f (x, u) − f (x, v), u − v ≤ l u − v 2 .
It is possible that the function f could have a very large Lipschitz constant
but a moderately sized, or even negative, one-sided Lipschitz constant. The
advantage of this is seen in the following result.
```

### DeepSeek LaTeX Output

```latex
\begin{definition}
The function $f$ satisfies a `one-sided Lipschitz condition',
with `one-sided Lipschitz constant' $l$ if for all $x \in [a, b]$ and all $u, v \in \mathbb{R}^N$,
\[
\langle f(x, u) - f(x, v), u - v \rangle \leq l \| u - v \|^2.
\]
It is possible that the function $f$ could have a very large Lipschitz constant
but a moderately sized, or even negative, one-sided Lipschitz constant. The
advantage of this is seen in the following result.
\end{definition}
```

---

## Theorem 112B  (Chapter 1, Section 11, Page 47)

### Original (pdftotext)

```
Theorem 112B If f satisfies a one-sided Lipschitz condition with constant
l, and y and z are each solutions of
                                  y  (x) = f (x, y(x)),
then for all x ≥ x0 ,
                 y(x) − z(x) ≤ exp(l(x − x0 )) y(x0 ) − z(x0 ) .
```

### Original Proof (pdftotext)

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
DIFFERENTIAL AND DIFFERENCE EQUATIONS                                             27

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
and the solution expanded in a series in powe
... [truncated, full text in formal_statements.json]
```

### DeepSeek LaTeX Output

```latex
\begin{theorem}
If \( f \) satisfies a one-sided Lipschitz condition with constant \( l \), and \( y \) and \( z \) are each solutions of
\[
y'(x) = f(x, y(x)),
\]
then for all \( x \geq x_0 \),
\[
\| y(x) - z(x) \| \leq \exp(l(x - x_0)) \| y(x_0) - z(x_0) \|.
\]
\end{theorem}

\begin{proof}
We have
\[
\frac{d}{dx} \| y(x) - z(x) \|^2 = \frac{d}{dx} \langle y(x) - z(x), y(x) - z(x) \rangle
\]
\[
= 2 \langle f(x, y(x)) - f(x, z(x)), y(x) - z(x) \rangle
\]
\[
\leq 2l \| y(x) - z(x) \|^2.
\]
Multiply by \( \exp(-2l(x - x_0)) \) and it follows that
\[
\frac{d}{dx} \left[ \exp(-2l(x - x_0)) \| y(x) - z(x) \|^2 \right] \leq 0,
\]
so that \( \exp(-2l(x - x_0)) \| y(x) - z(x) \|^2 \) is non-increasing.
\end{proof}

Note that the problem described in Subsection~102 possesses the one-sided Lipschitz condition with \( l = 0 \).

Even though stiff differential equation systems are typically non-linear, there is a natural way in which a linear system arises from a given non-linear system. Since stiffness is associated with the behaviour of perturbations to a given solution, we suppose that there is a small perturbation \( \epsilon Y(x) \) to a solution \( y(x) \). The parameter \( \epsilon \) is small, in the sense that we are interested only in asymptotic behaviour of the perturbed solution as this quantity approaches zero. If \( y(x) \) is replaced by \( y(x) + \epsilon Y(x) \) in the differential equation
\[
y'(x) = f(x, y(x)), \tag{112a}
\]
and the solution expanded in a series in powers of \( \epsilon \), with \( \epsilon^2 \) and higher powers replaced by zero, we obtain the system
\[
y'(x) + \epsilon Y'(x) = f(x, y(x)) + \epsilon \frac{\partial f}{\partial y} Y(x). \tag{112b}
\]
Subtract \eqref{eq:112a} from \eqref{eq:112b} and cancel out \( \epsilon \), and we arrive at the equation governing the behaviour of the perturbation,
\[
Y'(x) = \frac{\partial f}{\partial y} Y(x) = J(x) Y(x),
\]
say. The `Jacobian matrix' \( J(x) \) has a crucial role in the understanding of problems of this type; in fact its spectrum is sometimes used to characterize stiffness. In a time interval \( \Delta x \), chosen so that there is a moderate change in the value of the solution to \eqref{eq:112a}, and very little change in \( J(x) \), the eigenvalues of \( J(x) \) determine the growth rate of components of the perturbation. The existence of one or more large and negative values of \( \lambda \Delta x \), for \( \lambda \in \sigma(J(x)) \), the spectrum of \( J(x) \), is a sign that stiffness is almost certainly present. If \( J(x) \) possesses complex eigenvalues, then we interpret this test for stiffness as the existence of a \( \lambda = \operatorname{Re} \lambda + i \operatorname{Im} \lambda \in \sigma(J(x)) \) such that \( \operatorname{Re} \lambda \Delta x \) is negative with large magnitude.
```

---

## Theorem 123A  (Chapter 1, Section 12, Page 56)

### Original (pdftotext)

```
Theorem 123A H(y(x)) is invariant.
```

### Original Proof (pdftotext)

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
```

### DeepSeek LaTeX Output

```latex
\begin{theorem}
\( H(y(x)) \) is invariant.
\end{theorem}

\begin{proof}
Calculate \( \partial H / \partial y \) to obtain the result
\[
\nabla(H) J \nabla(H) = 0.
\]

The Jacobian of this problem is equal to
\[
\frac{\partial}{\partial y} f(y) = \frac{\partial}{\partial y} (J \nabla(H)) = J W(y),
\]
where \( W \) is the `Wronskian' matrix defined as the \( 2N \times 2N \) matrix with \( (i, j) \) element equal to \( \partial^2 H / \partial y_i \partial y_j \).

If the initial value \( y_0 = y(x_0) \) is perturbed by a small number multiplied by a fixed vector \( v_0 \), then, to within \( O(\epsilon^2) \), the solution is modified by \( v + O(\epsilon^2) \) where
\[
v'(x) = \frac{\partial f}{\partial y} v(x) = J W(y) v(x).
\]
For two such perturbations \( u \) and \( v \), it is interesting to consider the value of the scalar \( u^\top J v \).

This satisfies the differential equation
\[
\frac{d}{dx} u^\top J v = u^\top J J W v + (J W u)^\top J v = -u^\top W v + u^\top W v = 0.
\]
Hence we have:
\end{proof}
```

---

## Theorem 123B  (Chapter 1, Section 12, Page 57)

### Original (pdftotext)

```
Theorem 123B u Jv is invariant with time.

  In the special case of a two-dimensional Hamiltonian problem, the value of
( u) J( v) can be interpreted as the area of the infinitesimal parallelogram
with sides in the directions u and v. As the solution evolves, u and v might
change, but the area u Jv remains invariant. This is illustrated in Figure
123(i) for the two problems H(p, q) = p2 /2 + q 2 /2 and H(p, q) = p2 /2 − cos(q)
respectively.
```

### DeepSeek LaTeX Output

```latex
\begin{theorem}
In the special case of a two-dimensional Hamiltonian problem, the value of \( u^{\top} J v \) can be interpreted as the area of the infinitesimal parallelogram with sides in the directions \( u \) and \( v \). As the solution evolves, \( u \) and \( v \) might change, but the area \( u^{\top} J v \) remains invariant. This is illustrated in Figure~\ref{fig:123i} for the two problems \( H(p, q) = p^{2}/2 + q^{2}/2 \) and \( H(p, q) = p^{2}/2 - \cos(q) \) respectively.
\end{theorem}
```

---

## Theorem 140A  (Chapter 1, Section 14, Page 66)

### Original (pdftotext)

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

### Original Proof (pdftotext)

```
Proof. The result holds for n = 0, and the general case follows by induction.
                                                                           
```

### DeepSeek LaTeX Output

```latex
\begin{theorem}
The problem \eqref{eq:140a}, with initial value $X_0$ given, has the unique solution
\[
y_n = \sum_{i=1}^{n} A_i X_0 + \sum_{i=2}^{n} A_i \varphi_1 + \sum_{i=3}^{n} A_i \varphi_2 + \cdots + A_n \varphi_{n-1} + \varphi_n.
\]
\end{theorem}

\begin{proof}
The result holds for $n = 0$, and the general case follows by induction.
\end{proof}
```

---
