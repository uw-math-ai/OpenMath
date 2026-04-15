# Chapter 2: Numerical Differential Equation Methods

Pages 51-135

## Sections

- **20** The Euler Method
- **21** Analysis of the Euler Method
- **22** Generalizations of the Euler Method
- **23** Runge–Kutta Methods
- **24** Linear Multistep Methods
- **25** Taylor Series Methods
- **26** Hybrid Methods
- **27** Introduction to Implementation

## Theorems (4)

### Theorem 212A (p.89)
*Section 21, Subsection 212*

```
Theorem 212A Assuming that f satisfies a Lipschitz condition, with
constant L, the global error satisfies the bound
                   
                   
                    y(x0 )− y (x0 ) + Hm(x−x0 ),          L = 0,
   y(x) − y(x) ≤ exp((x−x0 )L) y(x0 )−     y (x0 ) + (exp((x−x0 )L)−1) Hm
                                                                         L ,
                   
                                                            L > 0.
```

**Referenced by:**
- `thm:213A` (uses_theorem)

---

### Theorem 213A (p.89)
*Section 21, Subsection 213*

```
Theorem 213A Under the conditions stated in the above discussion, Dn → 0
as n → ∞.
```

<details><summary>Proof</summary>

```
Proof. This result follows immediately from the bound on accumulated errors
given by Theorem 212A.                                                   

  The property expressed in this theorem is known as ‘convergence’. In
searching for other numerical methods that are suitable for solving initial value
problems, attention is usually limited to convergent methods. The reason for
this is clear: a non-convergent method is likely to give increasingly meaningless
results as greater computational effort is expended through the use of smaller
stepsizes.
  Because the bound used in the proof of Theorem 213A holds not only for
x = x, but also for all x ∈ [x0 , x], we can state a uniform version of this result.
```
</details>

**References:**
- uses_theorem: `thm:212A`

**Referenced by:**
- `thm:213B` (uses_theorem)

---

### Theorem 213B (p.89)
*Section 21, Subsection 213*

```
Theorem 213B Under the conditions of Theorem 213A,
                             sup       y(x) − yn (x) → 0
                           x∈[x0 ,x]
as n → ∞.

       Table 214(I)    An example of enhanced order for problem (214a)

                         n              |Error|      Ratio
                         20 1130400.0252×10−10 4.4125
                         40 256178.9889×10−10 4.1893
                         80    61150.2626×10−10 4.0904
                        160    14949.6176×10−10 4.0442
                        320       3696.5967×10−10 4.0218
                        640        919.1362×10−10 4.0108
                       1280        229.1629×10−10 4.0054
                       2560         57.2134×10−10 4.0026
                       5120         14.2941×10−10 4.0003
                      10240          3.5733×10−10
```

**References:**
- uses_theorem: `thm:213A`
- uses_equation: `eq:214a`

---

### Theorem 243A (p.130)
*Section 22, Subsection 243*

```
Theorem 243A A linear multistep method is convergent if and only if it is
stable and consistent.
```

---
