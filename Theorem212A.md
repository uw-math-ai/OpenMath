# Theorem 212A: Global Truncation Error Bound for the Euler Method

**Source:** J.C. Butcher, *Numerical Methods for Ordinary Differential Equations*, 2nd Edition, Section 212 (p. 66--68).

---

## Setting

We consider the initial value problem

$$y'(x) = f(x, y(x)), \qquad y(x_0) = y_0, \tag{210a}$$

where $f : [a,b] \times \mathbb{R}^N \to \mathbb{R}^N$ is continuous and satisfies a **Lipschitz condition**

$$\|f(x, y) - f(x, z)\| \leq L\|y - z\|$$

for all $x$ in a neighbourhood of $x_0$ and $y, z$ in a neighbourhood of $y_0$, with Lipschitz constant $L \geq 0$.

We approximate the solution on the interval $[x_0, \bar{x}]$ using step points $x_0 < x_1 < x_2 < \cdots < x_n = \bar{x}$.

### The Euler approximation

Define the **piecewise-linear Euler approximation** $\widetilde{y}$ on $[x_0, \bar{x}]$ as follows. At step points, $\widetilde{y}(x_k) = y_k$ is computed by the Euler method:

$$y_k = y_{k-1} + (x_k - x_{k-1}) f(x_{k-1}, y_{k-1}), \qquad k = 1, 2, \ldots, n.$$

For off-step points $x \in (x_{k-1}, x_k)$, $\widetilde{y}$ is defined by linear interpolation:

$$\widetilde{y}(x) = y_{k-1} + (x - x_{k-1}) f(x_{k-1}, y_{k-1}). \tag{212a}$$

### Key definitions

Define the **error** and the **residual** at any point $x$:

$$\alpha(x) = y(x) - \widetilde{y}(x), \tag{212b}$$

$$\beta(x) = f(x, y(x)) - f(x, \widetilde{y}(x)). \tag{212c}$$

By the Lipschitz condition:

$$\|\beta(x)\| \leq L\|\alpha(x)\|. \tag{212d}$$

### Local truncation error remainder

Since $y$ is the exact solution, we can write (using Taylor expansion with integral remainder as in equation (211a)):

$$y(x) = y(x_{k-1}) + (x - x_{k-1}) f(x_{k-1}, y(x_{k-1})) + (x - x_{k-1})^2 E(x), \qquad x \in (x_{k-1}, x_k], \tag{212e}$$

where $E(x)$ captures the local truncation error. Explicitly, from the integral form of the remainder:

$$E(x) = \frac{1}{(x - x_{k-1})^2} \int_0^{x - x_{k-1}} (x - x_{k-1} - s)\, y''(x_{k-1} + s)\, ds.$$

We assume a **uniform bound** on this remainder:

$$\|E(x)\| \leq m$$

for all $x \in [x_0, \bar{x}]$, where $m$ is a constant. (This holds whenever $y''$ is continuous and bounded on $[x_0, \bar{x}]$.)

Let $H$ denote the **maximum stepsize**:

$$H = \max_{1 \leq k \leq n} (x_k - x_{k-1}).$$

---

## Theorem 212A (Global Error Bound)

**Theorem.** *Assuming that $f$ satisfies a Lipschitz condition, with constant $L$, the global error satisfies the bound*

$$\|y(x) - \widetilde{y}(x)\| \leq \begin{cases} \|y(x_0) - \widetilde{y}(x_0)\| + Hm(x - x_0), & L = 0, \\[6pt] \exp\bigl((x - x_0)L\bigr)\|y(x_0) - \widetilde{y}(x_0)\| + \dfrac{\exp\bigl((x - x_0)L\bigr) - 1}{L}\, Hm, & L > 0. \end{cases}$$

---

## Proof

### Step 1: Derive the recurrence for $\|\alpha(x)\|$

Subtract equation (212a) from equation (212e). For $x \in (x_{k-1}, x_k]$:

$$\alpha(x) = y(x) - \widetilde{y}(x)$$

$$= \bigl[y(x_{k-1}) + (x - x_{k-1}) f(x_{k-1}, y(x_{k-1})) + (x - x_{k-1})^2 E(x)\bigr] - \bigl[y_{k-1} + (x - x_{k-1}) f(x_{k-1}, y_{k-1})\bigr]$$

$$= \alpha(x_{k-1}) + (x - x_{k-1})\bigl[f(x_{k-1}, y(x_{k-1})) - f(x_{k-1}, \widetilde{y}(x_{k-1}))\bigr] + (x - x_{k-1})^2 E(x)$$

$$= \alpha(x_{k-1}) + (x - x_{k-1})\,\beta(x_{k-1}) + (x - x_{k-1})^2 E(x).$$

Taking norms and applying the triangle inequality:

$$\|\alpha(x)\| \leq \|\alpha(x_{k-1})\| + (x - x_{k-1})\|\beta(x_{k-1})\| + (x - x_{k-1})^2\, m.$$

Apply the Lipschitz bound (212d) to $\|\beta(x_{k-1})\| \leq L\|\alpha(x_{k-1})\|$:

$$\|\alpha(x)\| \leq \|\alpha(x_{k-1})\| + (x - x_{k-1}) L\|\alpha(x_{k-1})\| + (x - x_{k-1})^2\, m$$

$$= \bigl(1 + (x - x_{k-1}) L\bigr)\|\alpha(x_{k-1})\| + (x - x_{k-1})^2\, m.$$

Since $(x - x_{k-1}) \leq H$:

$$\boxed{\|\alpha(x)\| \leq \bigl(1 + (x - x_{k-1}) L\bigr)\|\alpha(x_{k-1})\| + (x - x_{k-1})\, Hm.} \tag{$\star$}$$

### Step 2: Case $L = 0$

When $L = 0$, the recurrence $(\star)$ simplifies to:

$$\|\alpha(x)\| \leq \|\alpha(x_{k-1})\| + (x - x_{k-1})\, Hm.$$

Applying this recursively at the step points $x_0, x_1, \ldots, x_{k-1}$ and then from $x_{k-1}$ to $x$:

$$\|\alpha(x)\| \leq \|\alpha(x_0)\| + Hm\bigl[(x - x_{k-1}) + (x_{k-1} - x_{k-2}) + \cdots + (x_1 - x_0)\bigr]$$

$$= \|\alpha(x_0)\| + Hm(x - x_0). \tag{212f}$$

### Step 3: Case $L > 0$

When $L > 0$, we use a Gronwall-type argument. Rewrite $(\star)$ by adding $\frac{Hm}{L}$ to both sides:

$$\|\alpha(x)\| + \frac{Hm}{L} \leq \bigl(1 + (x - x_{k-1}) L\bigr)\|\alpha(x_{k-1})\| + (x - x_{k-1}) Hm + \frac{Hm}{L}.$$

Factor the right-hand side:

$$= \bigl(1 + (x - x_{k-1}) L\bigr)\|\alpha(x_{k-1})\| + \frac{Hm}{L}\bigl(1 + (x - x_{k-1}) L\bigr)$$

$$= \bigl(1 + (x - x_{k-1}) L\bigr)\left(\|\alpha(x_{k-1})\| + \frac{Hm}{L}\right).$$

Define the function:

$$\phi(x) = \exp\bigl(-(x - x_0) L\bigr)\left(\|\alpha(x)\| + \frac{Hm}{L}\right).$$

We show $\phi$ is non-increasing. Using the inequality $1 + u \leq e^u$ for all $u \geq 0$ (applied with $u = (x - x_{k-1})L$):

$$\phi(x) \leq \exp\bigl(-(x - x_0) L\bigr) \cdot \exp\bigl((x - x_{k-1}) L\bigr) \cdot \left(\|\alpha(x_{k-1})\| + \frac{Hm}{L}\right)$$

$$= \exp\bigl(-(x_{k-1} - x_0) L\bigr)\left(\|\alpha(x_{k-1})\| + \frac{Hm}{L}\right) = \phi(x_{k-1}).$$

Therefore $\phi(x) \leq \phi(x_{k-1}) \leq \cdots \leq \phi(x_0)$, so $\phi$ never increases. Evaluating at $x_0$:

$$\phi(x_0) = \|\alpha(x_0)\| + \frac{Hm}{L}.$$

Hence:

$$\exp\bigl(-(x - x_0) L\bigr)\left(\|\alpha(x)\| + \frac{Hm}{L}\right) \leq \|\alpha(x_0)\| + \frac{Hm}{L}.$$

Multiply both sides by $\exp\bigl((x - x_0) L\bigr)$:

$$\|\alpha(x)\| + \frac{Hm}{L} \leq \exp\bigl((x - x_0) L\bigr)\left(\|\alpha(x_0)\| + \frac{Hm}{L}\right).$$

Subtract $\frac{Hm}{L}$ from both sides:

$$\|\alpha(x)\| \leq \exp\bigl((x - x_0) L\bigr)\|\alpha(x_0)\| + \frac{\exp\bigl((x - x_0) L\bigr) - 1}{L}\, Hm. \qquad \blacksquare$$

---

## Interpretation

- **Initial error amplification.** The initial error $\|y(x_0) - \widetilde{y}(x_0)\|$ is amplified by the factor $\exp((x - x_0)L)$, which grows exponentially with the length of the integration interval and the Lipschitz constant $L$. This reflects the inherent sensitivity of the ODE.

- **Accumulated truncation error.** The second term $\frac{\exp((x-x_0)L)-1}{L}\,Hm$ represents the accumulated effect of local truncation errors across all steps. It is proportional to the maximum stepsize $H$, which shows that the Euler method is **first-order convergent**: halving the stepsize roughly halves the global error.

- **Convergence (Theorem 213A).** If we consider a sequence of approximations with $H_n \to 0$ and initial errors $\|y(x_0) - \widetilde{y}_n(x_0)\| \to 0$, then both terms in the bound tend to zero, proving that the Euler method **converges**: $D_n = \|y(\bar{x}) - \widetilde{y}_n(\bar{x})\| \to 0$ as $n \to \infty$.
