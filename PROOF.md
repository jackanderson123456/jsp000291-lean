# Distinct sums of exponential floors

Let $a_n=\lfloor t\alpha^n\rfloor$ for $n=0,1,2,\ldots$ and $t,\alpha>0$. A finite sum may use each **integer value** at most once. Call the pair good if every sufficiently large integer occurs as a sum. We give an explicit countable union of parameter intervals for the good pairs and an algebraic example below the golden ratio in which every floor is even. The interval description supplies finite certificates for good pairs. There is no uniform time bound here for deciding that a coefficient lies outside the union.

## The parameter intervals

For a fixed $1<\alpha<2$, enumerate all $k,u\ge0$ and integer words $b=(b_0,\ldots,b_{k+1})\ge0$. Keep a word when all the integers in $[u,u+b_{k+1})$ are sums of subsets of the **set** $\{b_0,\ldots,b_k\}$. This test uses integers only. For every retained word include $[L,U)$, where

$$
L=\max\left\{
\frac{2}{\alpha^k(\alpha-1)},\frac{2}{\alpha^k(2-\alpha)},
\max_{0\le i\le k+1}\frac{b_i}{\alpha^i}\right\},\qquad
U=\min_{0\le i\le k+1}\frac{b_i+1}{\alpha^i}.
$$

The union of these intervals is precisely the set of good coefficients $t$. In particular every good coefficient lies in a right-hand interval $[t,T)$ of good coefficients, even when an early $t\alpha^i$ is an integer.

To prove sufficiency, choose a retained word containing $t$ in its interval. Its digits are the actual floors. Write $x_j=t\alpha^j$. For all $j\ge k$, both $x_j(\alpha-1)$ and $x_j(2-\alpha)$ are at least two. The floor inequalities $a_j\le x_j<a_j+1$ give $a_j<a_{j+1}\le2a_j$. Suppose the terms with index below $n$ represent $[u,u+a_n)$ for $n\ge k+1$. Adding the fresh value $a_n$ gives the adjacent interval $[u+a_n,u+2a_n)$. Their union covers $[u,u+a_{n+1})$. Iterate and use $a_n\to\infty$.

Conversely, let $u$ be a completeness threshold. Choose $k$ so large that $a_k$ exceeds every earlier term, $a_k+u\le a_{k+1}$, $a_{k+1}+u\le2a_k$, and both real margin inequalities at $k$ hold. Such indices exist because the two margins tend to infinity. For $u\le m<a_{k+1}$, no term of index at least $k+1$ fits into a representation of $m$. For $a_{k+1}\le m<u+a_{k+1}$, the inequalities give $u\le m-a_k<a_k$. Represent that remainder using values below $a_k$ and then add $a_k$. Thus the actual prefix passes the finite test. Solving its floor conditions and the two margins for $t$ gives exactly the endpoints above.

## The boundary bases

For $0<\alpha\le1$ the set of distinct values is finite. For $\alpha\ge2$, the floors satisfy $a_{n+1}\ge2a_n$. Put $S_n=\sum_{i<n} a_i$. If $S_n+1<a_n$, then $S_n+1$ is missing, and the inequality propagates to the next index since $S_{n+1}=S_n+a_n$. The resulting missing integers grow without bound. Hence completeness requires $a_n\le S_n+1$ at every index.

Let $j$ be the first index with positive floor. Necessarily $a_j=S_j+1=1$. If $a_n=S_n+1$, then $2a_n\le a_{n+1}\le S_{n+1}+1=2a_n$. Induction gives $a_{j+l}=2^l$ for every $l\ge0$. For $\alpha>2$ this contradicts the fact that $t\alpha^n(\alpha-2)>2$ eventually. For $\alpha=2$ the floor inequalities give $1\le t2^j<1+2^{-l}$ for every $l$, so $t=2^{-j}$. Conversely every such coefficient supplies the whole sequence of binary powers and every natural number has a binary representation.

## When the summands have distinct indices

Graham's sequence convention allows two equal entries at different indices to be used together. For $1<\alpha<2$, use the same endpoints $L,U$. In the integer test select subsets of $\{0,\ldots,k\}$ and sum their indexed entries $b_i$. The two interval arguments still apply. An index $n$ is fresh among all indices below it, including when the corresponding values coincide.

At base one, every entry equals $\lfloor t\rfloor$. All sufficiently large numbers are representable precisely for $1\le t<2$. Indeed, a number dividing every sufficiently large integer divides two consecutive integers. When $0<\alpha<1$, all sufficiently late terms are zero and even the sum of every positive occurrence is finite. At bases at least two, all positive entries are strictly increasing. Omitting zero entries then gives the same representations as in the distinct-value convention. Thus base two contributes exactly $t=2^{-j}$, and larger bases contribute nothing.

For the frequently used indexing $n=1,2,\ldots$, substitute $t\alpha$ for the zero-based coefficient everywhere. In particular the exceptional coefficients at base two become $t=2^{-(j+1)}$ for that indexing.

## An explicit counterexample below the golden ratio

Set

$$
Q(Y)=Y^5-6Y^3-Y^2+7Y+1,\qquad H(Y)=2Y^4+4Y^3-2Y^2-6Y-1.
$$

Let $y_0<\cdots<y_4$ be the five real roots of $Q$. For each $i$ define

$$
W_i=H(y_i)\prod_{j\ne i}\frac{2-y_j}{y_i-y_j},\qquad
\alpha=\frac{y_4+\sqrt{y_4^2-4}}{2},\qquad t=\frac{2}{5} W_4\alpha^{12}.
$$

Then $1.59<\alpha<1.6<(1+\sqrt5)/2$ and **every** $\lfloor t\alpha^n\rfloor$ is even. In particular arbitrarily large odd positive integers are missing. The base is approximately $1.5970050092$ and the coefficient is approximately $4734.18$.

Here are the rational enclosures used below. Row $i$ locates $10^6 y_i$ strictly between the displayed integer and its successor. The last column encloses $W_i$.

| $i$ | Lower integer | Enclosure of $W_i$ |
|---|---:|---:|
| 0 | −1938938 | $(-0.20351,-0.20349)$ |
| 1 | −1349121 | $(0.05923,0.05925)$ |
| 2 | −142428 | $(0.06632,0.06635)$ |
| 3 | 1207308 | $(0.07387,0.07390)$ |
| 4 | 2223177 | $(43.0038,43.0043)$ |

For each interval $Q$ has opposite signs at its endpoints. The intervals are disjoint and $Q$ has degree five. Substituting the intervals in the product for $W_i$ using rational interval arithmetic gives $2\sum_{i<4}|W_i|<0.81$ and $42<W_4<44$. Since $x+x^{-1}$ increases for $x>1$, the interval for $y_4$ gives the bounds on $\alpha$. The accompanying script verifies these inequalities by integer and rational arithmetic.

Define $D_0(Y)=2,D_1(Y)=Y,D_{n+2}(Y)=Y D_{n+1}(Y)-D_n(Y)$. They satisfy $D_n(z+z^{-1})=z^n+z^{-n}$, in particular $D_n(2)=2$. For $-2\le y\le2$, write $y=2\cos\theta$, giving $|D_n(y)|\le2$. Divide $H D_n$ by the monic integer polynomial $Q$, obtaining integral remainder $R_n$ of degree below five. Its value $s_n=R_n(2)$ is an integer congruent to $2H(2)=86\equiv1\pmod 5$, since $Q(2)=-5$. By Lagrange interpolation at the five roots,

$$
s_n=\sum_{i=0}^4 W_i D_n(y_i).
$$

For $n\ge12$,

$$
|s_n-W_4\alpha^n|\le 2\sum_{i<4}|W_i|+W_4\alpha^{-n}
<0.81+44/(1.59)^{12}<1.
$$

Writing $s_n=5q+1$ therefore gives $5q<W_4\alpha^n<5q+2$. Multiplication by $2/5$ gives floor $2q$. The shift by 12 in $t$ applies this bound from exponent zero onwards.

## Sources and scope

The distinct-value, zero-based conventions are specified in the formal statement. The even-floor counterexample holds under either summation convention and either starting index. [Erdős Problem 349](https://www.erdosproblems.com/349) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/ErdosProblems/349.lean)

Interval propagation is related to Lemma 5 of [Wouter van Doorn, 2026](https://arxiv.org/abs/2602.23394). [Jesse Geneson, Theorem 9, 2026](https://arxiv.org/abs/2609.25107) already refuted the golden-ratio conjecture, building on work of [Artūras Dubickas, 2006](https://doi.org/10.1017/S0017089506003090). Credit for the prior disproof belongs to that work. The construction above gives its own polynomials, coefficient and uniform arithmetic certificate.
