# Local Rings and local ring homomorphisms

The mathematical result is the following: if $f : A\to R$ is a ring homomorphism from any ring $A$ to a local ring $R$ with maximal ideal $\mathfrak m$, then $f$ can be factorised as

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
A \arrow[r, "f"]\arrow[d, "\pi"'] & R \\
A_{f^{-1}\mathfrak m}\arrow[ru, "f'"']
\end{tikzcd}
\end{document}
```

with $f' : \frac{a}{b}\mapsto \frac{f(a)}{f(b)}$, since $f(b) \in \mathfrak m$, $f(b)$ is invertible.

Furthermore, if $g : A_{\mathfrak p}\to R$ is any local ring homomorphism such that $g\circ \pi: A\to A_{\mathfrak p}\to R=f$, then $\mathfrak p = f^{-1}\mathfrak m$ and $g = f'$. In another word $\operatorname{Hom}(A, R)\cong (\mathfrak p, \text{local ring homomorphism}~A_{\mathfrak p} \to R)$

# Implementation

We implement the data structure $(\mathfrak p, \text{local ring homomorphism}~A_{\mathfrak p} \to R)$ as $(\mathfrak p, M, \text{local ring homomorphism}~M\to R, M\cong A_{\mathfrak p})$, i.e. we are using any ring satisfying the universal property of localization, not just "the" localized ring at $\mathfrak p$:

```lean
structure point_local_ring_hom_pair :=
(pt : prime_spectrum A)
(localized_ring : Type u)
[comm_ring_localized_ring : comm_ring localized_ring]
[algebra_localized_ring : algebra A localized_ring]
[is_localization : is_localization.at_prime localized_ring pt.as_ideal]
(ring_hom_ : localized_ring →+* R)
[is_local_ring_hom_ : is_local_ring_hom ring_hom_]
```

But note that `point_local_ring_hom_pair` doesn't have a "correct" extensionality lemma as we need to compare `localized_ring` as well. The correct notion for "equality" of `point_local_ring_hom_pair` is

```lean
variables (P Q : point_local_ring_hom_pair A R)

structure equiv : Prop :=
(pt_eq : P.pt = Q.pt)
(ring_hom_eq : P.ring_hom_ 
    = Q.ring_hom_.comp (localized_ring_equiv_of_pt_eq pt_eq).to_ring_hom) 
```
