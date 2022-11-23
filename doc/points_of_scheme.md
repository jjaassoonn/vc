# [Points of Scheme](../src/points_of_scheme.lean)

Let $R$ be a local ring and $X$ be a scheme. The goal is to show that

$$
\operatorname{Hom}_{\mathfrak Sch}(\operatorname{Spec} R, X) \cong\{(x, \phi)\mid x \in X, \phi: \mathcal{O}_{X,x}\to R\text{ is local}\}.
$$

## Affine cases

If $i: X\cong\operatorname{Spec}\Gamma(X)$ is affine and $x \in X$, then $\mathcal{O}_{X,x}\cong \Gamma(X)_{i(x)}$. We note that

$$
\{(x, \phi)\mid x \in X, \phi: \mathcal{O}_{X,x}\to R\text{ is local}\} \cong \{(\mathfrak{p}, \psi)\mid \mathfrak{p}\in \operatorname{Spec}\Gamma(X), \psi : \Gamma(X)_{\mathfrak p}\to R\text{ is local}\},
$$

and

$$
\operatorname{Hom}_{\mathfrak{Sch}}(\operatorname{Spec} R, X)\cong \operatorname{Hom}_{\mathfrak{CRng}}(\Gamma(X), R)
$$

Since we know that the set of ring homomorphisms $A \to R$ into a local ring $R$ is in bijection to pairs of the form $(\mathfrak p\in\operatorname{Spec} A, \text{local ring homomorphisms } \psi: A_{\mathfrak p}\to R)$ from [`about_local_rings`](about_local_rings.md), we conclude the affine cases. See `point_local_ring_hom_pair_equiv` and `Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair` in [`points_of_scheme.lean`](../src/points_of_scheme.lean).

So the bijection is roughly this (modulo a lot of head-scratching on type-theory hell). Given a scheme morphism $\alpha: \operatorname{Spec} R\to X\cong\operatorname{Spec}\Gamma(X)$, there is a ring homomorphism $\beta: \Gamma(X) \to R$ by $\Gamma \dashv\operatorname{Spec}$. Then there is this diagram:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\begin{document}
\begin{tikzcd}
{\Gamma(X)} \arrow[r, "\beta"] \arrow[d, "\pi"] & R \\
\Gamma(X)_{\beta^{-1}\mathfrak{m}} \arrow[ru, "\beta'"] \arrow[d, dash, "\cong"']& \\
\mathcal{O}_{X,i^{-1}(\beta^{-1}\mathfrak{m})} \arrow[ruu, "\beta'"']
\end{tikzcd}
\end{document}
```

where $\mathfrak m$ is the unique maximal ideal of $R$, so the pair corresponding to $\alpha$ is $(i^{-1}(\beta^{-1}\mathfrak m), \beta'')$ . Conversely, if $(x, \psi : \mathcal{O}_{X, x}\to R)$ is a local ring homomorphism, then
```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage{amssymb}
\begin{document}
\begin{tikzcd}
\mathcal{O}_{X, x} \arrow[r, "\psi~\mathrm{local}"] \ar[d, dash, "\cong"]& R \\
\Gamma(X)_{i(x)} \arrow[ru, "\psi'~\mathrm{local}"'] & \\
\Gamma(X) \arrow[u, "a\mapsto\frac a 1"'] \arrow[uur, bend right=60]
\end{tikzcd}.
\end{document}
```
This gives us $\operatorname{Spec} R\to \operatorname{\Gamma(X)}\cong X$ needed.
