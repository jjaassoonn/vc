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