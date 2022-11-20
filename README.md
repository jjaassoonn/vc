# Valuative Criterion

This repo is dedicated to show valuative criterion for universal-closedness, separatedness and properness.

## Preliminary Results
We need to establish some preliminary results first

### Local rings

Let $R$ be a local ring and $A$ be any ring and $\phi : A \longrightarrow R$, then $\phi$ factors as

$$
A \stackrel{\pi}{\longrightarrow} A_{\phi^{-1}\mathfrak m} \stackrel{\phi'}{\longrightarrow} R
$$

Where $\pi : a \mapsto \frac a 1$, $\mathfrak m$ is the maximal ideal and $\phi' : \frac a b \mapsto \phi(a)\phi(b)^{-1}$.
Note that $\phi'$ is a local ring homomorphism. Furthermore, for any prime ideal $\mathfrak p$ and local ring homomorphism $f : A_{\mathfrak p}\longrightarrow R$ such that $\phi$ factors as

$$
A \stackrel{\pi}{\longrightarrow} A_{\mathfrak p} \stackrel{f}{\longrightarrow} R
$$

then $\mathfrak p = \phi^{-1}\mathfrak m$ and $f = \phi'$. This fact is recorded in [`about_local_rings.lean`](src/about_local_rings.lean#L235). In another word, we have the following bijection:

$$
\mathrm{Hom}(A, R) \cong \{(\mathfrak p, f : A_{\mathfrak p}\to R)\mid \mathfrak p\in\mathrm{Spec} A, f\text{ is a local ring homomorphism}\}.
$$
If we apply this to an affine scheme $X$, then $$
\mathrm{Hom}(\mathrm{Spec} R, X)\cong \mathrm{Hom}(\Gamma(X), R)\cong\{(\mathfrak p \in \mathrm{Spec}\,\Gamma(X), \Gamma(X)_{\mathfrak p}\to R)\}\cong\{(x \in X, \mathcal{O}_{X, x}\to R)\}.
$$

For an arbitrary scheme $X$, for any $\alpha : \mathrm{Spec} R\to X$, $\alpha$ is uniquely determined by $\mathrm{Spec} R \to V$ where $V$ is an affine subscheme of $X$ containing $\alpha(\mathfrak m)$  which in turn is uniquely determined by, according to the bijection in the affine cases by a pair $(x \in V, \mathcal{O}_{V, x}\to R)$; but since $\mathcal{O}_{V, x}\cong \mathcal{O}_{X, x}$, any pair $(x \in V, \mathcal{O}_{V, x}\to R)$ is uniquely determined by an $(x \in X, \mathcal{O}_{X, x})$. Hence, we have proved that scheme morphisms $\mathrm{Spec} R\to X$ is uniquely determined by $(x\in X, \mathcal O_{X, x}\to R)$. This is [01J6](https://stacks.math.columbia.edu/tag/01J6) from stack project.

<div align='center'>

![license](https://img.shields.io/bower/l/mi) ![line count](https://img.shields.io/tokei/lines/github/jjaassoonn/vc)
