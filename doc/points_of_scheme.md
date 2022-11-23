---
date created: 2022-11-23 02:34
---

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

## Non-affine cases
If $X$ is not affine and $\psi : \mathcal{O}_{X,x}\to R$ is a local ring homomorphism, let $x\in U$ be an affine open neighbourhood of $x$, then $\psi' : \mathcal{O}_{X\mid_U, x}\to R$ is still local and, since $X\mid_U$ is an affine scheme, $\psi'$ is induced by some $\Psi:\operatorname{Spec} R \to X\mid_ U$, hence we get a $\Psi':\operatorname{Spec}R\to X\mid_U\;\hookrightarrow X$. 

This is independent of the choice of affine open neighbourhood $U$. Let's first consider the case where $x\in U\subseteq V$ are two affine open neighbourhoods. Then the following diagram

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage{amssymb}
\begin{document}
\begin{tikzcd}
\operatorname{Spec} R \arrow[r, "\Psi_V"] \arrow[d, "\Psi_U"']& X\mid_V \arrow[r, hook] & X \\
X\mid_U \arrow[ru, hook]
\end{tikzcd}
\end{document}
```

commutes. Because $\Psi_V$ is uniquely determined by $\Gamma(X, V)_{i(x)}\cong\mathcal{O}_{X\mid_V, x}\to R$ and $\Psi_U$ by $\Gamma(X, U)_{i(x)}\cong\mathcal{O}_{X\mid_U, x} \to R$, where we denotes both $X\mid_U\cong \operatorname{Spec}\Gamma(X, U)$ and $X\mid_V\cong \operatorname{Spec}\Gamma(X, V)$ by $i$. The restriction map $\mathrm{res}: \Gamma(X, V)\to \Gamma(X, U)$ induces a ring homomorphism $\Gamma(X, V)_{i(x)}\to\Gamma(X, U)_{i(x)}$ by $\frac{a}{b}\mapsto \frac{\mathrm{res}(a)}{b}$. Then the following triangle commutes:

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage{amssymb}
\begin{document}
\begin{tikzcd}
\Gamma(X, V)_{i(x)}\arrow[d, "\mathrm{res}"]\arrow[r, dash, "\cong"] & \mathcal{O}_{X\mid_V, x} \arrow[d, dash, "\cong"]\arrow[r, "\psi_V"] & R \\
\Gamma(X, U)_{i(x)}\arrow[r, dash, "\cong"]& \mathcal{O}_{X\mid_U, x} \arrow[ru, "\psi_U"]& 
\end{tikzcd}
\end{document}
```

Finally, if $U, V$ are two arbitrary affine open neighbourhoods of $x$, then since $X\mid_{U \cap V}$ is a scheme, there is an affine neightbourhoods $W\subseteq U\cap V$, then the following diagram commutes, hence proving independence of choice.

```tikz
\usepackage{tikz-cd}
\usepackage{amsfonts}
\usepackage{amsmath}
\usepackage{amssymb}
\begin{document}
\begin{tikzcd}
\operatorname{Spec}R \arrow[rd, "\Psi'_W"]\arrow[rrd,  bend left = 30, "\Psi'_U"] \arrow[rdd, bend right = 30, "\Psi'_V"] \\
& X\mid_{W} \arrow[d, hook] \arrow[r, hook]& X\mid_{U} \arrow[d, hook]\\
& X\mid_{V} \arrow[r, hook] & X
\end{tikzcd}
\end{document}
```

## Bijection
Now that we have a map $F: \{(x, \text{local} ~\psi:\mathcal{O}_{X, x}\to R)\}\to \operatorname{Hom}(\operatorname{Spec}R, X)$, we prove that this map is surjective. Any $\alpha:\operatorname{Spec}R\to X$ can be factorized as $\operatorname{Spec}R\stackrel{\alpha'}{\to} X\mid_V\;\hookrightarrow X$ where $V$ is some affine open neighbourhoods of $\alpha(\mathfrak m)$ with $\mathfrak m$ as the maximal ideal of $R$. Then consider $(\alpha(\mathfrak m), \psi : \mathcal{O}_{X, \alpha(\mathfrak m)}\to R)$ induced by $\mathcal{O}_{X, \alpha(\mathfrak m)} \cong \mathcal{O}_{X\mid V, \alpha(\mathfrak m)}\cong\mathcal{O}_{\operatorname{Spec}\Gamma(X, V), i(\alpha(\mathfrak{m}))}\cong\Gamma(X, V)_{i(\alpha(\mathfrak m))}\to R$ coming from $\Gamma(X, V)\to R$ under adjunction $\Gamma \dashv \operatorname{Spec}$ and $\alpha'$, this pair is sent to $\alpha$ under $F$ (probably).

If $\phi : \mathcal{O}_{X, x}\to R$ and $\psi : \mathcal{O}_{X, y} \to R$ are two local ring homomorphisms such that $F(\phi) = F(\psi)=(\alpha : \operatorname{Spec} R\to X) = \operatorname{Spec} R \stackrel{\alpha'}{\to} \operatorname{Spec}(\Gamma(X, V))\hookrightarrow X$ where $\alpha(\mathfrak m)\in V$ is affine open. Then $\alpha'$ is uniquely determined by some local ring homomorphism $\Gamma(X, V)_{\mathfrak p}\to R$ where $\mathfrak p$ is a prime ideal of $\Gamma(X, V)$. Then $x = y = i^{-1}(\mathfrak p)$ where $i:X\mid_V\cong \operatorname{Spec}\Gamma(X, V)$ and $\phi = \psi$ as ring homomorphisms $\Gamma(X, V)_{\mathfrak p}\cong \mathcal{O}_{X\mid_V,i^{-1}\mathfrak p}\cong \mathcal{O}_{X, x} \to R$.
