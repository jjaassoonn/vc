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
then $\mathfrak p = \phi^{-1}\mathfrak m$ and $f = \phi'$. This fact is recorded in [`about_local_rings.lean`](src/about_local_rings.lean#L235).

![](https://img.shields.io/bower/l/mi?style=flat-square)