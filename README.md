# Valuative Criterion

This repo is dedicated to show valuative criterion for universal-closedness, separatedness and properness.

## Preliminary Results
We need to establish some preliminary results first

### Local rings

Let $R$ be a local ring and $A$ be any ring and $\phi : A \longrightarrow R$, then $\phi$ factors as
<!-- https://q.uiver.app/?q=WzAsMyxbMCwwLCJBIl0sWzEsMCwiUiJdLFswLDEsIkFfe1xccGhpXnstMX0oXFxtYXRoZnJhayBtKX0iXSxbMCwxLCJcXHBoaSJdLFswLDIsIlxccGkiLDJdLFsyLDEsIlxccGhpJyIsMl1d -->
<iframe class="quiver-embed" src="https://q.uiver.app/?q=WzAsMyxbMCwwLCJBIl0sWzEsMCwiUiJdLFswLDEsIkFfe1xccGhpXnstMX0oXFxtYXRoZnJhayBtKX0iXSxbMCwxLCJcXHBoaSJdLFswLDIsIlxccGkiLDJdLFsyLDEsIlxccGhpJyIsMl1d&embed" width="334" height="304" style="border-radius: 8px; border: none;"></iframe>

where $\mathfrak m$ is the maximal ideal of $R$, $\pi$ the descending morphism and $\phi'$ defined as $\frac a b\mapsto \phi(a)\phi(b)^{-1}$. Note that $\phi'$ is a local ring homomorphism. Furthermore, this factorization is unique in the sense that for any prime ideal $\mathfrak p \subseteq A$ and a local ring homomorphism $f : A_{\mathfrak p}\longrightarrow R$ such that the following commutes
<!-- https://q.uiver.app/?q=WzAsMyxbMCwwLCJBIl0sWzEsMCwiUiJdLFswLDEsIkFfe1xcbWF0aGZyYWsgcH0iXSxbMCwxLCJcXHBoaSJdLFswLDIsIlxccGkiLDJdLFsyLDEsImYiLDJdXQ== -->
<iframe class="quiver-embed" src="https://q.uiver.app/?q=WzAsMyxbMCwwLCJBIl0sWzEsMCwiUiJdLFswLDEsIkFfe1xcbWF0aGZyYWsgcH0iXSxbMCwxLCJcXHBoaSJdLFswLDIsIlxccGkiLDJdLFsyLDEsImYiLDJdXQ==&embed" width="304" height="304" style="border-radius: 8px; border: none;"></iframe>

then $\mathfrak p=\phi^{-1}(\mathfrak m)$ and $f = \phi'$. This fact is recorded in [`about_local_rings.lean`](src/about_local_rings.lean#L235).

![](https://img.shields.io/bower/l/mi?style=flat-square)