ru# Valuative Criterion

This repo is dedicated to show valuative criterion for universal-closedness, separatedness and properness.

## Preliminary Results
We need to establish some preliminary results first

### Local rings

Let <img src="https://i.upmath.me/svg/R" alt="R" /> be a local ring and <img src="https://i.upmath.me/svg/A" alt="A" /> be any ring and <img src="https://i.upmath.me/svg/%5Cphi%20%3A%20A%20%5Clongrightarrow%20R" alt="\phi : A \longrightarrow R" />, then <img src="https://i.upmath.me/svg/%5Cphi" alt="\phi" /> factors as

<img src="https://i.upmath.me/svg/%0A%5Cbegin%7Btikzcd%7D%0A%20%20%20A%20%5Carrow%7Br%7D%7B%5Cphi%7D%5Carrow%5Bd%2C%20%22%5Cpi%22'%5D%20%26%20R%20%5C%5C%0AA_%7B%5Cphi%5E%7B-1%7D%7B%5Cmathfrak%20m%7D%7D%20%5Carrow%5Bru%2C%20%22%5Cphi'%22'%5D%0A%5Cend%7Btikzcd%7D%0A" alt="
\begin{tikzcd}
   A \arrow{r}{\phi}\arrow[d, &quot;\pi&quot;'] &amp; R \\
A_{\phi^{-1}{\mathfrak m}} \arrow[ru, &quot;\phi'&quot;']
\end{tikzcd}
" />

then <img src="https://i.upmath.me/svg/%5Cmathfrak%20p%3D%5Cphi%5E%7B-1%7D(%5Cmathfrak%20m)" alt="\mathfrak p=\phi^{-1}(\mathfrak m)" /> and <img src="https://i.upmath.me/svg/f%20%3D%20%5Cphi'" alt="f = \phi'" />. This fact is recorded in [`about_local_rings.lean`](src/about_local_rings.lean#L235).

![](https://img.shields.io/bower/l/mi?style=flat-square)