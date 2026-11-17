# CGO in Lean 4: bilinear convergence and a general oCGO rate

An incremental formalization of **Competitive Gradient Optimization**,
Abhijeet Vyas, Brian Bullins and Kamyar Azizzadenesheli, ICML 2023.

Source: https://proceedings.mlr.press/v202/vyas23a.html

## Verified results

- `CGO/Bilinear.lean`: Eq. (3) specialized to `f(x,y)=xy`, unique saddle,
  exact energy identity and geometric convergence when `0 < eta < 2*alpha`.
- `CGO/Extragradient.lean`: general real-inner-product extragradient energy
  identity, descent from a Minty sign condition and a Lipschitz bound, finite
  telescoping and an explicit fixed-step average squared-residual bound.
- `CGO/Skew.lean`: a finite-dimensional identity-plus-skew interaction is
  invertible; its inverse is nonexpansive. Invertibility is proved, not assumed.
- `CGO/TransformedField.lean`: state-dependent inverse interaction, a proved
  Lipschitz estimate, and a general optimistic competitive-gradient rate under
  the explicit conditions below.

## General rate: exact scope

Let `S(x)` be a real linear interaction with `<v,S(x)v>=0`, and set
`F(x)=(I+alpha*S(x))^(-1) g(x)`. The proof constructs the inverse. Assume:

- a finite-dimensional real inner product space;
- `g` is `Lg`-Lipschitz and bounded in norm by `M`;
- `||(S(y)-S(x))v|| <= LH*||x-y||*||v||`;
- `Lg,LH,M >= 0`;
- Minty condition `<F(x),x-p> >= 0` for every `x`;
- fixed `eta>0`, with `eta*L<1`, where `L=Lg+|alpha|*LH*M`;
- `z_(n+1)=z_n-eta*F(z_n-eta*F(z_n))`.

Then, for every positive integer N, Lean proves

```
(1/N) sum_{n<N} ||F(z_n)||^2
 <= ||z_0-p||^2 / (eta^2*(1-eta^2*L^2)) / N.
```

This is a **general fixed-step theorem with explicit safe constants**, not a
verbatim formalization of published Theorem 5.4. It does not claim convergence
of the iterates themselves. The paper's cross-Hessian block must still be
connected to `S(x)` and its derivative hypotheses to these analytic assumptions.
The global boundedness assumption is substantive and is not inferred silently.
No descent inequality or inverse existence is introduced as an axiom.

## Build

Requires Lean 4.19.0 and mathlib v4.19.0 (pinned manifest included):

```
lake update
lake exe cache get
lake build
```

The source includes axiom audits. Standard Lean foundations `propext`,
`Classical.choice`, `Quot.sound` are expected; `sorryAx` is not present.
See VERIFICATION.md and build.log for actual build status.

## Remaining paper formalization

The full Theorems 5.1–5.4 are **not yet verified**. Remaining work includes
Fréchet derivatives and Hessian blocks, matching constants/hypotheses, projected
updates, and any asserted iterate-convergence result. See STATUS.md and GENERAL_NOTES.md for the exact correspondence and remaining work.
