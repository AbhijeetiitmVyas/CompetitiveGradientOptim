# Statement correspondence ledger

| Lean result | Paper relationship | Status boundary |
|---|---|---|
| `saddle_iff_origin` | Scalar example f(x,y)=xy | Exact saddle inequalities |
| `direction_solves_system` | Equation (3) | Scalar block-system identity |
| `energy_step` | Discrete CGO convergence mechanism | Exact scalar identity; no descent hypothesis assumed |
| `factor_nonneg`, `factor_lt_one` | Stable parameter region | Assumes 0 < eta < 2 alpha; entails alpha > 0 |
| `energy_iterate` | Geometric rate | Exact formula for every natural n |
| `energy_tends_to_zero` | Scalar bilinear convergence | Squared distance tends to zero; not general nonlinear theorem |
| `gda_factor` | CGO alpha=0 reduces to GDA | Exact factor 1+eta^2 |

## General extension

`Extragradient.lean` proves the exact energy identity, local descent,
telescoping, and explicit fixed-step average squared-field bound in any real
inner product space. `Skew.lean` proves inverse existence and nonexpansiveness
in finite dimension. `TransformedField.lean` proves the Lipschitz bound and
combines these into `optimistic_competitive_average_rate`.

The general rate uses `L=Lg+|alpha| LH M` and a constant positive stepsize.
It is not presented as identical to all variable-step cases or the exact
constants of published Theorem 5.4. It is a squared-residual bound, not an
iterate-convergence theorem.

## Not formalized yet

- Identification of the derivatives of f(x,y)=xy through Lean's derivative APIs.
- Identification of the objective's cross-Hessian block with the abstract skew
  operator, including the differential calculus and regularity hypotheses.
- Theorems 5.1, 5.2, 5.3, or 5.4 in their full published form.
- General projected/proximal domains, or trajectory invariance in a restricted
  domain where local rather than global analytic assumptions apply.
- Convergence of the full iterate sequence for the general transformed field.
- Empirical experiments, GAN applications, or an executable numerical solver.

No custom axioms or placeholders bridge these gaps.
