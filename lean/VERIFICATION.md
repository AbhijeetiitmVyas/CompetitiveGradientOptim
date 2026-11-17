# Verification record

Verified 2026-11-17 in a Linux cloud workspace.

- Lean: 4.19.0, commit `6caaee842e94`.
- mathlib: v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Command: `lake build`.
- Result: **passed**, exit code 0.
- `#print axioms CGO.energy_tends_to_zero`:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, or custom `axiom` declarations occur in the Lean source.
- All four proof files and the root `CGO` import target compiled.
- These are symbolic kernel-checked proofs, not numerical tests.

The formalization proves the scalar bilinear specialization and the general
fixed-step optimistic transformed-field residual rate described in README.
All four source modules and the root target compile. The entire paper has
**not** been verified. The general rate
`CGO.optimistic_competitive_average_rate` has the same three standard axioms
and no `sorryAx`.

## Environment note

Mathlib's precompiled dependency cache was used. Initial dependency downloads
hit a read-only default cache directory and later rate limiting; a workspace-local
cache and reduced download concurrency resolved these setup issues. The temporary
download-tool concurrency change was reverted before the final successful build.
No mathematical dependency source was modified.

## Source provenance

Official PMLR PDF SHA-256:
`081a4984e8126adecea5e593e48e832808b1bfaefc63d108e36226f281c621ee`.
PDF obtained from https://proceedings.mlr.press/v202/vyas23a/vyas23a.pdf.
The source paper is linked, not redistributed in this project.
