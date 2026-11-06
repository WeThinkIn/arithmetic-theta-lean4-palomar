# Official ordinary main-result verification

Ordinary submission `q0fcj6z7esrd` passed the official full mechanical verifier
at source commit `57c6842d63e4860c7978dbc32307380415bcce1c`, using
`comparator-main-complete.json` and `submissions/main-complete/formalization.yaml`.
The 43 configured targets cover 40 original endpoints. This repeats the same
scope as the successful main-result preflight; it adds no endpoint coverage.

[Official run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39738618013)
· [Mechanical report](mechanical-report.json) · [Exact scope and binding checks](receipt.json)

Lean 4.35.0-rc2's default kernel and NanoDa accepted the solution. The official
service's pinned Con-ron checker from Lean 4.36.0-rc1 also accepted, checking
158,728 declarations. The latter is the service's independent checker version,
not a replacement for the submitted Lean compiler.

The service used its approved `palomar-namespace-16x32-v1` profile (16 effective
CPUs and 33,716,862,976 memory bytes). The Challenge received high-trust provenance
and meets mandatory bounds: 969 lines and 62,283 bytes. Its only warning concerns
the preferred smaller review surface.

The submitted source revision, config/metadata and Challenge/Solution hashes,
selected declarations, permitted axioms and service profile digest have been
checked against immutable source and official pipeline records. The report
SHA-256 is `d4064e340bedc4419452ec8457e916840eabd9ca881d378a23d206313440f320`.
The service workflow revision `ad5db9e7ff8b17523d73aeb244aaeabcde810c64` is
separate from the submitted proof revision.

The mechanical pass does not establish whole-paper semantic acceptance or
registration. Both remain separate, and this report applies to its immutable
submitted revision, not automatically to later changes.
