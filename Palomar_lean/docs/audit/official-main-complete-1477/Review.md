# Official main-result mechanical verification

The complete Palomar reusable preflight **passed** for commit
`57c6842d63e4860c7978dbc32307380415bcce1c`, configuration
`comparator-main-complete.json`, and metadata
`submissions/main-complete/formalization.yaml`.

- [Official run 39709205904](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39709205904)
- [Unmodified official mechanical report](mechanical-report.json)
- [Exact endpoint scope and report checksum](scope.json)

The report records successful stock Lean and NanoDa checks and a successful
separate Conron replay. Conron accepted 158,728 declarations with exit code 0.
The Challenge contains 969 physical lines and 62,283 bytes, imports Mathlib,
and has high-trust provenance with no untrusted sources. The full verification
finished with status `pass`, stage `complete`, and no report errors.

The submitted proof uses Lean **4.35.0-rc2**. The official pipeline separately
pins its Conron checker to the binary distributed with Lean **4.36.0-rc1**;
this checker selection does not change the proof's submitted Lean toolchain.
The reusable pipeline revision is
`7a08c1da8e0558d330b9b3c244896c175d373303`.

The 43 selected targets recover **40 original complete endpoints**. Together
with the previously accepted formal-cover endpoint accepted-050, the recorded
official mechanical results cover **41 distinct original endpoints** at their
respective immutable revisions. The earlier accepted-017 result is already
included in the main-result scope and is not counted twice.

These mechanical results do not establish semantic acceptance of all 103
original endpoints or permanent registration. The local original-endpoint
audit and the 99/103 prepared independent-interface count remain separate
measures. This documentation commit does not transfer the official result
to a different source revision.

Ordinary intake for the passed main-result revision succeeded with submission
ID `q0fcj6z7esrd`. Its service verification is
[run 39738618013](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39738618013).
No private review or access credential is included here. Permanent registration
requires the responsible maintainer's decision after reviewing the actual report.
