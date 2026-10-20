# Third-party sources

The 2,713 library modules vendored under Proof/Definitions, Proof/Theorems and Proof/P2M were copied from the local fermats-last-theorem checkout used by the original delivery. Its origin is https://github.com/anthropics/fermats-last-theorem and its recorded HEAD is aa2d8b34692b16c70f699536de0d8e75b9a3e9ef. The local checkout may contain additional modifications; SourceProvenance.json records the actual source hashes before conversion. The HEAD is not asserted to reproduce all copied bytes by itself.

The upstream Apache-2.0 license is retained in fermats-last-theorem-LICENSE.txt, and existing source headers are retained. This repository adds Lean module headers, explicit exposure and version compatibility changes; the submitted repository commit identifies the resulting modified sources.

Mathlib is fetched by Lake at the exact revision in lake-manifest.json and lakefile.toml. It and its dependencies retain their own licenses and attribution. Jue Ding is the human author and responsible maintainer of the arithmetic theta project; this does not claim sole authorship of third-party library contributions.
