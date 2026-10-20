# Migration checkpoint — 2026-10-21 (Asia/Shanghai)

**Complete GoalRoot build and all103 original endpoint type/axiom checks passed. Full-paper independent Palomar verification remains incomplete.**

The repository is public by explicit owner authorization. Human author and responsible maintainer: Jue Ding. Original code is Apache-2.0, with third-party licenses and attribution preserved.

Lean4.35.0-rc2 and Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55 remain pinned. The original Lean4.33.1 delivery is a separate artifact. Read-only baseline344 checked all1207 original delivery files and found no changes.

## Migration evidence

- Actual project `lake build +GoalRoot` passed in build342 (exit0;165.26seconds for the final incremental run;12845 total build tasks including cached dependencies). JointSourceIntegrationR0267, FullSourceIntegrationR0268 and GoalRoot all built. Every bound project Proof source remained unchanged during the run. Receipt and source hashes: `audit/full-root-build-342/`.
- Joint endpoint audit343 passed all103 original exact types, in one environment, with only standard `propext`, `Classical.choice`, `Quot.sound` axiom closures. No changed inputs or axiom issues. The frozen13 requirements and103 endpoints were retained. Evidence: `audit/partial-endpoint-audit-343-result.json` and its probe/log/selection. The historical filename prefix and `complete_scope:false` mean this is type/axiom migration evidence, not full independent Palomar semantic verification.
- Final compatibility repairs preserve mathematical signatures and actual maps. They concern private declaration visibility, imported private proof visibility, Discrete.Hom API changes, explicit existing groupoid category parameters, and one finite local instance-search budget. Isolated complete-file/exact-type/axiom evidence is archived under audit/; actual project builds341/342 validate integration. Earlier failed attempts remain in the local evidence directory.
- The runner uses available96 logical CPUs for Lake scheduling, with one shared Lake writer and bounded independent checks. Real dependencies limit available parallelism.

## Independent Palomar evidence

- accepted-017 early certificate: official full preflight39455278417 passed at12f83ea with comparator-early.json. This covers only that endpoint.
- accepted-050 formal-cover constancy lemma: official full preflight39461300608 passed at2bd02cf. Ordinary submission86n83vqdajt2 passed Palomar verification39466419289. Its semantic review is available privately; no registration has occurred.
- Main-and-components: official39461299032 remains running at2bd02cf;39 complete endpoints plus supporting results and a main interface omitting the original FormalIdentity field.
- Stronger complete-main: official39469688913 remains running at35c8d4a;43 targets covering40 complete original endpoints, including original accepted-037 FormalIdentity for the same B/U. Its Challenge/Solution compiled in actual build314. This configuration needs its own passing report before ordinary intake.
- Full independent geometric interfaces, including the scheme-discriminant interface, remain incomplete. The40-endpoint main configuration does not cover the remaining63 original endpoints.

Local main265 three-kernel attempt02 timed out after3600seconds: con-ron and NanoDa accepted, while Lean default had not completed and had not rejected. A bounded7200second default-only continuation uses the identical frozen export. This is not a complete Comparator pass; official results remain separate.

See Coverage.md and PalomarPreflight.md for exact scope and run links. No full-paper semantic approval or permanent registration is claimed.
