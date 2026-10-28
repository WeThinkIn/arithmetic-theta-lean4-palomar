# Maintenance policy

`main` is the sole maintained branch. Integrate work into main and run new Palomar preflights from main. Former development branches are retired; their exact tips are preserved under `archive/20261028/` tags and in main history. See [the consolidation record](docs/maintenance/main-consolidation-20261028.md).

Keep `local-reproduction/` and its related dependency inputs, release tag, release assets and reproduction documentation unchanged during Palomar development. This is the independent Lean 4.33.1 reproduction target. The top-level Palomar edition uses Lean 4.35.0-rc2 and has its own Lake configuration.

An old successful report only applies to the commit it verified. Merging a branch does not transfer Palomar approval to the new main commit. Use GitHub standard runners (`ubuntu-24.04`, `palomar-standard-v1`) for new verification work.
