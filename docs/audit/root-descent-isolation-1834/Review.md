# Root-definition import isolation

Generic square-root test definitions now live in `RootTestDefinitionsR0196`.
The arithmetic metaplectic definitions retain their existing public declarations
through an explicit import. Root descent and square-isometry modules import the
generic definitions directly; `SharpFamilyRootLevelR0196` explicitly imports the
arithmetic definitions it uses. This removes unnecessary arithmetic imports from
the two split-divisor verification scopes without changing their statements.

The affected build covers 122 modules, including the joint `GoalRoot` entry point.
The declaration audit compares 2,949 original declarations, including 1,040 data
declarations, with no differences in types, universe parameters, data bodies or
checked metadata. Three regenerated equation declarations are matched to their
original owners with exact proof-body equality. Proposition dependencies remain
within the three permitted logical axioms.

The unchanged frozen probe also checks all 103 original endpoint statements and
their axiom dependencies. Both complete public split interfaces pass strict
structural and axiom comparison for all 33 configured targets each. The target
lists, Challenge and Solution source files, 13 requirements, and paper PDF are
unchanged. Three independent kernels, stock Lean, Con-ron and NanoDa, accepted
both complete 33-target split exports. Receipts in this directory record the
exact verification scope.

Independent kernel replay and official verification are separate gates. These
local build and comparison results do not establish whole-paper Palomar acceptance.
AI contribution disclosure is documented in `docs/AIContributions.md` and the
automation metadata; human author and responsible maintainer remains Jue Ding.
