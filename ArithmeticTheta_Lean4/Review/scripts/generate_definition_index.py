#!/usr/bin/env python3
"""Generate the exhaustive reading index from measured names and Lean metadata.

Docstrings and source positions come from definition_index_metadata.lean. No
mathematical description is inferred for an undocumented declaration.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re


CONSERVATIVE = 'ArithmeticThetaReview.Geometry.conservative_image_review'
MODULARITY = 'ArithmeticThetaReview.Geometry.cyclotomic_modularity_review'
OLD_CONSERVATIVE = 'ArithmeticThetaFullSourceR0268.conservative_image_consumer'
OLD_MODULARITY = 'ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity'

GROUPS = [
    ('review', 'The new review interfaces', {
        'ReviewGeometryDefinitions', 'ReviewNormalizationDefinitions'}),
    ('moduli', 'Elliptic families, level structures and the actual metaplectic stack', {
        'ActualLevelDefinitionsR0208', 'ActualMetaplecticGroupoidR0206',
        'ActualMetaplecticPullbackR0206', 'FullLevelCoverDefinitionsR0175',
        'LegendreLevelAtlasDefinitionsR0176', 'LocalWeierstrassDefinitionsR0203',
        'MetaplecticComparisonDefinitionsR0206', 'MetaplecticStackDefinitionsR0207',
        'RootDescentDefinitionsR0197', 'RootStackDefinitionsR0198',
        'SchemeLevelDefinitionsR0204', 'StackLevelDefinitionsR0199'}),
    ('normalization', 'Tate curves, differentials and Hodge normalization', {
        'BoundaryHodgeDefinitionsR0182', 'CommonHalfHodgeDefinitionsR0185',
        'CompactifiedDifferentialDefinitionsR0145', 'CubicModelDefinitionsR0144',
        'GlobalNormalizedDifferentialR0145', 'OpenHodgeDescentDefinitionsR0180',
        'RelativeDiscriminantDefinitionsR0171', 'RelativeHodgePowerBaseChangeR0171',
        'RelativeKatoDefinitionsR0169', 'RelativeWeierstrassPresentationR0174',
        'SchemeHodgeDefinitionsR0205', 'SimultaneousUnaryRootsDefinitionsR0187',
        'TateCuspDefinitionsR0181', 'TateSeriesDefinitions'}),
    ('sheaves', 'Sheaves, tensor powers and section operations', {
        'ActualSheafTensor', 'CoverComparisonDefinitions', 'NormalizedSectionDefinitions',
        'PullbackTensor', 'PullbackTensorDefinitions', 'PullbackUnit',
        'SquareLineComparisonDefinitionsR0192', 'TensorPowerDefinitions'}),
    ('series', 'Lattice theta series and image statements', {
        'ArithmeticFieldDefinitionsR0231', 'CompactUnaryDefinitionsR0183',
        'FieldImageDefinitionsR0233', 'LatticeGlobalSectionsDefinitionsR0188',
        'UnaryThetaProduct'}),
    ('arithmetic', 'Arithmetic inputs, cutoffs and elimination', {
        'ConservativeKernelDefinitionsR0189', 'ConservativeMatrixKernelR0189',
        'CyclotomicMatrixModularityR0239', 'EarlyCertificateAssembly',
        'EliminationAlgorithm', 'EnumerationAlgorithm', 'GlobalizationDefinitions',
        'IntegrationDefinitions', 'OrthogonalAlgorithm',
        'OrthogonalConsumerDefinitionsR0127', 'SharpKernelDefinitionsR0195'}),
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def clean(text):
    return re.sub(r'\s+', ' ', text).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--metadata', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.report.read_text())
    metadata = {r['name']: r for r in json.loads(args.metadata.read_text())}
    reports = {r['target']: r for r in report['reports']}
    conservative = set(reports[CONSERVATIVE]['custom_definitions'])
    modularity = set(reports[MODULARITY]['custom_definitions'])
    names = conservative | modularity
    if names != set(metadata):
        raise ValueError('Documentation metadata does not exactly cover the two measured closures')
    nodes = {}
    for target in (CONSERVATIVE, MODULARITY):
        nodes.update({r['name']: r for r in reports[target]['nodes']})
    binding = {r['module']: r for r in report['bindings']}
    for module in {nodes[name]['module'] for name in names}:
        if digest(Path(binding[module]['source'])) != binding[module]['source_sha256']:
            raise ValueError('Measured source changed before indexing: ' + module)
    groups = []
    assigned = set()
    for key, title, modules in GROUPS:
        entries = sorted(n for n in names if nodes[n]['module'] in modules)
        if assigned.intersection(entries):
            raise ValueError('Category assignment overlaps')
        assigned.update(entries)
        groups.append((key, title, entries))
    if assigned != names:
        raise ValueError('Uncategorized definitions: ' + repr(sorted(names - assigned)))
    ordered = [name for _, _, entries in groups for name in entries]
    ids = {name: f'D{i + 1:03}' for i, name in enumerate(ordered)}

    def link(name):
        return f'[{ids[name]}](#{ids[name].lower()})'

    def next_dependencies(name):
        pending = list(nodes[name]['dependencies'])
        found, seen = set(), {name}
        while pending:
            dependency = pending.pop()
            if dependency in seen:
                continue
            seen.add(dependency)
            if dependency in names:
                found.add(dependency)
            elif dependency in nodes:
                pending.extend(nodes[dependency]['dependencies'])
        return sorted(found, key=lambda n: ids[n])

    def source_info(name):
        node = nodes[name]
        source = Path(binding[node['module']]['source'])
        base = 'Lean/' if node['module'].startswith('Review') else '../Lean/'
        target = base + node['module'].replace('.', '/') + '.lean'
        line = metadata[name]['line']
        generated = bool(re.search(r'\.match_\d+$', name))
        if line is None and generated:
            line = metadata.get(name.rsplit('.', 1)[0], {}).get('line')
        if line:
            target += f'#L{line}'
        lines = source.read_text().splitlines()
        header = lines[line - 1].strip() if line and line <= len(lines) else None
        return target, generated, header

    lines = [
        '# Definition index for the two review main theorems', '',
        'This index covers **every counted custom definition** in the union of the two',
        'review statements, using the elaborated Lean environment recorded in the',
        '[definition dependency report](verification/DefinitionDependencyReport.json).',
        'It is grouped by mathematical role so that the 12 new interfaces can be read',
        'first, followed by the retained family, normalization, sheaf, series and',
        'arithmetic definitions. Each entry links to its actual source declaration.', '',
        '**C** means [`conservative_image_review`](Lean/ReviewMainTheorems.lean);',
        '**M** means [`cyclotomic_modularity_review`](Lean/ReviewMainTheorems.lean).',
        'These tags record membership in the respective recursive statement closure.', '',
        '| Statement | Original definitions | Review definitions | Net reduction |',
        '| --- | ---: | ---: | ---: |',
    ]
    for label, old, new in [('Conservative kernel/image/modularity', OLD_CONSERVATIVE, CONSERVATIVE),
                             ('Cyclotomic sharp modularity', OLD_MODULARITY, MODULARITY)]:
        a, b = reports[old]['custom_definition_count'], reports[new]['custom_definition_count']
        lines.append(f'| {label} | {a} | {b} | {a-b} ({(a-b)/a:.2%}) |')
    lines += [
        '', f'The union has **{len(names)} definitions**; definitions used by both statements are',
        'listed only once. The original sharp matrix-kernel statement remains at 23',
        'definitions under the same convention.', '',
        'This is a reduction in dependencies needed to **read the statements**, not a',
        'compression of the proofs or their transitive proof dependencies. The review',
        'theorems are proved projections of the richer original construction theorems.',
        'They do not have identical complete types to those original witness theorems.',
        'The original theorems, construction data, sources and audits remain available.',
        'The adapter preserves the actual curve, structural scalar map, half line, disk,',
        'frame, sections, compact square and normalized Hodge generator. A single family',
        'is still chosen before the universal quantifier over admissible cutoffs.', '',
        'The count follows definition bodies and all structure fields, including proof-field',
        'predicates. Abbreviations and opaque non-proof definitions therefore do not hide',
        'their dependencies. Theorem proof bodies and external library bodies are outside',
        'this statement-reading metric. See the',
        '[precise convention and regression tests](scripts/DEFINITION_METRIC.md).',
        'The count includes six **public named generated matcher',
        'helpers** (`match_1`), which are explicitly labeled below and linked to the',
        'definitions that generate them. These names are not classified as compiler-internal',
        'by Lean, unlike the internal names excluded from the count. They are not six',
        'additional handwritten concepts; no second adjusted headline count is used.', '',
        'Quoted descriptions below are the declarations\' actual Lean docstrings.',
        'Historical wording in a quoted comment is not a new validation claim. Where a',
        'docstring is absent, the entry says so and quotes the actual declaration header;',
        'no mathematical description has been guessed from its name. “Next definitions”',
        'means the next counted custom declarations after traversing projection and',
        'constructor bookkeeping; the complete direct dependency graph is in the JSON.', '',
        '## What moved behind the construction bridges', '',
        'The conservative statement no longer requires 128 of its original definitions',
        'and adds 12 review definitions. The cyclotomic statement removes 141 and adds',
        'the same 12. In both cases the statement no longer unfolds the following',
        'construction-specific records and functions:', '',
        '- `ArithmeticThetaArithmeticFieldR0231.MatrixData` and `MatrixData.root`;',
        '- `ArithmeticThetaCompactModularityR0209.CompactRoot`;',
        '- `ArithmeticThetaLevelCompactificationR0179.LevelData`;',
        '- `ArithmeticThetaActualLevelR0208.Provider`, `FiniteEtaleLevel`, `UsesFiber`,',
        '  `canonicalMap` and `testRoot`;',
        '- `ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.Provider`;',
        '- `ArithmeticThetaSimultaneousUnaryR0187.RootCover`.', '',
        'These remain part of the original proofs. Their public review replacements',
        'retain actual elliptic families, marked arrows and pullbacks, the metaplectic',
        'stack and its coherence, finite étale representability, compact regular sections,',
        'the specified Tate normalization and the complete `q = t^L` expansion.',
        'The conservative statement still includes the original conservative-cutoff',
        'specification, so its arithmetic decomposition/indexing dependencies remain.', '',
        '## Navigation', '',
        '| Group | Definitions | In C | In M |',
        '| --- | ---: | ---: | ---: |',
    ]
    for key, title, entries in groups:
        lines.append(f'| [{title}](#{key}) | {len(entries)} | '
                     f'{len(set(entries)&conservative)} | {len(set(entries)&modularity)} |')
    for key, title, entries in groups:
        lines += ['', f'<a id="{key}"></a>', '', f'## {title}', '']
        if key == 'review':
            lines += ['Read these 12 interfaces first. Their source docstrings specify which',
                      'actual maps, squares, frames and compatibility conditions they retain.', '']
        for name in entries:
            node = nodes[name]
            target, generated, header = source_info(name)
            membership = ', '.join(flag for flag, group in [('C', conservative), ('M', modularity)]
                                   if name in group)
            lines += [f'<a id="{ids[name].lower()}"></a>', '',
                      f'**{ids[name]} — [`{name}`]({target})**', '',
                      f'Used by **{membership}** · `{node["kind"]}` · module `{node["module"]}`.', '']
            doc = metadata[name]['docstring']
            if doc:
                lines += ['> ' + clean(doc), '']
            elif generated:
                parent = name.rsplit('.', 1)[0]
                lines += [f'Lean-generated pattern-matching helper for `{parent}`. It has no',
                          'separate handwritten declaration or docstring; the source link opens',
                          'its generating definition. It is included in the technical count.', '']
            else:
                lines += ['No declaration docstring is recorded in Lean.']
                if header:
                    lines += ['', 'Actual source header:', '', '```lean', header, '```']
                lines.append('')
            dependencies = next_dependencies(name)
            if dependencies:
                lines += ['Next definitions: ' + ', '.join(link(n) for n in dependencies) + '.', '']
            else:
                lines += ['No further counted custom definition is reached before the external-library boundary.', '']
    lines += ['## Generation record', '',
              f'- Measured report SHA-256: `{digest(args.report)}`.',
              f'- Lean declaration metadata SHA-256: `{digest(args.metadata)}`.',
              '- Generated with `scripts/generate_definition_index.py`; declaration metadata',
              '  is read from the compiled environment by `scripts/definition_index_metadata.lean`.',
              '- Every indexed source hash was checked against the measured report before generation.',
              '- These documentation tools do not build or alter proof declarations.', '']
    args.output.write_text('\n'.join(lines))
    print(f'Wrote {args.output}: {len(names)} definitions in {len(groups)} groups')


if __name__ == '__main__':
    main()
