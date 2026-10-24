from pathlib import Path
import datetime, fcntl, hashlib, importlib.util, json, os, traceback

R = Path(__file__).resolve().parent
E = R.parent
W = E.parent
P = E / 'remaining-five-render-publication-2398/project'
C = E / 'formal-cover-current-render-2416/formal-cover'
CACHE = E / 'phase-free-key-cache-resolution-build-2200'
OLD = E / 'direct-hodge-combined-build-831'
BIN = W / 'toolchains/lean-4.35.0-rc2-linux/bin'
PRE = E / 'strict-export-precheck-537'
spec = importlib.util.spec_from_file_location('process2418', E / 'isogeny-render-repair-strict-1984/supervisor.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
os.chdir(W)

def load(p):
    return json.loads(p.read_text())

def sha(p):
    return m.sha(Path(p))

def save(p, data):
    p.write_text(json.dumps(data, indent=2) + '\n')

def main():
    assert not (R / 'running.json').exists()
    save(R / 'running.json', {'pid': os.getpid(), 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'formal-cover'})
    B = E / 'formal-cover-current-full-audit-2418'
    prior = load(B / 'build-receipt.json')
    assert prior['passed'] and prior['cached_dependencies'] == 243
    process = load(B / 'solution-build-process.json')
    assert process['exit_code'] == 0 and process['stop_reason'] is None
    bindings = load(B / 'bindings-before.json')
    assert all(sha(p) == h for p, h in bindings.items())
    assert sha(P / 'FormalCoverSolution.lean') == prior['solution_sha256']
    assert sha(B / 'FormalCoverSolution.olean') == prior['solution_olean_sha256']
    for p in B.glob('FormalCoverSolution.olean*'):
        bindings[str(p)] = sha(p)
    sources = load(E / 'formal-cover-current-build-plan-2417/source-bindings.json')
    cfg = load(B / 'comparator.json')
    lean_path = str(R) + ':' + load(B / 'environment.json')['lean_path']
    env = dict(os.environ, LEAN_PATH=lean_path, LEAN_NUM_THREADS='1', PATH=str(BIN) + os.pathsep + os.environ.get('PATH', ''))
    save(R / 'environment.json', {'lean_path': lean_path, 'source_bound_cached_dependencies': 243, 'reused_solution_build': str(B)})
    save(R / 'comparator.json', cfg)
    save(R / 'build-reuse.json', {'passed': True, 'source': str(B / 'build-receipt.json'), 'recompiled': False, 'cached_dependencies': 243})
    save(R / 'bindings-before.json', bindings)
    m.r = R
    def run(label, args, timeout=1200, output=None):
        save(R / 'progress.json', {'stage': label, 'scope': 'formal-cover'})
        result = m.execute(label, ['/home/miniconda3/envs/lean4/bin/python', '/home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py', *args], timeout, env, stdout_path=output)
        assert result['exit_code'] == 0 and result['stop_reason'] is None, label
    original = load(P / 'challenges/formal-cover/Scope.json')['source_obligation']
    canonical = next(x for x in load(P / 'docs/SourceObligations.json') if x['id'] == 'accepted-050')
    assert original['declaration'] == canonical['declaration'] and original['type'] == canonical['type']
    prefix = 'module\npublic import FormalCoverSolution\nimport Lean\n@[expose] public section\nopen AlgebraicGeometry CategoryTheory Opposite\nset_option autoImplicit false\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\nnoncomputable section\nuniverse u\nnamespace ArithmeticThetaFormalCoverRecovery2418\n'
    (R / 'StatementPreflight.lean').write_text(prefix + 'def OriginalStatement : Prop :=\n  ' + original['type'] + '\nend ArithmeticThetaFormalCoverRecovery2418\n')
    run('statement-preflight', [str(BIN / 'lean'), '-j1', '-M16384', str(R / 'StatementPreflight.lean')])
    proof = ''' := by
  intro k _ X f _ _ _ _ _
  obtain ⟨rho, hrho⟩ := ArithmeticThetaPalomarFormalCover275.arbitrary_formal_cover_constant k X f
  refine ⟨ArithmeticThetaPalomarFormalCover275.Bridges.toRestrictions k X f rho, ?_⟩
  intro C hC v hv hn
  exact hrho (ArithmeticThetaPalomarFormalCover275.Bridges.fromCover k X f C) hC v hv hn
end ArithmeticThetaFormalCoverRecovery2418
#print axioms ArithmeticThetaFormalCoverRecovery2418.recover_original_050
'''
    (R / 'FormalCoverRecovery2418.lean').write_text(prefix + 'theorem recover_original_050 :\n  ' + original['type'] + proof)
    run('original-recovery-proof', [str(BIN / 'lean'), '-j1', '-M16384', '-o', str(R / 'FormalCoverRecovery2418.olean'), str(R / 'FormalCoverRecovery2418.lean')])
    template = E / 'remaining-four-full-audit-continuation-2395/component-hodge-degree/OriginalAudit.lean'
    audit = template.read_text().replace('import all ComponentHodgeDegreeSolution', 'import all FormalCoverRecovery2418').replace('historical-thirteen-publication-2370/project', 'remaining-five-render-publication-2398/project').replace('accepted-031', 'accepted-050').replace('ArithmeticThetaPalomarHodge495.recover_original_031', 'ArithmeticThetaFormalCoverRecovery2418.recover_original_050').replace(str(template.parent / 'audit.json'), str(R / 'audit.json')).replace('ORIGINAL_ENDPOINTS_EXACT_TYPE_UNIVERSE_AXIOM_PASS', 'ORIGINAL_ENDPOINTS_DEFINITIONAL_TYPE_UNIVERSE_AXIOM_PASS')
    (R / 'OriginalAudit.lean').write_text(audit)
    (R / 'RecoveryEquality.lean').write_text('module\nimport all FormalCoverRecovery2418\nset_option maxRecDepth 8192\nexample : ArithmeticThetaFormalCoverRecovery2418.recover_original_050 = ' + original['declaration'] + ' := by rfl\n')
    holes_template = E / 'remaining-four-full-audit-continuation-2395/component-hodge-degree/TargetHoleAudit.lean'
    holes = holes_template.read_text().replace('ComponentHodgeDegreeChallenge', 'FormalCoverChallenge').replace(str(E / 'remaining-four-full-audit-continuation-2395/component-hodge-degree/comparator.json'), str(R / 'comparator.json')).replace(str(E / 'remaining-five-matcher-render-2382/component-hodge-degree'), str(C))
    (R / 'TargetHoleAudit.lean').write_text(holes)
    for label in ['OriginalAudit', 'RecoveryEquality', 'TargetHoleAudit']:
        run(label, [str(BIN / 'lean'), '-j1', '-M16384', str(R / (label + '.lean'))])
    assert 'DIRECT_PROPOSITION_HOLES 1; DEFINITION_HOLES 0; LITERAL_HOLES 1' in (R / 'TargetHoleAudit.log').read_text()
    lock = (W / 'tools/structural-comparison.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX)
    template_dir = E / 'isogeny-render-cache-name-repair-1982'
    diagnostic = (template_dir / 'Diagnostic.lean').read_text().replace(str(template_dir), str(R)).replace('IsogenyHalfLineSolution', 'FormalCoverSolution').replace(str(R / 'IsogenyHalfLineChallenge.olean'), str(C / 'FormalCoverChallenge.olean'))
    (R / 'Diagnostic.lean').write_text(diagnostic)
    run('shared-declarations', [str(BIN / 'lean'), '-j1', '-M16384', str(R / 'Diagnostic.lean')])
    assert not load(R / 'differences.json')['mismatches']
    assert m.memory_available() > 48 * 1024**3
    names = list(dict.fromkeys(['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] + cfg['theorem_names'] + cfg.get('definition_names', []) + cfg['permitted_axioms'] + load(PRE / 'primitives.json')))
    exports = {}
    for side in ['challenge', 'solution']:
        p = R / (side + '.ndjson')
        run(side + '-export', [str(BIN / 'leanexport'), cfg[side + '_module'], '--', *names], 1800, p)
        exports[side] = {'bytes': p.stat().st_size, 'sha256': sha(p)}
        bindings[str(p)] = exports[side]['sha256']
    save(R / 'exports.json', exports)
    run('strict', [str(PRE / 'Precheck'), str(R / 'comparator.json'), str(PRE / 'primitives.json'), str(R / 'challenge.ndjson'), str(R / 'solution.ndjson')], 1800)
    assert all(x in (R / 'strict.log').read_text() for x in ['TRUSTED_STRUCTURAL_COMPARISON_PASS', 'TRUSTED_AXIOM_CLOSURE_PASS'])
    for p in list(R.glob('*.lean')) + list(R.glob('*.olean*')) + [R / 'audit.json', R / 'differences.json']:
        bindings[str(p)] = sha(p)
    assert all(sha(p) == h for p, h in bindings.items())
    save(R / 'bindings.json', bindings)
    save(R / 'receipt.json', {'passed': True, 'scope': 'formal-cover', 'targets': 1, 'original_endpoint_ids': ['accepted-050'],
        'original_recovered_through_checked_structure_bridges': True, 'original_type_and_axiom_audit': load(R / 'audit.json'),
        'cached_dependencies': len(sources), 'full_strict_and_standard_axioms_passed': True, 'definition_holes': 0,
        'bindings_unchanged': True, 'challenge_source_unchanged': True, 'official_acceptance_claimed': False})

if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        save(R / 'error.json', {'type': type(exc).__name__, 'message': str(exc), 'traceback': traceback.format_exc()})
        raise
