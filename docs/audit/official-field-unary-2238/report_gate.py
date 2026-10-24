import hashlib, json, re
import yaml
from pathlib import PurePosixPath
REPO = "WeThinkIn/arithmetic-theta-lean4-palomar"
PIPELINE = "7a08c1da8e0558d330b9b3c244896c175d373303"
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

class Refused(Exception):
    """Only fixed, nonsecret messages should be passed to this exception."""

def require(value, message):
    if not value:
        raise Refused(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def repo_path(s):
    p = PurePosixPath(s)
    require(bool(s) and not p.is_absolute() and '..' not in p.parts and str(p) == s,
            'Invalid repository-relative path')
    return s

def report_gate(report, request, git_blob, expected_challenge_imports, run):
    """Pure validation except the injected read-only Git blob accessor."""
    require(report.get('status') == 'pass', 'Mechanical report is not pass')
    require(report.get('phase') == 'verification' and report.get('stage') == 'complete',
            'Mechanical report is not a complete full verification')
    require(not report.get('errors'), 'Mechanical report contains errors')
    source = report.get('source', {})
    require(source.get('repository') == request['repository'] and source.get('commit') == request['commit'],
            'Mechanical source repository/commit mismatch')
    require(source.get('project_path', '') in ('', '.'), 'Only the root Lake project is supported')
    requested = report.get('submission', {}).get('requested_paths', {})
    require(requested.get('project_path', '') in ('', '.'), 'Requested project is not repository root')
    require(requested.get('comparator_config_path') == request['comparator_config_path'],
            'Requested Comparator path mismatch')
    require(requested.get('formalization_metadata_path') == request['formalization_metadata_path'],
            'Requested metadata path mismatch')
    require(report.get('submission', {}).get('authorization', {}).get('relationship') == 'maintainer',
            'Mechanical authorization relationship mismatch')
    require(report.get('execution_profile') == 'palomar-standard-v1', 'Unexpected execution profile')
    require(report.get('verification_profile', {}).get('id') == 'palomar-standard-v1',
            'Verification profile is not standard-v1')
    cfg_data = git_blob(request['comparator_config_path'])
    cfg = json.loads(cfg_data)
    for field, path in [('comparator', request['comparator_config_path']),
                        ('formalization', request['formalization_metadata_path'])]:
        entry = report.get(field, {})
        require(entry.get('path') == path and entry.get('sha256') == digest(git_blob(path)),
                'Config or metadata source hash mismatch')
    for field, key in [('challenge', 'challenge_module'), ('solution', 'solution_module')]:
        entry = report.get(field, {})
        require(entry.get('module') == cfg.get(key), 'Challenge/Solution module mismatch')
        path = repo_path(entry.get('path', ''))
        require(entry.get('sha256') == digest(git_blob(path)), 'Challenge/Solution source hash mismatch')
    for key in ['theorem_names', 'definition_names', 'permitted_axioms']:
        require(report.get('comparator', {}).get(key, []) == cfg.get(key, []),
                'Comparator declaration or axiom list mismatch')
    require(set(cfg.get('permitted_axioms', [])) <= STANDARD_AXIOMS, 'Nonstandard permitted axiom')
    challenge = report.get('challenge', {})
    require(challenge.get('trust_level') == 'high' and not challenge.get('untrusted_sources'),
            'Challenge provenance is not high trust')
    require(expected_challenge_imports == ['Lean.Meta.Match.Match', 'Mathlib'], 'Unexpected audited source imports')
    require(challenge.get('direct_imports') == expected_challenge_imports, 'Challenge imports differ from pinned source header')
    require(0 < challenge.get('lines', 1001) <= 1000 and 0 < challenge.get('bytes', 102401) <= 102400,
            'Challenge exceeds official bounds')
    source_req = report.get('source_requirements', {})
    require(source_req.get('module_required') is True and source_req.get('maximum_lines') == 10000
            and source_req.get('header_parser') == 'lean --deps-json', 'Complete source scan not established')
    log = report.get('comparator_log_tail', '')
    for text in ['nanoda kernel accepts the solution',
                 'Lean default kernel accepts the solution', 'Your solution is okay!']:
        require(text in log, 'Mandatory Lean and NanoDa result not established')
    accepted = report.get('kernels', [])
    require(isinstance(accepted, list) and all(isinstance(x, dict) for x in accepted),
            'Malformed accepted-kernel evidence')
    names = [x.get('name') for x in accepted]
    require(names.count('nanoda') == 1 and len(names) == len(set(names)),
            'Accepted NanoDa evidence missing or ambiguous')
    attempts = report.get('kernel_attempts', [])
    require(isinstance(attempts, list) and len(attempts) == 1 and isinstance(attempts[0], dict)
            and attempts[0].get('name') == 'con-ron', 'Separate Con-ron replay evidence missing')
    replay = attempts[0]
    if replay.get('status') == 'accepted':
        require(replay.get('reason') == 'complete' and replay.get('exit_code') == 0
                and names.count('con-ron') == 1, 'Inconsistent Con-ron acceptance')
    elif replay.get('status') == 'declined':
        reason, code = replay.get('reason'), replay.get('exit_code')
        require((reason == 'capacity' and code is None)
                or (reason == 'unsupported-inductive' and code == 2)
                or (reason == 'fuel-exhausted' and code == 3),
                'Unrecognized Con-ron support/capacity decline')
        require('con-ron' not in names and any('con-ron declined' in x for x in report.get('warnings', [])),
                'Con-ron decline must be explicitly reported, not counted as acceptance')
    else:
        raise Refused('Con-ron rejected or failed without a recognized decline')
    url = report.get('workflow_url', '')
    m = re.fullmatch(r'https://github.com/' + re.escape(REPO) + r'/actions/runs/([0-9]+)', url)
    require(m is not None, 'Unexpected report workflow URL')
    require(run.get('id') == int(m.group(1)) and run.get('head_sha') == request['commit']
            and run.get('status') == 'completed' and run.get('conclusion') == 'success',
            'Official run identity or completion mismatch')
    require(run.get('event') == 'workflow_dispatch' and run.get('path') == '.github/workflows/palomar-preflight.yml',
            'Unexpected official dispatch workflow')
    require(run.get('display_title') == 'Palomar full preflight at ' + request['commit'],
            'Full verification dispatch mode is not established')
    require(run.get('referenced_workflows') == [{'path': 'PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@' + PIPELINE, 'sha': PIPELINE}],
            'Executed reusable workflow differs from pinned pipeline')
    workflow = yaml.load(git_blob('.github/workflows/palomar-preflight.yml'), Loader=yaml.BaseLoader)
    call = workflow['jobs']['palomar-preflight']
    require(call['uses'] == 'PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@' + PIPELINE
            and call['with']['pipeline_commit'] == PIPELINE
            and call['with']['execution_profile'] == 'palomar-standard-v1', 'Official pipeline pin mismatch')
    require(call['with']['repository'] == '${{ github.repository }}' and call['with']['commit'] == '${{ github.sha }}',
            'Workflow source binding mismatch')
    require(workflow.get('run-name') == "Palomar ${{ inputs.verification_mode || 'full' }} preflight at ${{ github.sha }}",
            'Workflow mode display binding mismatch')
    mode = call['with'].get('mode')
    require(mode == "${{ inputs.verification_mode || 'full' }}", 'Unexpected workflow mode selector')
    selector = workflow['on']['workflow_dispatch']['inputs']['verification_mode']
    require(selector.get('default') == 'full' and selector.get('type') == 'choice'
            and selector.get('options') == ['full', 'preflight'], 'Unexpected allowed verification modes')
    lake = report.get('lakefile', {})
    require(lake.get('path') == 'lakefile.toml' and lake.get('sha256') == digest(git_blob('lakefile.toml')),
            'Lake configuration binding mismatch')
    return m.group(1)
