from pathlib import Path
import json, shutil, hashlib
p=Path(__file__).resolve().parent
w=p.parent.parent
project=w/'project'
r=json.loads((p/'postbuild-result.json').read_text())
assert r['passed'] and r['source_bindings_unchanged']
a=json.loads((w/'evidence/partial-endpoint-audit-431-result.json').read_text())
assert a['passed'] and a['checked_endpoint_count']==103
dest=project/'docs/audit/proof-kernel-regression-repair-430'
assert not dest.exists()
dest.mkdir()
for f in p.iterdir():
    if f.suffix in ['.json','.md','.py','.lean','.patch']:
        shutil.copy2(f,dest/f.name)
for name in ['yz-target-kernel-benchmark-428','third-yz-target-kernel-benchmark-429']:
    q=dest/name;q.mkdir()
    for f in (w/'evidence'/name).iterdir():
        if f.suffix in ['.json','.py','.log']:
            shutil.copy2(f,q/f.name)
paragraph=('The two Weierstrass polynomial proofs have been restored to their original ring implementations after stock-kernel benchmarks found substantial performance regressions in the smaller grind proof terms. Both versions passed the pinned Lean kernel: the symmetric YZ theorem took 6.57 seconds / 0.492 GiB with ring versus 79.98 seconds / 12.285 GiB with grind; the third-addition YZ theorem took 5.27 seconds / 0.258 GiB versus 54.37 seconds / 8.575 GiB. Memory figures are sampled process high-water measurements, and concurrent work makes precise timing ratios indicative. Actual GoalRoot and all 13 current Comparator Solution roots passed build430; exact theorem types/universes, every Solution declaration axiom closure, all 103 original endpoints (audit431), and the unchanged original1207-file baseline passed. Independent interface coverage remains61/103. Historical optimized export416 and its ongoing comparator are preserved for their exact bytes; they do not describe the restored source or establish official acceptance. See docs/audit/proof-kernel-regression-repair-430/Review.md.')
for name in ['README.md','docs/MigrationStatus.md']:
    f=project/name;s=f.read_text();lines=s.splitlines();indexes=[i for i,line in enumerate(lines) if line.startswith('Two Weierstrass polynomial proofs now use smaller kernel proof terms')];assert len(indexes)==1;lines[indexes[0]]=paragraph;f.write_text('\n'.join(lines)+'\n')
files=[f for f in dest.rglob('*') if f.is_file()]
(p/'publish-docs-receipt.json').write_text(json.dumps({'files':{str(f.relative_to(project)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files},'root_count':len(json.loads((p/'build-result.json').read_text())['roots']),'full_endpoint_count':103,'official_acceptance':False},indent=2)+'\n')
print('Prepared',len(files),'audit files and current status corrections')
