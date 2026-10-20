from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent;w=p.parent.parent;b=w/'evidence/phase-free-key-package-466'
source=(b/'Challenge.lean').read_text();lines=source.splitlines()
remove=set()
def remove_block(start,end):
    a=source.index(start);z=source.index(end,a)
    lo=source[:a].count('\n')+1;hi=source[:z].count('\n')
    remove.update(range(lo,hi+1))
remove_block('theorem decompose_mk (','end Engine')
remove_block('section QuotGradingDef','section SubmoduleVersion')
remove_block('theorem decompose_quotGradingSubmodule_mk_apply','end SubmoduleVersion')
unused=json.loads((b/'DependencyProbe-check-01.log').read_text())
extra_names={
 'HomogeneousIdealQuotientGrading.pieceHom_surjective',
 'ArithmeticThetaFourTorsion.splitCurve','ArithmeticThetaFourTorsion.rootExpression',
 'ArithmeticThetaFourTorsion.generatorS','ArithmeticThetaFourTorsion.generatorT2',
 'ArithmeticThetaLegendreComparisonR0177.chartScalar',
 'WeierstrassProjModel.RelativeGroupLaw.idPoint','WeierstrassProjModel.RelativeGroupLaw.schemeNsmul',
 'ArithmeticThetaPalomarKey466.generator','AlgebraicGeometry.Scheme.Modules.tensor',
 'SheafOfModules.symmetricCategory','AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory',
 'AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed','AlgebraicGeometry.Scheme.Modules.symmetricCategory',
 'AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify',
 'SheafOfModules.tensorUnit_eq','AlgebraicGeometry.Scheme.Modules.tensorUnit_eq',
 'PresheafOfModules.InternalHom.naturality','PresheafOfModules.ihomFunctor_obj','PresheafOfModules.ihomFunctor_map',
 'PresheafOfModules.InternalHom.restrict_app','PresheafOfModules.InternalHom.presheaf_map_apply',
 'PresheafOfModules.InternalHom.postcomp_app','PresheafOfModules.ihomMap_app_val',
 'ArithmeticThetaTensorPower.tensorProductSection',
}
for r in unused:
    if r['name'] in extra_names:
        assert not r['needed'];remove.update(range(r['start'],r['end']+1))
rows=json.loads((p/'ProofSurfaceProbe-check-01.log').read_text())
replacements={}
def proof_delimiter(body):
    depth=0;i=0
    while i<len(body):
        ch=body[i]
        if ch in '([{':depth+=1
        elif ch in ')]}':depth-=1
        if depth==0:
            if body[i:i+2]==':=':return i
            if body[i:i+5]=='where' and (i==0 or body[i-1].isspace()) and (i+5==len(body) or body[i+5].isspace()):return i
        i+=1
    raise ValueError('No top-level proof delimiter')
for r in rows:
    if not r['proof'] or r['start'] is None:continue
    a,z=r['start'],r['end'];head=lines[a-1]
    if a in remove:continue
    m=re.search(r'\b(?:theorem|lemma|instance)\s+([\w\'.]+)',head)
    if not m or not r['name'].endswith('.'+m[1]):continue
    body='\n'.join(lines[a-1:z])
    if 'sorry' in body or z-a<2:continue
    # All selected declarations are proposition-valued according to Lean,
    # and the source prefix is retained verbatim up to its proof delimiter.
    prefix=body[:proof_delimiter(body)]
    assert prefix.strip()
    replacement=prefix.rstrip()+' := by sorry'
    replacements[a]=(z,replacement,r['name'])
result=[];i=1
while i<=len(lines):
    if i in remove:i+=1
    elif i in replacements:
        z,value,_=replacements[i];result.extend(value.splitlines());i=z+1
    else:result.append(lines[i-1]);i+=1
text='\n'.join(result)+'\n'
(p/'Challenge.proof-surface.lean.txt').write_text(text)
# Join only continuation lines of non-layout expression bodies, up to140 chars.
# No tokens change; Lean compilation and semantic-body checks validate elaboration.
out=[];i=0
starts=re.compile(r'^(?:@\[[^\]]+\]\s*)?(?:(?:noncomputable|private|local|protected)\s+)*(?:def|abbrev|theorem|lemma|instance)\b')
while i<len(result):
    line=result[i];i+=1
    if starts.match(line):
        while ':=' not in line and not re.search(r'\bwhere\s*$',line) and i<len(result) and result[i].startswith('  '):
            line+=' '+result[i].strip();i+=1
        if ':=' in line:
            rhs=line.split(':=',1)[1]
            if not re.search(r'\b(by|do|where|let|match)\b',rhs):
                body=[]
                while i<len(result) and result[i].startswith('  '):body.append(result[i]);i+=1
                if not any(re.search(r'\b(by|do|where|let|match)\b',l) or l.lstrip().startswith('|') for l in body):
                    for l in body:
                        if len(line)+1+len(l.strip())>140:out.append(line);line=l
                        else:line+=' '+l.strip()
                else:
                    out.append(line);out.extend(body);continue
    out.append(line)
packed=[];i=0
while i<len(out):
    line=out[i];i+=1
    # A declaration's long forall type may start at column zero in the source.
    if re.match(r'^theorem \w+\s*:\s*$',line) and i<len(out) and out[i].startswith('∀ '):
        line+=' '+out[i];i+=1
    if line.endswith(':= by') and i<len(out) and out[i].strip() in ['sorry','rfl','infer_instance']:
        line+=' '+out[i].strip();i+=1
    elif line.endswith(':=') and i<len(out) and out[i].strip()=='by sorry':
        line+=' by sorry';i+=1
    packed.append(line)
out=packed
joined='\n'.join(out)+'\n'
assert re.sub(r'\s+','',text)==re.sub(r'\s+','',joined)
docs='''/-! Full original053/054 key and naturality, with actual theta ideal, dual and evaluation.
The37 selected support/main propositions are proof obligations, not extra assumptions.
All semantic definition bodies and original statements are checked against Solution.
See challenges/phase-free-key/SourceMap.json for original definitions and recovery bridges. -/
'''
joined=joined.replace('public import Mathlib\n','public import Mathlib\n'+docs,1)
out=joined.splitlines()
(p/'Challenge.lean').write_text(joined)
(p/'Solution.lean').write_bytes((b/'Solution.lean').read_bytes())
cfg=json.loads((b/'comparator.json').read_text());cfg['theorem_names'] += [r[2] for r in replacements.values()]
(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
receipt={'original_source_sha256':hashlib.sha256(source.encode()).hexdigest(),'proof_probe_sha256':hashlib.sha256((p/'ProofSurfaceProbe-check-01.log').read_bytes()).hexdigest(),'removed_original_lines':sorted(remove),'replacements':[{'start':a,'end':z,'name':n,'replacement':v} for a,(z,v,n) in replacements.items()],'body_line_joining_changes_tokens':False,'stats':{'original_lines':len(lines),'proof_surface_lines':len(result),'joined_lines':len(out),'bytes':len(joined.encode())}}
(p/'transformation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'proof_targets_added':len(replacements),'stats':receipt['stats']}))
