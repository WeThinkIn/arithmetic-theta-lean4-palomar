from pathlib import Path
import re,json,hashlib,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;b=p.parent/'component-discriminant-package-509';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
ob=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-073');typ=ob['type']
newtyp=typ.replace('ArithmeticThetaComponentDegreeR0184.IsCompactD2','ArithmeticThetaPalomarD2_509.ComponentDegree.IsCompactD2').replace('ArithmeticThetaComponentDegreeR0184.restrict','ArithmeticThetaPalomarD2_509.ComponentDegree.restrict')
marker='namespace ArithmeticThetaPalomarD2_509\ntheorem componentDiscriminantDivisor'
for n in ['Challenge','Solution']:
 s=read(b/(n+'.lean'));s=s[:s.rindex(marker)];s=s.replace('public import ComponentDiscriminantDivisorR0184','public import SplitDiscriminantDivisorR0239')
 body='sorry' if n=='Challenge' else 'simpa only [ArithmeticThetaPalomarD2_509.compactD2_iff_original, ArithmeticThetaPalomarD2_509.restrict_eq_original] using '+ob['declaration']
 s+='namespace ArithmeticThetaPalomarSplit515\ntheorem splitComponentDiscriminantDivisor : '+newtyp+' := by\n  '+body+'\n'
 if n=='Solution':s+='theorem recover_original_073 : '+typ+' := by\n  simpa only [ArithmeticThetaPalomarD2_509.compactD2_iff_original, ArithmeticThetaPalomarD2_509.restrict_eq_original] using splitComponentDiscriminantDivisor\n'
 s+='end ArithmeticThetaPalomarSplit515\n';(p/(n+'.lean')).write_text(s)
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-1]='ArithmeticThetaPalomarSplit515.splitComponentDiscriminantDivisor';(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
targets='['+', '.join('``'+n for n in cfg['theorem_names'])+']'
for n in ['ChallengeAudit','SolutionAudit','TargetHoleAudit','TargetTypeAudit','DefinitionCompatibility']:
 s=read(b/(n+'.lean')).replace(str(b),str(p));s=re.sub(r'let targets : List Name := \[.*\]',lambda m:'let targets : List Name := '+targets,s);(p/(n+'.lean')).write_text(s)
s=read(b/'OriginalEndpointAudit.lean').replace('ArithmeticThetaPalomarD2_509.recover_original_030','ArithmeticThetaPalomarSplit515.recover_original_073').replace('ArithmeticThetaComponentDegreeR0184.component_discriminant_divisor',ob['declaration']);(p/'OriginalEndpointAudit.lean').write_text(s)
for n in ['compile.py','finalize.py']:shutil.copyfile(b/n,p/n)
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
print({n:len((p/(n+'.lean')).read_text().splitlines()) for n in ['Challenge','Solution']})
