from pathlib import Path
import json,hashlib,re
p=Path(__file__).resolve().parent;w=p.parent.parent;b=w/'evidence/component-cusp-package-485';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-072');typ=o['type'].replace('ArithmeticThetaComponentDegreeR0184.Cusps','ArithmeticThetaPalomarComponent485.Cusps')
c=read(b/'Challenge.lean');c=c[:c.index('theorem geometricComponentCuspBound :')]+ 'theorem splitComponentCuspBound :\n'+typ+' := by sorry\nend ArithmeticThetaPalomarComponent485\n'
s=read(b/'Solution.lean').replace('public import GeometricComponentCuspBoundR0184','public import SplitCuspDegreeR0239');s=s[:s.index('theorem geometricComponentCuspBound :')]+ 'theorem splitComponentCuspBound :\n'+typ+' := by\n  exact ArithmeticThetaCyclotomicModularityR0239.split_component_cusp_bound\ntheorem recover_original_072 :\n'+o['type']+' := by\n  exact splitComponentCuspBound\nend ArithmeticThetaPalomarComponent485\n'
for n,t in [('Challenge',c),('Solution',s)]: (p/(n+'.lean')).write_text(t);print(n,len(t.splitlines()),len(t.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']=[x.replace('geometricComponentCuspBound','splitComponentCuspBound') for x in cfg['theorem_names']];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','TargetTypeAudit','TargetHoleAudit','OriginalEndpointAudit']:
 s=(b/(n+'.lean')).read_text().replace(str(b),str(p)).replace('geometricComponentCuspBound','splitComponentCuspBound').replace('ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound','ArithmeticThetaCyclotomicModularityR0239.split_component_cusp_bound').replace('recover_original_029','recover_original_072');(p/(n+'.lean')).write_text(s)
