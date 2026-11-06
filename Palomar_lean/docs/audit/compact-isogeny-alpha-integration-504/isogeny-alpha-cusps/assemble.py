from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
c=read(w/'evidence/compact-alpha-package-501/Challenge.lean');c=c[:c.index('namespace ArithmeticThetaPalomarCompactAlpha501')]
# Remove only unused compact-global alpha declarations; retain the actual relative realization and theta series.
a=c.index('section LevelBase\n');b=c.index('def thetaAt',a);z=c.index('def ExactTateAlpha',b);theta=c[b:z];c=c[:a]+ 'variable (k : Type) [Field k] [CharZero k]\n'+theta+'end ArithmeticThetaGlobalFourTorsionR0190\n'
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','structure Pointed','def scalar'),'NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176')
t=cut('IsogenyHalfLinesDefinitionsR0193','def IsFamilyAlpha','variable (X : Compactification')
c+=ns('ArithmeticThetaIsogenyHalfLinesR0193',t,'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182')
s='''module
public import IsogenyAlphaDesignatedExpansionR0193
public import IsogenyAlphaAllCuspOrdersR0193
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
'''
obs=json.loads(read(w/'project/docs/SourceObligations.json'));names=[]
for i,n in [('043','isogenyAlphaDesignatedExpansion'),('044','isogenyAlphaAllCuspOrders')]:
 o=next(x for x in obs if x['id']=='accepted-'+i);claim='theorem '+n+' :\n'+o['type']+' := by\n';c+=ns('ArithmeticThetaPalomarIsogeny502',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarIsogeny502',claim+'  exact '+o['declaration']+'\n'+'theorem recover_original_'+i+' :\n'+o['type']+' := '+n+'\n');names.append('ArithmeticThetaPalomarIsogeny502.'+n)
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(w/'evidence/compact-alpha-package-501/comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if not n.startswith('ArithmeticThetaPalomarCompactAlpha501.')]+names;(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/compact-alpha-package-501/compile.py').read_bytes())
