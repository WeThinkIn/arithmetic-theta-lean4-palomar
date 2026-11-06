from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
b=w/'evidence/compact-alpha-half-line-package-505';c=read(b/'Challenge.lean');marker='namespace ArithmeticThetaPalomarHalf505\nopen ArithmeticThetaTensorPower ArithmeticThetaPullback';c=c[:c.rindex(marker)]
a=c.index('def openComparison');z=c.index('variable (X : Compactification',a);c=c[:a]+c[z:]
a=c.index('def CuspOrders');z=c.index('def thetaAt',a);c=c[:a]+c[z:]
a=c.index('def ExactTateAlpha');z=c.index('end LevelBase',a);c=c[:a]+c[z:]
a=c.index('def IsCompactAlpha');z=c.index('def componentAlpha',a);c=c[:a]+c[z:]
a=c.index('def HalfAlphaDivisor');z=c.index('def canonicalDivisorData',a);c=c[:a]+c[z:]
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','structure Pointed','def scalar'),'NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176')
opens='ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaLineRoot ArithmeticThetaSectionOrder'
c+=ns('ArithmeticThetaIsogenyHalfLinesR0193',cut('IsogenyHalfLinesDefinitionsR0193','def IsFamilyAlpha','/-- Normalization in the ORIGINAL disk'),opens)
branch=ns('ArithmeticThetaPalomarIsogenyHalf506','variable (k : Type) [Field k] [CharZero k] (L m : ℕ) (D : LevelData k L) (X : Compactification k L D) (H : Extension k L D X)\n'+cut('IsogenyHalfLinesDefinitionsR0193','def HalfBranch','end ArithmeticThetaIsogenyHalfLinesR0193').replace('pullback_tensorPower_iso','ArithmeticThetaPalomarHalf505.powerComparison'),opens)
a=c.index('def testAlpha');z=c.index('def testKernel',a);c=c[:a]+c[z:]
a=c.index('def AllCuspOrders');z=c.index('variable (X : Compactification',a);c=c[:a]+c[z:]
c+=branch;s=read(b/'Solution.lean');s=s[:s.rindex(marker)];s=s.replace('public import CompactAlphaCanonicalHalfLineR0192','public import IsogenyCanonicalHalfLineR0193');s+=branch
s+=ns('ArithmeticThetaPalomarIsogenyHalf506','''theorem branch_iff_original (k : Type) [Field k] [CharZero k] (L m : ℕ) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) (x : X.space) (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (β : ArithmeticThetaTensorPower.tensorPower _ A.line 2 ≅ ArithmeticThetaComponentDegreeR0184.hodge k L D X x H) : HalfBranch k L m D X H x A β ↔ ArithmeticThetaIsogenyHalfLinesR0193.HalfBranch k L m D X H x A β := by
  simp only [HalfBranch, ArithmeticThetaIsogenyHalfLinesR0193.HalfBranch, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
''')
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-045');typ=o['type'].replace('ArithmeticThetaIsogenyHalfLinesR0193.HalfBranch','ArithmeticThetaPalomarIsogenyHalf506.HalfBranch');claim='theorem isogenyCanonicalHalfLine :\n'+typ+' := by\n';c+=ns('ArithmeticThetaPalomarIsogenyHalf506',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarIsogenyHalf506',claim+'  simpa only [branch_iff_original] using ArithmeticThetaIsogenyHalfLinesR0193.isogeny_canonical_half_line\n'+'theorem recover_original_045 :\n'+o['type']+' := by\n  simpa only [branch_iff_original] using isogenyCanonicalHalfLine\n')
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if n!='ArithmeticThetaPalomarHalf505.compactAlphaCanonicalHalfLine']+['ArithmeticThetaPalomarIsogenyHalf506.isogenyCanonicalHalfLine'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
