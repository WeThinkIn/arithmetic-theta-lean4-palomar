from pathlib import Path
import ast,hashlib,json,re
p=Path(__file__).resolve().parent;w=p.parent.parent;inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
b=w/'evidence/actual-dual-evaluation-465';c=read(b/'Challenge.lean');s=read(b/'Solution.lean').replace('public import Mathlib','public import Mathlib\npublic import EvenPointThetaEvaluationR0217',1)
model=read(w/'evidence/compact-key-surface-469/Challenge.lean')
def block(t,a,z):i=t.index(a);return t[i:t.index(z,i)+len(z)]+'\n'
c+='open AlgebraicGeometry\n'+block(model,'namespace NeronModelInfra','end NeronModelInfra')+'open NeronModelInfra\n'
c+=block(model,'namespace GoodReductionJacobian','end GoodReductionJacobian')
c+=block(model,'namespace ArithmeticThetaLocalWeierstrassR0203','end ArithmeticThetaLocalWeierstrassR0203')
c+='namespace ArithmeticThetaLocalWeierstrassR0203\nabbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)\nend ArithmeticThetaLocalWeierstrassR0203\n'
t=read(w/'project/Proof/SchemeLevelDefinitionsR0204.lean');mult=t[t.index('def multiple'):t.index('/-- A full ordered marking')]
c+='namespace ArithmeticThetaSchemeLevelR0204\nopen ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra\n'+mult+'end ArithmeticThetaSchemeLevelR0204\n'
ev=model[model.index('namespace ArithmeticThetaEvenMarkingTorsorR0216'):model.index('def Cartesian {T : Scheme.{u}}')]
c+=ev+'end ArithmeticThetaEvenMarkingTorsorR0216\n'
t=read(w/'project/Proof/Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean')
c+='namespace AlgebraicGeometry\n'+t[t.index('structure Scheme.Modules.IsInvertible'):t.index('theorem Scheme.Modules.isInvertible_unit')]+'end AlgebraicGeometry\n'
c+=block(model,'namespace ArithmeticThetaRelativeDiscriminantR0171\ndef res','end ArithmeticThetaRelativeDiscriminantR0171')
t=read(w/'project/Proof/Definitions/Def_AlgebraicCurve_RelCartier.lean')
c+='namespace AlgebraicGeometry.Scheme.IdealSheafData\nvariable {X : Scheme.{u}}\n'+t[t.index('def IsInvertible'):t.index('theorem isInvertible_top')]+'end AlgebraicGeometry.Scheme.IdealSheafData\n'
t=read(w/'project/Proof/Definitions/Def_AlgebraicGeometry_ModulesSectionZeroScheme.lean')
c+='namespace AlgebraicGeometry.Scheme.Modules\nvariable {X : Scheme.{u}} {M : X.Modules}\n'+t[t.index('def toUnitSection'):t.index('abbrev zeroScheme')]+ 'end AlgebraicGeometry.Scheme.Modules\n'
t=read(w/'project/Proof/MultiplierKeyDefinitionsR0217.lean');defs=t[t.index('def thetaIdeal'):t.index('def inverseSquare')].replace('Scheme.Modules.ihomGlobalSectionsEquiv','ArithmeticThetaPalomarDual465.globalSectionsEquiv')
head='''namespace ArithmeticThetaPalomarTheta473
open CategoryTheory AlgebraicGeometry MonoidalCategory
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
'''
c+=head+defs;s+=head+defs
s+='''theorem evaluationSection_eq_original
    (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) :
    evaluationSection E P e = ArithmeticThetaMultiplierKeyR0217.evaluationSection E P e :=
  ArithmeticThetaPalomarDual465.evaluationSection_eq_original _ _ _
'''
obs=json.loads(read(w/'project/docs/SourceObligations.json'));o=next(x for x in obs if x['id']=='accepted-099');typ=o['type'].replace('ArithmeticThetaMultiplierKeyR0217.','ArithmeticThetaPalomarTheta473.')
c+='theorem evenPointThetaEvaluation :\n'+typ+' := by\n  sorry\n'
s+='theorem evenPointThetaEvaluation :\n'+typ+' := by\n'+'''  intro k _ _ S σ E P
  have h := ArithmeticThetaMultiplierKeyR0217.even_point_theta_evaluation k S σ E P
  convert h using 1 <;> (try simp only [evaluationSection_eq_original]) <;> rfl
'''
s+='theorem recover_original_099 :\n'+o['type']+' := by\n'+'''  intro k _ _ S σ E P
  have h := evenPointThetaEvaluation k S σ E P
  convert h using 1 <;> (try simp only [evaluationSection_eq_original]) <;> rfl
'''
c+='end ArithmeticThetaPalomarTheta473\n';s+='end ArithmeticThetaPalomarTheta473\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
    (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']+=['ArithmeticThetaPalomarTheta473.evenPointThetaEvaluation'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
