from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):t=read(src/(f+'.lean'));return t[t.index(a):t.index(z,t.index(a))]
def decl(f,start):
 t=read(src/(f+'.lean'));a=t.index(start);m=re.search(r'\n(?:/\-\-|@\[|(?:private |local |noncomputable )?(?:def|abbrev|theorem|lemma|instance|structure) |end |namespace |variable )',t[a+len(start):]);b=a+len(start)+m.start() if m else len(t);return t[a:b]+'\n'
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'end '+n+'\n'
t=read(w/'evidence/tate-coordinate-package-377/Challenge.lean');c=t[:t.index('namespace ArithmeticThetaPolygonCartierR0133')]
c+=ns('ArithmeticThetaIdentitySectionsR0138',decl('IdentityThetaSectionsDefinitionsR0138','def zeroIndex '))
c+=ns('ArithmeticThetaProjectiveEffectivityR0135','variable (k : Type u) [Field k] [CharZero k]\n'+decl('ProjectiveEffectivityDefinitionsR0135','def genericBase ')+decl('ProjectiveEffectivityDefinitionsR0135','def genericStructure '),'ArithmeticThetaInfinitesimalPolygonR0129')
opens='ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138'
vars='variable (k : Type u) [Field k] [CharZero k]\nvariable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}\n'
c+=ns('ArithmeticThetaGenericEvaluationR0140',vars+decl('GenericThetaEvaluationDefinitionsR0140','def genericScheme ')+decl('GenericThetaEvaluationDefinitionsR0140','def genericPoint '),opens)
m=read(w/'evidence/compact-key-surface-469/Challenge.lean');c+=m[m.index('namespace NeronModelInfra'):m.index('namespace HomogeneousIdealQuotientGrading')]
c+=ns('WeierstrassProjModel',m[m.index('def schemeHomOverComp'):m.index('end WeierstrassProjModel\nnamespace ArithmeticThetaRelativeKatoR0169')],'NeronModelInfra')
c+=m[m.index('namespace WeierstrassProjModel.RelativeGroupLaw'):m.index('open NeronModelInfra\nnamespace GoodReductionJacobian')]
opens+=' ArithmeticThetaGenericEvaluationR0140'
point=decl('MarkedGroupLawDefinitionsR0146','def pointOver ').replace('by rw [Category.assoc, genericPoint_structure, Category.comp_id]','by simp [ArithmeticThetaGenericEvaluationR0140.genericPoint, ArithmeticThetaProjectiveEffectivityR0135.genericStructure]')
c+=ns('ArithmeticThetaMarkedGroupLawR0146',vars+decl('MarkedGroupLawDefinitionsR0146','abbrev Law ')+point+decl('MarkedGroupLawDefinitionsR0146','def IsOriginLaw '),opens+' NeronModelInfra')
c+=ns('ArithmeticThetaHodgeFourTorsionR0147',vars+decl('HodgeFourTorsionDefinitionsR0147','def universalPoint ')+decl('HodgeFourTorsionDefinitionsR0147','def multiplication '),opens+' NeronModelInfra ArithmeticThetaMarkedGroupLawR0146')
c+=ns('ArithmeticThetaGeometricNormR0150','variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]\n'+decl('GeometricNormDefinitionsR0150','def IsFieldMap ')+decl('GeometricNormDefinitionsR0150','def fieldNorm ')+vars+decl('GeometricNormDefinitionsR0150','def identityPoint ')+decl('GeometricNormDefinitionsR0150','def katoOrder '),opens+' ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaHodgeFourTorsionR0147')
c+=ns('ArithmeticThetaKatoExistenceR0151',vars+decl('KatoExistenceDefinitionsR0151','def HasKatoDivisor ')+decl('KatoExistenceDefinitionsR0151','def IsKatoFunction '),opens+' ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaGeometricNormR0150')
c+=ns('ArithmeticThetaMarkedKatoValuesR0159',decl('MarkedKatoValueDefinitionsR0159','def HasValue '))
c+=ns('ArithmeticThetaUnaryProduct',decl('UnaryThetaProduct','noncomputable def unaryA ')+decl('UnaryThetaProduct','noncomputable def clearedUnaryTheta '))
c+=ns('ArithmeticThetaDiscriminant',decl('DiscriminantDefinitions','noncomputable def partialEuler ')+decl('DiscriminantDefinitions','noncomputable def euler ')+decl('DiscriminantDefinitions','noncomputable def P :'))
c+=cut('UnaryKatoPowerDefinitionsR0160','namespace ArithmeticThetaUnaryKatoPowerR0160','end ArithmeticThetaUnaryKatoPowerR0160')+'end ArithmeticThetaUnaryKatoPowerR0160\n'
s='''module
public import Mathlib
public import UnaryPowerGeometricRealizationR0160
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
'''
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-093');name='ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization';sig='theorem '+name+' :\n'+o['type']+' := by\n';c+=sig+'  sorry\n';s+=sig+'  exact ArithmeticThetaUnaryKatoPowerR0160.unary_power_geometric_realization\n';s+='theorem ArithmeticThetaPalomarUnary489.recover_original_093 :\n'+o['type']+' := '+name+'\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg={'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization'],'permitted_axioms':['propext','Classical.choice','Quot.sound']};(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/compact-key-surface-469/compile.py').read_bytes())
