from pathlib import Path
import re,json,hashlib,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):
 inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def decl(file,marker):
 text=read(src/(file+'.lean'));rest=text[text.index(marker):];m=re.search(r'\n(?=(?:/--|/-!|(?:private |local |protected )?(?:def |abbrev |theorem |lemma |structure |instance |variable |namespace |end |section )))',rest)
 return rest[:m.start() if m else len(rest)]+'\n'
def ns(n,t,opens=''):
 return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'end '+n+'\n'
base=w/'evidence/scheme-alpha-character-package-437'
c=read(base/'Challenge.uncompressed.lean.txt');s=read(base/'Solution.uncompressed.lean.txt').replace('public import','public import PhaseFreeMultiplierR0219\npublic import PhaseFreeMultiplierBaseChangeR0219\npublic import',1)
extra=ns('AlgebraicGeometry',decl('Definitions/Def_AlgebraicGeometry_RelativePicardFunctor','structure Scheme.Modules.IsInvertible '))
extra+=ns('ArithmeticThetaRelativeDiscriminantR0171',decl('RelativeDiscriminantDefinitionsR0171','def res ')+decl('RelativeDiscriminantDefinitionsR0171','def IsFrame '))
extra+=ns('ArithmeticThetaSchemeLevelR0204',decl('SchemeLevelDefinitionsR0204','def Multiplicative ')+decl('SchemeLevelDefinitionsR0204','def MarkedCartesian '),'ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra')
extra+=ns('ArithmeticThetaEvenMarkingTorsorR0216','variable {S : Scheme.{u}} (E : Family S)\n'+decl('EvenMarkingTorsorDefinitionsR0216','structure EvenPoint ')+decl('EvenMarkingTorsorDefinitionsR0216','def Cartesian '),'ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 NeronModelInfra')
extra+=ns('ArithmeticThetaUniversalEvaluationR0213','variable {S : Scheme.{u}} (E : Family S) (M : ArithmeticThetaSchemeLevelR0204.FullLevel E 4)\n'+decl('UniversalThetaEvaluationDefinitionsR0213','def evenPoint '),'ArithmeticThetaLocalWeierstrassR0203')
extra+=ns('ArithmeticThetaPhaseSwitchR0218',decl('PhaseSwitchDefinitionsR0218','def reversal '))
opens='ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaPullback ArithmeticThetaRelativeDiscriminantR0171'
body='variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)\n'
body+=''.join(decl('PhaseFreeKeyDefinitionsR0219',x) for x in ['structure MarkedTest ','def remark ','abbrev Frames ','structure TestMap ','def testPull ','def IsMultiplier ','def PreservesFrames '])
body+='variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F) (b : T ⟶ S) (f : F.curve ⟶ E.curve)\n'
body+=''.join(decl('PhaseFreeKeyDefinitionsR0219',x) for x in ['structure RelativeTestMap ','def testSquare ','def Compatible '])
extra+=ns('ArithmeticThetaPhaseFreeKeyR0219',body,opens)
c+=extra
obs={x['id']:x for x in json.loads(read(w/'project/docs/SourceObligations.json'))};targets=[]
for id,name,orig in [('accepted-095','phaseFreeMultiplier','phase_free_multiplier'),('accepted-097','phaseFreeMultiplierBaseChange','phase_free_multiplier_base_change')]:
 d='theorem '+name+' :\n'+obs[id]['type']+' := by\n';c+=ns('ArithmeticThetaPalomarMultiplier450',d+'  sorry\n');s+=ns('ArithmeticThetaPalomarMultiplier450',d+'  exact ArithmeticThetaPhaseFreeKeyR0219.'+orig+'\n'+'theorem recover_original_'+id[-3:]+' :\n'+obs[id]['type']+' := by\n  exact '+name+'\n');targets.append('ArithmeticThetaPalomarMultiplier450.'+name)
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(base/'comparator.json'));cfg['theorem_names']+=targets;(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
(p/'compile.py').write_bytes((w/'evidence/relative-alpha-package-442/compile.py').read_bytes())
