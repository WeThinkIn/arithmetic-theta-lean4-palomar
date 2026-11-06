from pathlib import Path
import re,ast,json,hashlib
r=Path(__file__).resolve().parent;e=r.parent;project=e.parent/'project';src=project/'Proof';inputs={}
def read(n):
 p=src/n;inputs[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest();return p.read_text()
def span(s,a,b):
 i=s.index(a);return s[i:s.index(b,i)]
def ns(n,s):return 'namespace '+n+'\n'+s+'end '+n+'\n'
base=(e/'scheme-kato-package-394/Challenge.lean').read_text()
c=base[:base.index('namespace ArithmeticThetaGeometricNormR0150')]
c+='open NeronModelInfra\n'
c+=span(base,'namespace GoodReductionJacobian','namespace ArithmeticThetaPalomarWeierstrass373')
c+=ns('ArithmeticThetaRelativeDiscriminantR0171','abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)\n')
c+=(e/'global-normalized-frame-401/ChartSupport.lean.txt').read_text()
s=read('FullLevelCoverDefinitionsR0175.lean')
c+=ns('ArithmeticThetaFullLevelCoverR0175','open NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171\n'+span(s,'variable (R : Type u)','/-- Universal marking data'))
s=read('SchemeLevelDefinitionsR0204.lean')
c+=ns('ArithmeticThetaSchemeLevelR0204','open ArithmeticThetaLocalWeierstrassR0203 NeronModelInfra\n'+span(s,'def multiple','/-- Compatibility with multiplication'))
s=read('LegendreComparisonDefinitionsR0177.lean')
c+=ns('ArithmeticThetaLegendreComparisonR0177','open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171\n'+span(s,'abbrev ChartRing','def twoPoint')+span(s,'def completedCubic','def legendreAt'))
s=read('GlobalFourTorsionDefinitionsR0190.lean')
c+=ns('ArithmeticThetaGlobalFourTorsionR0190','open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177\n'+span(s,'variable (R : Type u)','/-- The section is the actual quarter'))
s=read('FourTorsionDefinitions.lean')
c+=ns('ArithmeticThetaFourTorsion',span(s,'def splitCurve','/-- The rational expression'))
s=read('MillerGeometryDefinitionsR0114.lean')
c+=ns('ArithmeticThetaMillerR0114',span(s,'abbrev Curve','def Distinct')+span(s,'def tangentSlope','def tangentValue')+span(s,'def tangentClass','def pointIdeal')+span(s,'def xFunction','def millerFunction')+span(s,'def branchEquation','end ArithmeticThetaMillerR0114'))
s=read('MillerReciprocityDefinitionsR0116.lean')
c+=ns('ArithmeticThetaReciprocityR0116',span(s,'abbrev Curve','def pointOrder')+span(s,'def localValue','def tameSymbol')+span(s,'def GoodShift','def movedPairing'))
s=read('MarkingCharacterDefinitionsR0115.lean')
c+=ns('ArithmeticThetaMarkingR0115',span(s,'abbrev Curve','def act')+span(s,'def labels','def root'))
s=read('GeometricFourPairingDefinitionsR0118.lean')
c+=ns('ArithmeticThetaGeometricPairingR0118',span(s,'abbrev Curve','def order')+span(s,'def value','/-- The actual chord/tangent quotient')+span(s,'def movedValue','end ArithmeticThetaGeometricPairingR0118'))
s=read('RelativeFourCharacterDefinitionsR0211.lean')
c+=ns('ArithmeticThetaRelativeFourCharacterR0211','open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaGlobalFourTorsionR0190\nvariable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)\nvariable [Algebra ℚ R] (M : FullLevel R W G 4 (𝟙 (Base R)))\n'+span(s,'def Coordinates','/-- Both marking sections'))
s=read('RelativeGeometricPhaseR0211.lean')
c+=ns('ArithmeticThetaRelativeFourCharacterR0211.RelativeGeometricPhase',span(s,'def tangentNumerator','lemma map_numerator'))
s=read('ArbitraryFourCharacterDefinitionsR0214.lean')
c+=ns('ArithmeticThetaArbitraryFourCharacterR0214','open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190 ArithmeticThetaRelativeFourCharacterR0211\n'+span(s,'variable (R : Type u)','section BaseChange'))
s=read('SchemeFourCharacterDefinitionsR0215.lean')
c+=ns('ArithmeticThetaSchemeFourCharacterR0215','open NeronModelInfra ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204\n'+span(s,'structure AffineTest','/-- The source right action')+span(s,'def affineScalar','/-- Inclusion compatibility'))
original=next(x for x in json.loads((project/'docs/SourceObligations.json').read_text()) if x['id']=='accepted-051')
fiber=span(read('ArbitrarySplitFiberBasisR0214.lean'),'theorem arbitrary_split_fiber_basis :',':= by').replace('theorem arbitrary_split_fiber_basis','theorem arbitrarySplitFiberBasis')+':= by\n'
local='''theorem localDataExists (k : Type u) [Field k] [CharZero k] [DecidableEq k]
    (e : Fin 3 → k) (he : Function.Injective e) :
    Nonempty (ArithmeticThetaGeometricPairingR0118.LocalData k e) := by
'''
endpoint='theorem schemeMillerPhase :\n'+original['type']+' := by\n'
head='namespace ArithmeticThetaPalomarSchemePhase433\n';end='end ArithmeticThetaPalomarSchemePhase433\n'
c+=head+local+'  sorry\n'+fiber+'  sorry\n'+endpoint+'  sorry\n'+end
solution='''module
public import SchemeMillerPhaseR0215
public import ArbitrarySplitFiberBasisR0214
public import GeometricFourCharacterR0118
@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
universe u
'''+head+local+'''  obtain ⟨D, _⟩ := ArithmeticThetaGeometricPairingR0118.geometric_four_character k e he
  exact ⟨D⟩
'''+fiber+'  exact ArithmeticThetaArbitraryFourCharacterR0214.arbitrary_split_fiber_basis\n'+endpoint+'  exact ArithmeticThetaSchemeFourCharacterR0215.scheme_miller_phase\n'+'theorem recover_original_051 :\n'+original['type']+' := by\n  exact schemeMillerPhase\n'+end
tree=ast.parse((e/'period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',solution)]:
 (r/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(r/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
names=['localDataExists','arbitrarySplitFiberBasis','schemeMillerPhase']
(r/'comparator.json').write_text(json.dumps({'challenge_module':'Challenge','solution_module':'Solution','theorem_names':['ArithmeticThetaPalomarSchemePhase433.'+n for n in names],'permitted_axioms':['propext','Classical.choice','Quot.sound']},indent=2)+'\n')
for f in [e/'scheme-kato-package-394/Challenge.lean',e/'global-normalized-frame-401/ChartSupport.lean.txt',project/'docs/SourceObligations.json']:
 inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
(r/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
