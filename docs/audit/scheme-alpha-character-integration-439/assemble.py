from pathlib import Path
import re,ast,json,hashlib
r=Path(__file__).resolve().parent;e=r.parent;project=e.parent/'project';src=project/'Proof';inputs={}
def read(n):
 p=src/n;inputs[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest();return p.read_text()
def span(s,a,b):
 i=s.index(a);return s[i:s.index(b,i)]
def ns(n,s):return 'namespace '+n+'\n'+s+'end '+n+'\n'
phase=(e/'scheme-miller-phase-package-433/Challenge.uncompressed.lean.txt').read_text()
c=phase[:phase.index('namespace ArithmeticThetaFourTorsion')]
c+=ns('ArithmeticThetaFourTorsion',span(read('FourTorsionDefinitions.lean'),'def splitCurve','end ArithmeticThetaFourTorsion'))
relative=read('RelativeFourCharacterDefinitionsR0211.lean')
c+=ns('ArithmeticThetaRelativeFourCharacterR0211','open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaGlobalFourTorsionR0190\nvariable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)\nvariable [Algebra ℚ R] (M : FullLevel R W G 4 (𝟙 (Base R)))\n'+span(relative,'def Coordinates','/-- Identification with'))
c+=span(phase,'namespace ArithmeticThetaRelativeFourCharacterR0211.RelativeGeometricPhase','namespace ArithmeticThetaPalomarSchemePhase433')
originalScheme=read('SchemeFourCharacterDefinitionsR0215.lean')
c+=ns('ArithmeticThetaSchemeFourCharacterR0215','open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204\nvariable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)\n'+span(originalScheme,'def Changes','/-- Pull the actual global'))
diff=(e/'canonical-conormal-map-436/Challenge.lean').read_text()
defs=span(diff,'namespace ArithmeticThetaPalomarDifferential365','namespace ArithmeticThetaPalomarConormal436')
c+=defs
framec=(e/'global-normalized-frame-401/Challenge.lean').read_text()
c+=framec[framec.index('namespace ArithmeticThetaPalomarGlobalFrame401'):]
c+=diff[diff.index('namespace ArithmeticThetaPalomarConormal436'):]
sol=(e/'canonical-conormal-map-436/Solution.lean').read_text();conormalProofs=sol[sol.index('namespace ArithmeticThetaPalomarConormal436'):]
frames=(e/'global-normalized-frame-401/Solution.lean').read_text();frameProofs=frames[frames.index('section KaehlerProvider'):]
s='''module
public import Mathlib
public import SchemeAlphaCharacterR0215
public import SchemeAlphaSectionR0215
public import AffineConormalHodgeNaturalityR0205
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
'''+defs+frameProofs+conormalProofs
c+=ns('ArithmeticThetaRelativeDiscriminantR0171','abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) := ArithmeticThetaPalomarGlobalFrame401.Hodge R W\n')
c+=ns('ArithmeticThetaPullback',span(read('PullbackTensorDefinitions.lean'),'def pullbackGlobalSection','end ArithmeticThetaPullback'))
c+=ns('ArithmeticThetaOpenHodgeR0180','open ArithmeticThetaRelativeDiscriminantR0171\n'+span(read('OpenHodgeDescentDefinitionsR0180.lean'),'def scalar','/-- Local-frame formula'))
g=read('GlobalFourTorsionDefinitionsR0190.lean')
c+=ns('ArithmeticThetaGlobalFourTorsionR0190','open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177\n'+span(g,'variable (R : Type u)','def twoLabel')+span(g,'def RootData','abbrev CurveFrame'))
pull=ns('ArithmeticThetaPalomarPullback437',span(read('PullbackUnit.lean'),'def pullback_unit_iso','end ArithmeticThetaPullback')+'''def pullbackEqIso {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
  eqToIso (by cases h; rfl)
'''+span(read('RelativeHodgePowerBaseChangeR0171.lean'),'def squarePullbackIso','theorem squarePullbackIso_section'))
affine='''namespace ArithmeticThetaPalomarAffineAlpha437
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaGlobalFourTorsionR0190
variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W) (L : ℕ)
  (M : FullLevel R W G L (𝟙 (Base R)))
def RealizesAlpha [Algebra ℚ R] (a : Γ(Hodge R W, ⊤)) : Prop :=
  ∃ (e : Fin 3 → R) (x y g : R) (δ : ArithmeticThetaPalomarGlobalFrame401.CurveFrame R W),
    RootData R W G L M e x y g ∧ ArithmeticThetaPalomarGlobalFrame401.NormalizedFrame R W δ ∧
    a = ArithmeticThetaOpenHodgeR0180.scalar R (2*g) • ArithmeticThetaPalomarGlobalFrame401.hodgeGenerator R W δ
end ArithmeticThetaPalomarAffineAlpha437
'''
top='''namespace ArithmeticThetaPalomarSchemeAlpha437
open NeronModelInfra ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaSchemeFourCharacterR0215
open ArithmeticThetaPalomarDifferential365 ArithmeticThetaPalomarPullback437
abbrev Cotangent {S : Scheme.{u}} (E : Family S) : S.Modules :=
  (Scheme.Modules.pullback E.zero).obj (idealModule E.zero.ker)
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4)
'''
body=span(originalScheme,'def AffineIdealCompatible','/-- Pullback along a canonical')
origin='(ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation)'
for x in ['E.zero',origin]:
 body=body.replace(x+'.ker.moduleι','(idealInclusion '+x+'.ker)').replace(x+'.ker.module','(idealModule '+x+'.ker)')
body=body.replace('ArithmeticThetaPullback.pullback_unit_iso','ArithmeticThetaPalomarPullback437.pullback_unit_iso').replace('ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap','ArithmeticThetaPalomarConormal436.conormalMap').replace('ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha','ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha')
common=pull+affine+top+body
c+=common;s+=common
bridges='''theorem affineAlpha_iff (R : Type u) [CommRing R] [Algebra ℚ R] (W : WeierstrassCurve R)
    (G : ArithmeticThetaRelativeKatoR0169.Law R W) (L : ℕ)
    (N : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (𝟙 (ArithmeticThetaRelativeDiscriminantR0171.Base R)))
    (a : Γ(ArithmeticThetaRelativeDiscriminantR0171.Hodge R W, ⊤)) :
    ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha R W G L N a ↔
      ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha R W G L N a := by
  simp only [ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha,
    ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha,
    ArithmeticThetaPalomarGlobalFrame401.normalizedFrame_iff_original,
    ArithmeticThetaPalomarGlobalFrame401.hodgeGenerator_eq_original]
  rfl
theorem idealCompatible_iff (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅
      idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) :
    AffineIdealCompatible E M P i ↔ ArithmeticThetaSchemeFourCharacterR0215.AffineIdealCompatible E M P i := Iff.rfl
theorem affineHodgeMap_eq (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅
      idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) :
    affineHodgeMap E M P i = ArithmeticThetaSchemeFourCharacterR0215.affineHodgeMap E M P i := by
  unfold affineHodgeMap
  rw [ArithmeticThetaPalomarConormal436.conormalMap_eq_original]
  rfl
theorem affineAlpha_eq (P : AffineTest E M)
    (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅
      idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker)
    (a : Γ(Cotangent E, ⊤)) :
    affineAlpha E M P i a = ArithmeticThetaSchemeFourCharacterR0215.affineAlpha E M P i a := by
  unfold affineAlpha
  rw [affineHodgeMap_eq]
  rfl
theorem realizesAlpha_iff (a : Γ(Cotangent E, ⊤)) :
    RealizesAlpha E M a ↔ ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha E M a := by
  simp only [RealizesAlpha, ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha,
    idealCompatible_iff, affineAlpha_iff, affineAlpha_eq]
  rfl
'''
s+=bridges
exists='''theorem alphaExists (k : Type u) [Field k] [CharZero k] (S : Scheme.{u})
    (σ : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base k) (E : Family S) (M : FullLevel E 4) :
    ∃! a : Γ(Cotangent E, ⊤), RealizesAlpha E M a := by
'''
c+=exists+'  sorry\n'
s+=exists+'''  obtain ⟨a,ha,hu⟩ := (ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_section k S σ E M).1
  refine ⟨a,(realizesAlpha_iff E M a).mpr ha,?_⟩
  intro b hb
  exact hu b ((realizesAlpha_iff E M b).mp hb)
'''
original=next(x for x in json.loads((project/'docs/SourceObligations.json').read_text()) if x['id']=='accepted-052')
typ=original['type'].replace('ArithmeticThetaSchemeHodgeR0205.Cotangent','Cotangent').replace('ArithmeticThetaSchemeFourCharacterR0215.RealizesAlpha','RealizesAlpha')
target='theorem schemeAlphaCharacter :\n'+typ+' := by\n'
c+=target+'  sorry\n'
s+=target+'''  intro k _ _ S σ E M z a hz ha A hA
  obtain ⟨N,hN,hzN,hchar⟩ := ArithmeticThetaSchemeFourCharacterR0215.scheme_alpha_character
    k S σ E M z a hz ((realizesAlpha_iff E M a).mp ha) A hA
  exact ⟨N,hN,hzN,fun a' ha' => hchar a' ((realizesAlpha_iff E N a').mp ha')⟩
'''
s+='theorem recover_original_052 :\n'+original['type']+' := by\n'+'''  intro k _ _ S σ E M z a hz ha A hA
  obtain ⟨N,hN,hzN,hchar⟩ := schemeAlphaCharacter k S σ E M z a hz
    ((realizesAlpha_iff E M a).mpr ha) A hA
  exact ⟨N,hN,hzN,fun a' ha' => hchar a' ((realizesAlpha_iff E N a').mpr ha')⟩
'''
c+='end ArithmeticThetaPalomarSchemeAlpha437\n';s+='end ArithmeticThetaPalomarSchemeAlpha437\n'
tree=ast.parse((e/'period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (r/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(r/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
targets=['ArithmeticThetaPalomarGlobalFrame401.'+n for n in ['canonicalDifferentialMap','normalizedFrameExists','hodgeGeneratorFrame','normalizedFrameExistsUnique']]+['ArithmeticThetaPalomarConormal436.canonicalConormalMap','ArithmeticThetaPalomarSchemeAlpha437.alphaExists','ArithmeticThetaPalomarSchemeAlpha437.schemeAlphaCharacter']
(r/'comparator.json').write_text(json.dumps({'challenge_module':'Challenge','solution_module':'Solution','theorem_names':targets,'permitted_axioms':['propext','Classical.choice','Quot.sound']},indent=2)+'\n')
for f in [e/'scheme-miller-phase-package-433/Challenge.uncompressed.lean.txt',e/'canonical-conormal-map-436/Challenge.lean',e/'canonical-conormal-map-436/Solution.lean',e/'global-normalized-frame-401/Challenge.lean',e/'global-normalized-frame-401/Solution.lean',project/'docs/SourceObligations.json']:
 inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
(r/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
