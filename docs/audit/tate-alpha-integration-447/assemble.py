from pathlib import Path
import re,json,hashlib,ast
w=Path(__file__).resolve().parent.parent.parent;p=w/'evidence/tate-alpha-package-445';p.mkdir(exist_ok=True);src=w/'project/Proof';inputs={}
def read(f):
 inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def decl(file,marker):
 s=read(src/(file+'.lean'));start=s.index(marker);rest=s[start:];m=re.search(r'\n(?=(?:/--|/-!|(?:private |local |protected )?(?:def |abbrev |theorem |lemma |structure |instance |variable |namespace |end |section )))',rest)
 return rest[:m.start() if m else len(rest)]+'\n'
def ns(n,t,opens=''):
 return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'end '+n+'\n'
base=w/'evidence/scheme-alpha-character-package-437'
c=read(base/'Challenge.uncompressed.lean.txt');s=read(base/'Solution.uncompressed.lean.txt').replace('public import', 'public import FourTorsionTateBehaviorR0190\npublic import',1)
extra=''
extra+=ns('ArithmeticThetaTateSeries','variable {k : Type u} [Field k]\n'+''.join(decl('TateSeriesDefinitions','def '+x+' ') for x in ['monomial','xTerm','yTerm','partialX','partialY','tateX','tateY','theta']))
extra+=ns('ArithmeticThetaCubicModelR0144','variable (k : Type u) [Field k] [CharZero k]\n'+decl('CubicModelDefinitionsR0144','def rootSeries '))
extra+=ns('ArithmeticThetaCompactifiedDifferentialR0145','variable (k : Type u) [Field k] [CharZero k]\n'+''.join(decl('CompactifiedDifferentialDefinitionsR0145',x) for x in ['def root ','def curve ','abbrev projectiveCurve ','abbrev ChartRing ','def chartInclusion ']),'ArithmeticThetaCubicModelR0144')
extra+=ns('ArithmeticThetaFullLevelCoverR0175','variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)\n'+decl('FullLevelCoverDefinitionsR0175','def coordinatePoint '),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171')
extra+=ns('ArithmeticThetaTateCuspsR0181','variable (k : Type u) [Field k] [CharZero k] (L : ℕ)\n'+''.join(decl('TateCuspDefinitionsR0181',x) for x in ['abbrev TateCurve ','abbrev Puncture ','structure TateLevel ','def CanonicalMarking ']),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175')
extra+=ns('ArithmeticThetaRelativeDiscriminantR0171',decl('RelativeDiscriminantDefinitionsR0171','def res '))
extra+=ns('ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential','''section ChartEquiv
variable {B : Type u} [CommRing B] {C : Scheme.{u}}
variable (i : Spec (CommRingCat.of B) ⟶ C) [IsOpenImmersion i]
'''+decl('GlobalNormalizedDifferentialR0145','def chartRingEquiv ')+'''end ChartEquiv
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} (E : C ≅ projectiveCurve k r)
'''+decl('GlobalNormalizedDifferentialR0145','abbrev zLeg ')+decl('GlobalNormalizedDifferentialR0145','instance zLeg_open ')+decl('GlobalNormalizedDifferentialR0145','abbrev zOpen ')+decl('GlobalNormalizedDifferentialR0145','abbrev zSection '))
# New namespace prevents collision with original boundary definitions; exact source formulas retained.
bound=ns('ArithmeticThetaPalomarBoundary445','variable (k : Type) [Field k] [CharZero k] (L : ℕ)\n'+''.join(decl('BoundaryHodgeDefinitionsR0182',x) for x in ['abbrev CurveFrame ','def Normalized ','def hodgeGenerator ']),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaTateCuspsR0181')
bound=bound.replace('ArithmeticThetaCompactifiedDifferentialR0145.relativeD','ArithmeticThetaPalomarDifferential365.relativeD')
# Original Challenge kaehler is the independent365 definition.
bound=bound.replace('(structureMap (LaurentSeries k) (TateCurve k L)).kaehler','ArithmeticThetaPalomarDifferential365.kaehler (structureMap (LaurentSeries k) (TateCurve k L))')
bound=bound.replace('Scheme.Modules.pullbackLocalSection','ArithmeticThetaPalomarDifferential365.pullSection')
# Independent adjunction pullback has a compiled bridge to the original.
extra+=ns('ArithmeticThetaGlobalFourTorsionR0190','variable (k : Type) [Field k] [CharZero k]\n'+decl('GlobalFourTorsionDefinitionsR0190','def thetaAt '))
c+=extra+bound;s+=bound
obs=json.loads(read(w/'project/docs/SourceObligations.json'));o=next(x for x in obs if x['id']=='accepted-040');typ=o['type'].replace('ArithmeticThetaBoundaryHodgeR0182.','ArithmeticThetaPalomarBoundary445.').replace('ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha','ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha')
head='namespace ArithmeticThetaPalomarTateAlpha445\n';c+=head;s+=head
s+='''theorem boundaryNormalized_iff (k : Type) [Field k] [CharZero k] (L : ℕ)
    (δ : ArithmeticThetaPalomarBoundary445.CurveFrame k L) :
    ArithmeticThetaPalomarBoundary445.Normalized k L δ ↔ ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ := Iff.rfl
theorem boundaryGenerator_eq (k : Type) [Field k] [CharZero k] (L : ℕ)
    (δ : ArithmeticThetaPalomarBoundary445.CurveFrame k L) :
    ArithmeticThetaPalomarBoundary445.hodgeGenerator k L δ = ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ := rfl
'''
d='theorem fourTorsionTateBehavior :\n'+typ+' := by\n';c+=d+'  sorry\n';s+=d+'''  intro k _ _ L hL h4 E δ hδ a ha
  exact ArithmeticThetaGlobalFourTorsionR0190.four_torsion_tate_behavior k L hL h4 E δ hδ a
    (ArithmeticThetaPalomarSchemeAlpha437.affineAlpha_iff _ _ _ _ _ _).mp ha
'''
s+='theorem recover_original_040 :\n'+o['type']+' := by\n'+'''  intro k _ _ L hL h4 E δ hδ a ha
  exact fourTorsionTateBehavior k L hL h4 E δ hδ a
    ((ArithmeticThetaPalomarSchemeAlpha437.affineAlpha_iff _ _ _ _ _ _).mpr ha)
'''
c+='end ArithmeticThetaPalomarTateAlpha445\n';s+='end ArithmeticThetaPalomarTateAlpha445\n'
# Parenthesize the argument of the forward proof.
s=s.replace('(ArithmeticThetaPalomarSchemeAlpha437.affineAlpha_iff _ _ _ _ _ _).mp ha','((ArithmeticThetaPalomarSchemeAlpha437.affineAlpha_iff _ _ _ _ _ _).mp ha)')
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(base/'comparator.json'));cfg['theorem_names']+=['ArithmeticThetaPalomarTateAlpha445.fourTorsionTateBehavior'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
(p/'compile.py').write_bytes((w/'evidence/relative-alpha-package-442/compile.py').read_bytes())
