from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'end '+n+'\n'
m=read(w/'evidence/compact-key-surface-469/Challenge.lean');c=m[:m.index('namespace GoodReductionJacobian')];c=re.sub(r'/-! Full original053/054.*?-/', '',c,flags=re.S)
# Preserve original group-law structures on all scheme-valued points.
t=cut('Definitions/Def_AlgebraicGeometry_RelativeGroupLaw','def schemeHomOverComp','@[simp]\ntheorem schemeHomOverComp_coe')
t+=cut('Definitions/Def_AlgebraicGeometry_RelativeGroupLaw','structure RelativeGroupLaw','theorem IsCommutative.mul_comm')+'end RelativeGroupLaw\n'
c+=ns('GoodReductionJacobian',t)
t='variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}\n'
t+=cut('Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel','def nsmul','@[simp]\ntheorem nsmul_zero')
t+=cut('Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel','abbrev idPoint','theorem schemeNsmul_over')
c+=ns('GoodReductionJacobian.RelativeGroupLaw',t)
c+=ns('ArithmeticThetaRelativeDiscriminantR0171','abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)\n')
c+=ns('ArithmeticThetaFullLevelCoverR0175', 'variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)\n'+cut('FullLevelCoverDefinitionsR0175','structure FullLevel','def coordinatePoint'),'NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171')
c+=cut('LegendreLevelAtlasDefinitionsR0176','namespace ArithmeticThetaLegendreAtlasR0176','end ArithmeticThetaLegendreAtlasR0176')+'end ArithmeticThetaLegendreAtlasR0176\n'
# Actual affine coordinates used by the two-marking compatibility locus.
c+=m[m.index('section Chart\n'):m.index('namespace ArithmeticThetaFullLevelCoverR0175')]
c+=m[m.index('namespace ArithmeticThetaLegendreComparisonR0177'):m.index('namespace ArithmeticThetaGlobalFourTorsionR0190')]
c+=cut('CompatibleLevelDefinitionsR0178','namespace ArithmeticThetaCompatibleLevelR0178','/-- Cartesian comparison')+'end ArithmeticThetaCompatibleLevelR0178\n'
c+=ns('ArithmeticThetaProjectiveEffectivityR0135','attribute [local instance] MvPolynomial.gradedAlgebra\n'+cut('ProjectiveEffectivityDefinitionsR0135','def projectiveSpace','def coefficientChartMap'))
c+=cut('LevelCompactificationDefinitionsR0179','namespace ArithmeticThetaLevelCompactificationR0179','/-- Both the field and module')+'end ArithmeticThetaLevelCompactificationR0179\n'
c+=ns('ArithmeticThetaLevelCount',cut('GlobalizationDefinitions','def PrimitivePair','/-- The rational product'))
s='''module
public import Mathlib
public import GeometricComponentCuspBoundR0184
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
'''
head='''namespace ArithmeticThetaPalomarComponent485
open ArithmeticThetaLevelCompactificationR0179
variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
'''
claim='''theorem componentIsOpen (x : X.space) : IsOpen (irreducibleComponent x) := by
'''
defs='''def componentOpen (x : X.space) : X.space.Opens := ⟨irreducibleComponent x, componentIsOpen k L D X x⟩
abbrev Component (x : X.space) : Scheme := (componentOpen k L D X x).toScheme
abbrev inclusion (x : X.space) : Component k L D X x ⟶ X.space := (componentOpen k L D X x).ι
def cuspSet (x : X.space) : Set (Component k L D X x) := {y | inclusion k L D X x y ∈ boundary k L D X}
abbrev Cusps (x : X.space) := {y : Component k L D X x // y ∈ cuspSet k L D X x}
'''
c+=head+claim+'  sorry\n'+defs
s+=head+claim+'''  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
'''+defs+'''theorem componentOpen_eq_original (x : X.space) : componentOpen k L D X x = ArithmeticThetaComponentDegreeR0184.componentOpen k L D X x := by
  apply TopologicalSpace.Opens.ext
  rfl
'''
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-029');typ=o['type'].replace('ArithmeticThetaComponentDegreeR0184.Cusps','ArithmeticThetaPalomarComponent485.Cusps')
c+='theorem geometricComponentCuspBound :\n'+typ+' := by sorry\n'
s+='theorem geometricComponentCuspBound :\n'+typ+''' := by
  intro k _ _ _ L hL heven D X x
  exact ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound k L hL heven D X x
'''
s+='theorem recover_original_029 :\n'+o['type']+''' := by
  intro k _ _ _ L hL heven D X x
  exact geometricComponentCuspBound k L hL heven D X x
'''
c+='end ArithmeticThetaPalomarComponent485\n';s+='end ArithmeticThetaPalomarComponent485\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(w/'evidence/compact-key-surface-469/comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if n.startswith(('HomogeneousIdealQuotientGrading.','WeierstrassProjModel.','ProjWeierstrassCubicPrime.'))]+['ArithmeticThetaPalomarComponent485.componentIsOpen','ArithmeticThetaPalomarComponent485.geometricComponentCuspBound'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/compact-key-surface-469/compile.py').read_bytes())
