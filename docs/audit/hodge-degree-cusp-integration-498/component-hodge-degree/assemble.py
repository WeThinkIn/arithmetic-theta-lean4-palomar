from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
b=read(w/'evidence/component-cusp-package-485/Challenge.lean');c=b[:b.index('namespace ArithmeticThetaPalomarComponent485')]
c=c.replace('universe u\n','universe u v\n');c+='open TopologicalSpace MonoidalCategory\n'
a=read(w/'evidence/relative-alpha-package-442/Challenge.lean');c+=re.sub(r'def nsmul.*?abbrev idPoint','abbrev idPoint',a[a.index('namespace WeierstrassProjModel.RelativeGroupLaw'):a.index('open NeronModelInfra\nnamespace GoodReductionJacobian')],flags=re.S)
a=read(w/'evidence/arbitrary-rigidification-package-484/Challenge.lean');start=a.index('structure Scheme.Modules.IsInvertible');end=a.index('instance Scheme.Hom.opensMapFinal',start);c+='namespace AlgebraicGeometry\n'+a[start:end]+'end AlgebraicGeometry\n'
c+=ns('AlgebraicGeometry.Scheme.Hom',cut('Definitions/Def_AlgebraicGeometry_KaehlerModule','variable {A :','def topDifferentials')+cut('Definitions/Def_AlgebraicGeometry_KaehlerModule','def kaehlerToSections (','def kaehlerToSectionsₗ'))
c+=ns('AlgebraicGeometry.Scheme.Modules','variable {X Y : Scheme.{u}} (φ : X ⟶ Y) {L : Y.Modules} {U : Y.Opens}\n'+cut('Definitions/Def_AlgebraicGeometry_ModulesPullbackLocalSection','def pullbackLocalSection','lemma pullbackLocalSection_def'))
c+=ns('ArithmeticThetaSheafTensor',cut('ActualSheafTensor','variable (X :','def tensorUnitMap').replace('local instance : MonoidalCategory','local instance instMonoidalCategoryPresheafOfModules_actualSheafTensor : MonoidalCategory'))
c+=ns('ArithmeticThetaTensorPower',cut('TensorPowerDefinitions','def tensorPower (','/-- The unit sheaf'),'ArithmeticThetaSheafTensor')
c+=ns('ArithmeticThetaRelativeDiscriminantR0171',cut('RelativeDiscriminantDefinitionsR0171','abbrev Hodge (','def localDifferential')+'''def baseMap (R : Type u) [CommRing R] (S : Type u) [CommRing S] (ι : R →+* S) : Base S ⟶ Base R := Spec.map (CommRingCat.ofHom ι)
''','ArithmeticThetaRelativeKatoR0169 ArithmeticThetaTensorPower')
f='P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq';n='P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull'
t=cut(f,'section Main','lemma k1_kaehlerToSections')+'end Main\n';c+=ns(n,t)
t='''section DifferentialMap
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {X Y : Scheme.{u}}
    (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B)) (φ : X ⟶ Y)
    (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
'''+cut('RelativeHodgePowerBaseChangeR0171','def differentialMap :','/-- Its value')+cut('RelativeHodgePowerBaseChangeR0171','theorem differentialMap_isIso','  letI : IsIso (θ')+'  sorry\nend DifferentialMap\n'
t+='variable {X Y : Scheme.{u}}\n'+cut('RelativeHodgePowerBaseChangeR0171','def pullbackEqIso','theorem pullbackEqIso_section')+cut('RelativeHodgePowerBaseChangeR0171','def squarePullbackIso','theorem squarePullbackIso_section')+cut('RelativeHodgePowerBaseChangeR0171','section PointedComparison','theorem pointedDifferentialIso_D')+'end PointedComparison\n'
c+=ns('ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange',t,n)
t=cut('OpenHodgeDescentDefinitionsR0180','abbrev zero','/-- Constructed affine charts')+cut('OpenHodgeDescentDefinitionsR0180','def comparison {','def powerComparison')
c+=ns('ArithmeticThetaOpenHodgeR0180',t,'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower')
c+=ns('ArithmeticThetaCompatibleLevelR0178','variable (k : Type u) [Field k] (L : ℕ) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L)\n'+cut('CompatibleLevelDefinitionsR0178','def Classifies','/-- The existing local comparison'),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175')
c+=ns('ArithmeticThetaTateSeries',cut('TateSeriesDefinitions','variable {k :','/-- Q=t^d'))
c+=ns('ArithmeticThetaCubicModelR0144','variable (k : Type u) [Field k] [CharZero k]\n'+cut('CubicModelDefinitionsR0144','def rootSeries','def rootAt'))
c+=ns('ArithmeticThetaCompactifiedDifferentialR0145','variable (k : Type u) [Field k] [CharZero k]\n'+cut('CompactifiedDifferentialDefinitionsR0145','def root (','def origin (')+cut('CompactifiedDifferentialDefinitionsR0145','def relativeD','def differentialAt'),'ArithmeticThetaCubicModelR0144')
t='''section ChartEquiv
variable {B : Type u} [CommRing B] {C : Scheme.{u}} (i : Spec (CommRingCat.of B) ⟶ C) [IsOpenImmersion i]
'''+cut('GlobalNormalizedDifferentialR0145','def chartRingEquiv :','lemma chartRingEquiv_algebraMap')
t+='''end ChartEquiv
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
variable {C : Scheme.{u}} (E : C ≅ projectiveCurve k r)
abbrev zLeg := chartInclusion k r ≫ E.inv
instance zLeg_open : IsOpenImmersion (zLeg k r E) := by dsimp [zLeg, chartInclusion]; infer_instance
abbrev zOpen : C.Opens := zLeg k r E ''ᵁ ⊤
abbrev zSection : ChartRing k r ≃+* Γ(C, zOpen k r E) := (chartRingEquiv (zLeg k r E)).symm
'''
c+=ns('ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential',t)
t=cut('TateCuspDefinitionsR0181','variable (k :','/-- Every nonidentity combination')+cut('TateCuspDefinitionsR0181','def Extends','abbrev CuspStalk')
c+=ns('ArithmeticThetaTateCuspsR0181',t,'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLevelCompactificationR0179')
t=cut('BoundaryHodgeDefinitionsR0182','variable (k :','def pullAmbientPower')+cut('BoundaryHodgeDefinitionsR0182','structure Extension','def restrictPower')
c+=ns('ArithmeticThetaBoundaryHodgeR0182',t,'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaOpenHodgeR0180 ArithmeticThetaTensorPower')
t='''variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
theorem componentIsOpen (x : X.space) : IsOpen (irreducibleComponent x) := by sorry
''';c+=ns('ArithmeticThetaPalomarComponent485',t,'ArithmeticThetaLevelCompactificationR0179')
t='''variable (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D)
def compactComponent (x : X.space) : X.space.Opens := ⟨irreducibleComponent x, ArithmeticThetaPalomarComponent485.componentIsOpen k L D X x⟩
''';c+=ns('ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182',t,'ArithmeticThetaLevelCompactificationR0179')
t=cut('ComponentDegreeDefinitionsR0184','variable (k :','instance componentIntegral')
t+='''theorem componentIntegral : IsIntegral (Component k L D X x) := by sorry
attribute [instance] componentIntegral
theorem componentLocallyNoetherian : IsLocallyNoetherian (Component k L D X x) := by sorry
attribute [instance] componentLocallyNoetherian
'''+cut('ComponentDegreeDefinitionsR0184','def cuspSet','def restrict (')
c+=ns('ArithmeticThetaComponentDegreeR0184',t,'ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower')
t=cut('LineRootGluing','structure LocalFrame','variable {R :')+'''variable (X : Scheme.{u}) [IsIntegral X]
'''+cut('LineRootGluing','structure NormalFrameCover','variable {X} {H :')+'''instance {X : Scheme.{u}} [IsIntegral X] {H : X.Modules} {ι : Type v} (C : NormalFrameCover X H ι) (i : ι) : Nonempty (C.opens i) := C.nonempty i
''';c+=ns('ArithmeticThetaLineRoot',t)
c+=ns('ArithmeticThetaNormalizedSections',cut('NormalizedSectionDefinitions','def sectionCoordinate','/-- Coefficient of an actual tensor-power'),'ArithmeticThetaLineRoot')
c+=ns('ArithmeticThetaSectionOrder',cut('SectionOrderDefinitions','def localOrder','/-- Vanishing of all coefficients'),'ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections')
c+=ns('ArithmeticThetaCurveDegree',cut('CurveDegreeDefinitions','def baseToResidue','def OneDimensionalCharts')+cut('CurveDegreeDefinitions','def weightedDegree','def MatchesPrincipalOrder'))
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-031');claim='theorem componentHodgePowerDegree :\n'+o['type']+' := by\n'
c+=ns('ArithmeticThetaPalomarHodge495',claim+'  sorry\n')
s='''module
public import ComponentHodgePowerDegreeR0184
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory AlgebraicGeometry
'''
s+=ns('ArithmeticThetaPalomarComponent485',t if False else '''theorem componentIsOpen (k : Type) [Field k] [CharZero k] (L : ℕ) (D : LevelData k L) (X : Compactification k L D) (x : X.space) : IsOpen (irreducibleComponent x) := by
  exact (ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.compactComponent k L D X x).isOpen
''','ArithmeticThetaLevelCompactificationR0179')
s+=ns('ArithmeticThetaPalomarHodge495',claim+'  exact ArithmeticThetaComponentDegreeR0184.component_hodge_power_degree\n'+ 'theorem recover_original_031 :\n'+o['type']+' := componentHodgePowerDegree\n')
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(w/'evidence/component-cusp-package-485/comparator.json'));cfg['theorem_names'].remove('ArithmeticThetaPalomarComponent485.geometricComponentCuspBound');cfg['theorem_names']+=['ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap_isIso','ArithmeticThetaComponentDegreeR0184.componentIntegral','ArithmeticThetaComponentDegreeR0184.componentLocallyNoetherian','ArithmeticThetaPalomarHodge495.componentHodgePowerDegree'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/component-cusp-package-485/compile.py').read_bytes())
