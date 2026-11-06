from pathlib import Path
import re,json,ast,hashlib,shutil
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';b=p.parent/'compact-unary-package-514';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
marker='namespace ArithmeticThetaPalomarUnary514\ntheorem compactUnaryHodgeRealization'
c=read(b/'Challenge.lean');c=c[:c.rindex(marker)]
s=read(b/'Solution.lean');s=s[:s.rindex(marker)];s=s.replace('public import CompactUnaryHodgeRealizationR0183','public import FieldCompactUnaryR0236')
# Canonical conormal on every ideal section, with its proven exact original map.
for kind in ['Challenge','Solution']:
 t=read(p.parent/'canonical-conormal-map-436'/(kind+'.lean'));t=t[t.index('namespace ArithmeticThetaPalomarDifferential365'):]
 if kind=='Challenge':c+=t
 else:s+=t
c+=ns('AlgebraicGeometry','variable {X Y : Scheme.{u}}\n'+cut('Definitions/Def_AlgebraicGeometry_IdealSheafModule','abbrev Scheme.Hom.unitToPushforwardUnit','namespace Scheme.IdealSheafData'))
c+=ns('AlgebraicGeometry.Scheme.IdealSheafData','variable {X : Scheme.{u}}\n'+cut('Definitions/Def_AlgebraicGeometry_IdealSheafModule','def module (','def invModule').replace('𝟙_ X.Modules','SheafOfModules.unit X.ringCatSheaf'),'CategoryTheory.Limits')
c+=ns('ArithmeticThetaLocalWeierstrassR0203','abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)\n'+cut('LocalWeierstrassDefinitionsR0203','structure SchemeLaw','/-- An actual open affine presentation'),'CategoryTheory.Limits NeronModelInfra')
c+=ns('ArithmeticThetaSchemeLevelR0204',cut('SchemeLevelDefinitionsR0204','def multiple','/-- Compatibility with multiplication')+cut('SchemeLevelDefinitionsR0204','variable (k :','/-- Actual affine local classifying'),'CategoryTheory.Limits NeronModelInfra ArithmeticThetaLocalWeierstrassR0203')
c+=ns('ArithmeticThetaSchemeLevelR0204.GlobalSchemeClassifier',cut('GlobalSchemeClassifierR0204','def universalFamily','variable {k :'),'ArithmeticThetaLocalWeierstrassR0203')
# Original conormal/pointed comparisons; rename only definitions using chosen equivalent derivative.
h=cut('SchemeHodgeDefinitionsR0205','abbrev Cotangent','/-- Reuse the canonical affine')
h=h.replace('ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap','ArithmeticThetaPalomarConormal436.conormalMap')
t=read(src/'SchemeHodgeDefinitionsR0205.lean');a=t.index('variable (k :');z=t.index('/-- Naturality keeps',a);h+=t[a:z]
common=ns('ArithmeticThetaPalomarField519.Hodge',h,'ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange')
l=cut('LevelConstantsDefinitionsR0234','abbrev constants','/-- The module is explicitly');common+=ns('ArithmeticThetaPalomarField519.Level',l,'CategoryTheory.Limits ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaPalomarField519.Hodge')
t='variable {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l]\n'+cut('BoundaryConstantsDefinitionsR0235','def CompactCompatible','/-- Exact normalized differentials')+cut('BoundaryConstantsDefinitionsR0235','def GeometricallyCanonical','end ArithmeticThetaBoundaryConstantsR0235')
t=t.replace('ArithmeticThetaLevelConstantsR0234.Extends','ArithmeticThetaPalomarField519.Level.Extends')
common+=ns('ArithmeticThetaPalomarField519.Boundary',t,'ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaPalomarField519.Level')
c+=common;s+=common
# semantic equations of the normalized classifier, then both geometric-canonical predicates.
s+=ns('ArithmeticThetaPalomarField519','''theorem classifierHodge_iff_original {k : Type u} [Field k] [CharZero k] (L : ℕ) (A : ArithmeticThetaLegendreAtlasR0176.LegendreAtlas k L) (B : ArithmeticThetaCompatibleLevelR0178.TwoMarking k L A) (C : ArithmeticThetaCompatibleLevelR0178.CompatibleCover k L A B) (Q : ArithmeticThetaCompatibleLevelR0178.CompatibleQuotient k L A B C) {S : Scheme.{u}} (E : ArithmeticThetaLocalWeierstrassR0203.Family S) (b : S ⟶ ArithmeticThetaLocalWeierstrassR0203.Base Q.quotient.ring) (f : E.curve ⟶ A.descent.family.curve) (e : (Scheme.Modules.pullback b).obj (Hodge.ModularHodge k L A B C Q) ≅ Hodge.Cotangent E) : Hodge.ClassifierHodge k L A B C Q E b f e ↔ ArithmeticThetaSchemeHodgeR0205.ClassifierHodge k L A B C Q E b f e := by
  simp only [Hodge.ClassifierHodge, ArithmeticThetaSchemeHodgeR0205.ClassifierHodge, Hodge.affineDifferential, ArithmeticThetaSchemeHodgeR0205.affineDifferential, ArithmeticThetaPalomarConormal436.conormalMap_eq_original]
  rfl
theorem hodgeCompatible_iff_original {k l : Type} [Field k] [CharZero k] [Field l] [CharZero l] {L : ℕ} (ι : k →+* l) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (E : ArithmeticThetaLevelCompactificationR0179.LevelData l L) (f : ArithmeticThetaLevelCompactificationR0179.OpenBase l L E ⟶ ArithmeticThetaLevelCompactificationR0179.OpenBase k L D) (e : (Scheme.Modules.pullback f).obj (Level.weight D) ≅ Level.weight E) : Level.HodgeCompatible ι D E f e ↔ ArithmeticThetaLevelConstantsR0234.HodgeCompatible ι D E f e := by
  simp only [Level.HodgeCompatible, ArithmeticThetaLevelConstantsR0234.HodgeCompatible, classifierHodge_iff_original]
theorem geometric_iff_original {k : Type} [Field k] [CharZero k] {L : ℕ} {D : ArithmeticThetaLevelCompactificationR0179.LevelData k L} {X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D} (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X) : Boundary.GeometricallyCanonical H ↔ ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical H := by
  simp only [Boundary.GeometricallyCanonical, ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical, hodgeCompatible_iff_original]
  rfl
''')
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-069');typ=o['type'].replace('ArithmeticThetaCompactUnaryR0183.OpenPower','ArithmeticThetaPalomarUnary514.OpenPower').replace('ArithmeticThetaCompactUnaryR0183.RealizesUnary','ArithmeticThetaPalomarUnary514.RealizesUnary').replace('ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical','ArithmeticThetaPalomarField519.Boundary.GeometricallyCanonical');claim='theorem fieldCompactUnary : '+typ+' := by\n'
c+=ns('ArithmeticThetaPalomarField519',claim+'  sorry\n')
s+=ns('ArithmeticThetaPalomarField519',claim+'''  intro k _ _ m N hm hmeven hN hNeven hmN D X H hH hgH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := ArithmeticThetaArithmeticSectionsR0236.field_compact_unary k m N hm hmeven hN hNeven hmN D X H hH ((geometric_iff_original H).mp hgH) ν hν
  refine ⟨a,b,ha,hb,ArithmeticThetaPalomarUnary514.ofOriginal k m N A, ?_⟩
  simpa only [ArithmeticThetaPalomarUnary514.realizes_ofOriginal] using hA
'''+ 'theorem recover_original_069 : '+o['type']+''' := by
  intro k _ _ m N hm hmeven hN hNeven hmN D X H hH hgH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := fieldCompactUnary k m N hm hmeven hN hNeven hmN D X H hH ((geometric_iff_original H).mpr hgH) ν hν
  refine ⟨a,b,ha,hb,ArithmeticThetaPalomarUnary514.toOriginal k m N A, ?_⟩
  simpa only [ArithmeticThetaPalomarUnary514.realizes_toOriginal] using hA
''')
tree=ast.parse(read(p.parent/'period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for n,t in [('Challenge',c),('Solution',s)]:
 t=t.replace('open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory','open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory')
 (p/(n+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(n+'.lean')).write_text(v);print(n,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-1:] = ['ArithmeticThetaPalomarConormal436.canonicalConormalMap','ArithmeticThetaPalomarField519.fieldCompactUnary'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
for n in ['compile.py','compact.py']:shutil.copyfile(b/n,p/n)
