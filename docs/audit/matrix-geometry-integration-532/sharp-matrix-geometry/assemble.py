from pathlib import Path
import re,json,hashlib,shutil,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;b=p.parent/'split-square-degree-package-516';src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):t=read(src/(f+'.lean'));return t[t.index(a):t.index(z,t.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
c=read(b/'Challenge.lean');c=c[:c.index('namespace ArithmeticThetaPalomarSplit516')]
s=read(p.parent/'field-unary-package-519/Solution.lean');s=s[:s.index('namespace ArithmeticThetaPalomarD2_509.HodgeBaseChange')];s=s.replace('public import FieldCompactUnaryR0236','public import SharpMatrixGeometricFamilyR0195\npublic import SharpGeometricCutoffR0195')
v=read(p.parent/'field-unary-package-519/Challenge.lean');a=v.index('namespace ArithmeticThetaSheafTensor\nvariable (X : Scheme.{u})\ndef tensorUnitMap');z=v.index('namespace ArithmeticThetaGeometricNormR0150',a);c+=v[a:z]
c+=ns('ArithmeticThetaTensorPower',cut('TensorPowerDefinitions','def tensorProductSection','end ArithmeticThetaTensorPower'),'ArithmeticThetaSheafTensor')
c+=ns('ArithmeticThetaPullback',cut('PullbackTensorSections','def pullbackGlobalSection','theorem pullbackGlobalSection_def') if False else '''def pullbackGlobalSection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) : Γ(M, ⊤) → Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ (⊤ : Y.Opens)) := fun s => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s''')
c+=ns('ArithmeticThetaCommonHalfHodgeR0185',cut('CommonHalfHodgeDefinitionsR0185','def along','def pullSquare'))
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','def scalar','/-- Local-frame formula'),'ArithmeticThetaRelativeDiscriminantR0171')
c+=ns('ArithmeticThetaCompactUnaryR0183','abbrev level (N : ℕ) : ℕ := 24*N^2\nabbrev exponent (N : ℕ) : ℕ := (1+12*N)^2-1\nabbrev weight (N : ℕ) : ℕ := exponent N / 2\n')
a=v.index('namespace ArithmeticThetaUnaryProduct\n');z=v.index('end ArithmeticThetaUnaryProduct',a)+len('end ArithmeticThetaUnaryProduct');c+=v[a:z]+'\n'
c+=ns('ArithmeticThetaSimultaneousUnaryR0187',cut('SimultaneousUnaryRootsDefinitionsR0187','abbrev Sections','/-- All degrees refer'))
c+=ns('ArithmeticThetaComputed',cut('IntegrationDefinitions','def validGram','def coefficientMatrix')+cut('IntegrationDefinitions','noncomputable def thetaMap','noncomputable def prefixMap'))
c+=ns('ArithmeticThetaOrthogonalAlgorithm',cut('OrthogonalAlgorithm','def pairing','def indexValue'))
c+=ns('ArithmeticThetaOrthogonalConsumerR0127',cut('OrthogonalConsumerDefinitionsR0127','def castVec','def OrthogonalData'))
geoopens='ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181 ArithmeticThetaSquareLinesR0192 ArithmeticThetaSharpCoverR0194 ArithmeticThetaTensorPower ArithmeticThetaPullback ArithmeticThetaSimultaneousUnaryR0187 ArithmeticThetaNormalizedSections ArithmeticThetaLatticeSectionsR0188 ArithmeticThetaCompactUnaryR0183 ArithmeticThetaCommonHalfHodgeR0185'
c+=ns('ArithmeticThetaLatticeSectionsR0188',cut('LatticeGlobalSectionsDefinitionsR0188','abbrev Matrices','/-- Actual pullback')+cut('LatticeGlobalSectionsDefinitionsR0188','def baseScalar','/-- The common geometric realization'),'ArithmeticThetaOrthogonalAlgorithm ArithmeticThetaOrthogonalConsumerR0127 ArithmeticThetaCompactUnaryR0183 ArithmeticThetaSimultaneousUnaryR0187')
c+=ns('ArithmeticThetaSharpKernelR0195',cut('SharpKernelDefinitionsR0195','def norms','structure NormIndex')+cut('SharpKernelDefinitionsR0195','def cutoff','/-- Actual common disk frame'),geoopens)
c+=ns('ArithmeticThetaSectionOrder',cut('SectionOrderDefinitions','def VanishesThrough','end ArithmeticThetaSectionOrder'))
# Only canonical tensor-comparison expressions are renamed; equality bridges below.
t=cut('SquareLineComparisonDefinitionsR0192','def squarePull','/-- Equality of the two actual')+cut('SimultaneousUnaryRootsDefinitionsR0187','def squareOnDisk','/-- An iterated power comparison')+cut('NormalizedSectionDefinitions','def pullbackPowerSection','/-- A local frame') if False else cut('SquareLineComparisonDefinitionsR0192','def squarePull','/-- Equality of the two actual')+cut('SimultaneousUnaryRootsDefinitionsR0187','def squareOnDisk','/-- An iterated power comparison')+cut('NormalizedSectionDefinitions','def pullbackPowerSection','def FramePullbackCompatible')
t=t.replace('ArithmeticThetaPullback.pullback_tensorPower_iso','ArithmeticThetaPalomarHalf505.powerComparison').replace('pullback_tensorPower_iso','ArithmeticThetaPalomarHalf505.powerComparison')
common=ns('ArithmeticThetaPalomarSharp529',t,geoopens);c+=common;s+=common
common=ns('ArithmeticThetaPalomarSharp529',cut('SharpKernelDefinitionsR0195','structure CoverFrame','/-- Equality as rational sections')+cut('SharpKernelDefinitionsR0195','def GeometricFamily','/-- The existing exact elimination certificate').replace('normCount A','ArithmeticThetaSharpKernelR0195.normCount A'),geoopens);c+=common;s+=common
s+=ns('ArithmeticThetaPalomarSharp529','''theorem squarePull_eq_original {Z Y : Scheme} {W : Z.Modules} (f : Y ⟶ Z) (A : SquareLine Z W) : squarePull f A = ArithmeticThetaSquareLinesR0192.squarePull f A := by
  simp only [squarePull, ArithmeticThetaSquareLinesR0192.squarePull, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem squareOnDisk_eq_original (k : Type) [Field k] {B X : Scheme} (p : B ⟶ X) (J : B.Modules) (H : X.Modules) (β : tensorPower B J 2 ≅ (Scheme.Modules.pullback p).obj H) (f : Disk k ⟶ B) (d : Disk k ⟶ X) (hf : f ≫ p = d) : squareOnDisk k p J H β f d hf = ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk k p J H β f d hf := by
  simp only [squareOnDisk, ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem pullbackPowerSection_eq_original {Y X : Scheme.{u}} (p : Y ⟶ X) (H : X.Modules) (n : ℕ) (F : Γ(tensorPower X H n, ⊤)) : pullbackPowerSection p H n F = ArithmeticThetaNormalizedSections.pullbackPowerSection p H n F := by
  simp only [pullbackPowerSection, ArithmeticThetaNormalizedSections.pullbackPowerSection, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
variable (k : Type) [Field k] [CharZero k] (N : ℕ) {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (J : SquareLine (Component k (level N) D X (V.disk (closedPoint k))) (hodge k (level N) D X (V.disk (closedPoint k)) H)) (b : ℕ) (C : RootCover k (Component k (level N) D X (V.disk (closedPoint k))) (projection k (level N) D X (V.disk (closedPoint k))) b)
def frameToOriginal (F : CoverFrame k N H V J b C) : ArithmeticThetaSharpKernelR0195.CoverFrame k N H V J b C where
  disk := F.disk
  triangle := F.triangle
  dominant := F.dominant
  frame := F.frame
  isFrame := F.isFrame
  generator := F.generator
  extendsGenerator := F.extendsGenerator
  square_eq := by simpa only [squareOnDisk_eq_original, squarePull_eq_original] using F.square_eq
def frameOfOriginal (F : ArithmeticThetaSharpKernelR0195.CoverFrame k N H V J b C) : CoverFrame k N H V J b C where
  disk := F.disk
  triangle := F.triangle
  dominant := F.dominant
  frame := F.frame
  isFrame := F.isFrame
  generator := F.generator
  extendsGenerator := F.extendsGenerator
  square_eq := by simpa only [squareOnDisk_eq_original, squarePull_eq_original] using F.square_eq
''',geoopens)
s+=ns('ArithmeticThetaPalomarSharp529','''theorem geometric_iff_original {n h : ℕ} (A : Matrices n h) (U : Indexing A) {D : LevelData ℂ (level (commonN A))} {X : Compactification ℂ (level (commonN A)) D} (H : Extension ℂ (level (commonN A)) D X) (V : DiskTest ℂ (level (commonN A)) D X) : GeometricFamily A U H V ↔ ArithmeticThetaSharpKernelR0195.GeometricFamily A U H V := by
  constructor
  · rintro ⟨J,C,het,hiso,hdeg,F,t,σ,ht,hσ,hexp⟩
    refine ⟨J,C,het,hiso,hdeg,frameToOriginal ℂ _ H V J _ C F,t,σ,ht,hσ,?_⟩
    simpa only [frameToOriginal, pullbackPowerSection_eq_original] using hexp
  · rintro ⟨J,C,het,hiso,hdeg,F,t,σ,ht,hσ,hexp⟩
    refine ⟨J,C,het,hiso,hdeg,frameOfOriginal ℂ _ H V J _ C F,t,σ,ht,hσ,?_⟩
    simpa only [frameOfOriginal, pullbackPowerSection_eq_original] using hexp
''',geoopens)
obs=json.loads(read(w/'project/docs/SourceObligations.json'));names=[]
for i,n in [('047','sharpMatrixGeometricFamily'),('048','sharpGeometricCutoff')]:
 o=next(x for x in obs if x['id']=='accepted-'+i);typ=o['type'].replace('ArithmeticThetaSharpKernelR0195.GeometricFamily','ArithmeticThetaPalomarSharp529.GeometricFamily');claim='theorem '+n+' : '+typ+' := by\n';c+=ns('ArithmeticThetaPalomarSharp529',claim+'  sorry\n');s+=ns('ArithmeticThetaPalomarSharp529',claim+'  simpa only [geometric_iff_original] using '+o['declaration']+'\n'+'theorem recover_original_'+i+' : '+o['type']+' := by\n  simpa only [geometric_iff_original] using '+n+'\n');names.append('ArithmeticThetaPalomarSharp529.'+n)
tree=ast.parse(read(p.parent/'period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for n,t in [('Challenge',c),('Solution',s)]:
 (p/(n+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(n+'.lean')).write_text(v);print(n,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-1:]=['ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor']+names;(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');targets='['+', '.join('``'+n for n in cfg['theorem_names'])+']'
b2=p.parent/'field-unary-package-519'
for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','TargetTypeAudit','TargetHoleAudit']:
 t=read(b2/(n+'.lean')).replace(str(b2),str(p));t=re.sub(r'let targets : List Name := \[.*\]',lambda m:'let targets : List Name := '+targets,t);(p/(n+'.lean')).write_text(t)
t='module\nimport all Solution\nset_option maxRecDepth 8192\nset_option backward.isDefEq.respectTransparency false\n'
for i in ['047','048']:
 o=next(x for x in obs if x['id']=='accepted-'+i);t+='example : ArithmeticThetaPalomarSharp529.recover_original_'+i+' = '+o['declaration']+' := by rfl\n'
t+='\n'.join('#print axioms '+n for n in names)+'\n#print axioms ArithmeticThetaPalomarSharp529.geometric_iff_original\n';(p/'OriginalEndpointAudit.lean').write_text(t)
for n in ['compile.py','finalize.py','compact.py','pack_fields.py']:shutil.copyfile(b2/n,p/n)
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
