from pathlib import Path
import re,json,hashlib,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
base=w/'evidence/phase-free-multiplier-package-450';c=read(base/'Challenge.uncompressed.lean.txt');s=read(base/'Solution.uncompressed.lean.txt').replace('public import','public import PhaseFreeAlphaDescentR0219\npublic import SchemeDiscriminantExistenceR0244\npublic import',1)
bc=read(w/'evidence/canonical-binary-tensor-458/Challenge.lean');bs=read(w/'evidence/canonical-binary-tensor-458/Solution.lean')
c+='open MonoidalCategory\n'+bc[bc.index('namespace ArithmeticThetaSheafTensor'):];s+=bs[bs.index('namespace ArithmeticThetaPalomarBinaryTensor458'):]
ident=read(w/'evidence/full-scheme-discriminant-385/Challenge.lean');start=ident.index('namespace ArithmeticThetaPalomarIdentity357\n');idbody=ident[start:ident.index('end ArithmeticThetaPalomarIdentity357',start)+len('end ArithmeticThetaPalomarIdentity357')]+'\n';c+=idbody;s+=idbody
head='''namespace ArithmeticThetaPalomarAlphaDescent459
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219
open ArithmeticThetaSheafTensor ArithmeticThetaPalomarIdentity357 ArithmeticThetaPalomarBinaryTensor458
open ArithmeticThetaPalomarSchemeAlpha437
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
def productLine (L : S.Modules) : S.Modules := sheafTensor S (cotangent E) L
def tensorComparison (L : S.Modules) (A : MarkedTest E P)
    (c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family) :
    (Scheme.Modules.pullback A.map).obj (productLine E L) ≅
      sheafTensor A.base (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) :=
  (canonicalBinaryTensor A.map (cotangent E) L (cotangent A.family)
    ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _)).exists.choose
def Descends (L : S.Modules) (m : Frames E P L) (β : Γ(productLine E L, ⊤)) : Prop :=
  ∀ A : MarkedTest E P,
    (∃ c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c) ∧
    (∃ a : Γ(cotangent A.family, ⊤), RealizesAlpha A.family A.marking a) ∧
    ∀ c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family,
      CotangentCompatible E A.family A.map A.comparison A.cartesian.2.1 c →
      ∀ a : Γ(cotangent A.family, ⊤), RealizesAlpha A.family A.marking a →
      (tensorComparison E P L A c).hom.app ⊤
        (ArithmeticThetaPullback.pullbackGlobalSection A.map (productLine E L) β) =
        tensorSection A.base (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) ⊤ a (m A)
''';c+=head;s+=head
s+='''theorem cotangentCompatible_iff {T : Scheme.{u}} (F : Family T) (b : T ⟶ S)
    (f : F.curve ⟶ E.curve) (hz : F.zero ≫ f = b ≫ E.zero)
    (e : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F) :
    CotangentCompatible E F b f hz e ↔ ArithmeticThetaSchemeHodgeR0205.CotangentCompatible E F b f hz e := Iff.rfl
theorem tensorComparison_eq_original (L : S.Modules) (A : MarkedTest E P)
    (c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family) :
    tensorComparison E P L A c =
      ArithmeticThetaPullback.pullback_sheafTensor_iso A.base S A.map (ArithmeticThetaSchemeHodgeR0205.Cotangent E) L ≪≫
        ArithmeticThetaPullback.sheafTensorCongr A.base c (Iso.refl _) := by
  exact (compatible_iff_original A.map (cotangent E) L (cotangent A.family)
    ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _) _).mp
      (canonicalBinaryTensor A.map (cotangent E) L (cotangent A.family)
        ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _)).exists.choose_spec
theorem descends_iff (L : S.Modules) (m : Frames E P L) (β : Γ(productLine E L, ⊤)) :
    Descends E P L m β ↔ ArithmeticThetaPhaseFreeKeyR0219.Descends E P L m β := by
  simp only [Descends, ArithmeticThetaPhaseFreeKeyR0219.Descends, cotangentCompatible_iff,
    realizesAlpha_iff, tensorComparison_eq_original]
  rfl
'''
obs=json.loads(read(w/'project/docs/SourceObligations.json'));o=next(x for x in obs if x['id']=='accepted-096');typ=o['type'].replace('ArithmeticThetaMultiplierKeyR0217.productLine','productLine').replace('ArithmeticThetaPhaseFreeKeyR0219.Descends','Descends');d='theorem phaseFreeAlphaDescent :\n'+typ+' := by\n';c+=d+'  sorry\n';s+=d+'''  intro k _ _ S σ E P L m hm
  have h := ArithmeticThetaPhaseFreeKeyR0219.phase_free_alpha_descent k S σ E P L m hm
  convert h using 1 <;> simp only [descends_iff] <;> rfl
'''
s+='theorem recover_original_096 :\n'+o['type']+' := by\n'+'''  intro k _ _ S σ E P L m hm
  have h := phaseFreeAlphaDescent k S σ E P L m hm
  convert h using 1 <;> simp only [descends_iff] <;> rfl
'''
c+='end ArithmeticThetaPalomarAlphaDescent459\n';s+='end ArithmeticThetaPalomarAlphaDescent459\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(base/'comparator.json'));cfg['theorem_names']+=['ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor','ArithmeticThetaPalomarAlphaDescent459.phaseFreeAlphaDescent'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((base/'compile.py').read_bytes())
