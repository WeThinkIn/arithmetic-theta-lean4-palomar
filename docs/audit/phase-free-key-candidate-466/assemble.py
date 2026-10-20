from pathlib import Path
import ast, hashlib, json, re
p=Path(__file__).resolve().parent; w=p.parent.parent; inputs={}
def read(f):
    inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest(); return f.read_text()
base=w/'evidence/phase-free-alpha-descent-package-459'
c=read(base/'Challenge.uncompressed.lean.txt')
s=read(base/'Solution.uncompressed.lean.txt').replace('public import','public import PhaseFreeKeyNaturalityR0219\npublic import',1)
dual=w/'evidence/actual-dual-evaluation-465'
dc=read(dual/'Challenge.lean'); ds=read(dual/'Solution.lean')
# Isolate copied universe and local notation scopes without importing project modules.
c+='\nsection ActualDualLayer\n'+dc[dc.index('set_option autoImplicit false'):].replace('universe u v\' u\'','universe v\' u\'')+'\nend\nend\nend ActualDualLayer\n'
s+=ds[ds.index('namespace ArithmeticThetaPalomarDual465'):]
t=read(w/'evidence/multiplier-fourth-package-454/Challenge.uncompressed.lean.txt')
tp=t[t.index('namespace ArithmeticThetaTensorPower\n'):t.index('end ArithmeticThetaTensorPower')+len('end ArithmeticThetaTensorPower')]+'\n'
c+=tp
unit=read(w/'project/Proof/Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean')
c+='namespace AlgebraicGeometry\n'+unit[unit.index('instance Scheme.Hom.opensMapFinal'):unit.index('theorem Scheme.Modules.isInvertible_unit')]+'end AlgebraicGeometry\n'
src=read(w/'project/Proof/MultiplierKeyDefinitionsR0217.lean')
defs=src[src.index('def thetaIdeal'):src.index('\nvariable (D : Cover E)')]
defs=defs.replace('Scheme.Modules.ihomGlobalSectionsEquiv','ArithmeticThetaPalomarDual465.globalSectionsEquiv')
head='''namespace ArithmeticThetaPalomarKey466
open CategoryTheory MonoidalCategory AlgebraicGeometry
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216
open ArithmeticThetaTensorPower ArithmeticThetaSheafTensor ArithmeticThetaPullback
open ArithmeticThetaPalomarAlphaDescent459 ArithmeticThetaPalomarIdentity357
variable {S : Scheme.{u}} (E : Family S) (P : EvenPoint E)
'''
key=src[src.index('def IsKey'):src.index('\nvariable {T : Scheme.{u}}')]
extra='''
variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F) (b : T ⟶ S)
def productComparison (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F)
    (v : (Scheme.Modules.pullback b).obj L ≅ K) :
    (Scheme.Modules.pullback b).obj (productLine E L) ≅ productLine F K :=
  (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor b (cotangent E) L
    (cotangent F) K c v).exists.choose
def AlphaNatural (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F)
    (v : (Scheme.Modules.pullback b).obj L ≅ K)
    (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine F K, ⊤)) : Prop :=
  (productComparison E F b L K c v).hom.app ⊤
    (pullbackGlobalSection b (productLine E L) β) = γ
def EvaluationSquareCompatible
    (eS : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules))
    (eT : (Scheme.Modules.pullback F.zero).obj (thetaLine F Q) ≅ (𝟙_ T.Modules))
    (j : (Scheme.Modules.pullback b).obj (inverseSquare E P) ≅ inverseSquare F Q) : Prop :=
  j.hom.app ⊤ (pullbackGlobalSection b (inverseSquare E P) (evaluationSquare E P eS)) =
    evaluationSquare F Q eT
'''
c+=head+defs+key+extra
s+=head+defs+key+extra
s+='''theorem evaluationSection_eq_original
    (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) :
    evaluationSection E P e = ArithmeticThetaMultiplierKeyR0217.evaluationSection E P e := by
  exact ArithmeticThetaPalomarDual465.evaluationSection_eq_original _ _ _
theorem evaluationSquare_eq_original
    (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules)) :
    evaluationSquare E P e = ArithmeticThetaMultiplierKeyR0217.evaluationSquare E P e := by
  unfold evaluationSquare ArithmeticThetaMultiplierKeyR0217.evaluationSquare
  rw [evaluationSection_eq_original]
  rfl
theorem isKey_iff (L : S.Modules)
    (e : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules))
    (β : Γ(productLine E L, ⊤)) (κ : inverseSquare E P ≅ productLine E L) :
    IsKey E P L e β κ ↔ ArithmeticThetaMultiplierKeyR0217.IsKey E P L e β κ := by
  unfold IsKey ArithmeticThetaMultiplierKeyR0217.IsKey
  rw [evaluationSquare_eq_original]
  rfl
theorem productComparison_eq_original (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F)
    (v : (Scheme.Modules.pullback b).obj L ≅ K) :
    productComparison E F b L K c v = ArithmeticThetaMultiplierKeyR0217.productComparison E F b L K c v :=
  (ArithmeticThetaPalomarBinaryTensor458.compatible_iff_original b (cotangent E) L
    (cotangent F) K c v _).mp
      (ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor b (cotangent E) L
        (cotangent F) K c v).exists.choose_spec
theorem alphaNatural_iff (L : S.Modules) (K : T.Modules)
    (c : (Scheme.Modules.pullback b).obj (cotangent E) ≅ cotangent F)
    (v : (Scheme.Modules.pullback b).obj L ≅ K)
    (β : Γ(productLine E L, ⊤)) (γ : Γ(productLine F K, ⊤)) :
    AlphaNatural E F b L K c v β γ ↔ ArithmeticThetaMultiplierKeyR0217.AlphaNatural E F b L K c v β γ := by
  unfold AlphaNatural ArithmeticThetaMultiplierKeyR0217.AlphaNatural
  rw [productComparison_eq_original]
  rfl
theorem evaluationSquareCompatible_iff
    (eS : (Scheme.Modules.pullback E.zero).obj (thetaLine E P) ≅ (𝟙_ S.Modules))
    (eT : (Scheme.Modules.pullback F.zero).obj (thetaLine F Q) ≅ (𝟙_ T.Modules))
    (j : (Scheme.Modules.pullback b).obj (inverseSquare E P) ≅ inverseSquare F Q) :
    EvaluationSquareCompatible E P F Q b eS eT j ↔
      ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible E P F Q b eS eT j := by
  unfold EvaluationSquareCompatible ArithmeticThetaMultiplierKeyR0217.EvaluationSquareCompatible
  rw [evaluationSquare_eq_original, evaluationSquare_eq_original]
  rfl
'''
obs=json.loads(read(w/'project/docs/SourceObligations.json'))
for ident,name,args in [('accepted-053','phaseFreeKey','k _ _ S σ E P L m hm β hβ e he'),('accepted-054','phaseFreeKeyNaturality','k _ _ S σ E P L m hm T F Q b f hb hQ K n hn c hc v hv β γ hβ hγ')]:
    o=next(x for x in obs if x['id']==ident)
    typ=o['type']
    for old,new in {
      'ArithmeticThetaMultiplierKeyR0217.productLine':'ArithmeticThetaPalomarAlphaDescent459.productLine',
      'ArithmeticThetaPhaseFreeKeyR0219.Descends':'ArithmeticThetaPalomarAlphaDescent459.Descends',
      'ArithmeticThetaSchemeHodgeR0205.CotangentCompatible':'ArithmeticThetaPalomarIdentity357.CotangentCompatible',
      'ArithmeticThetaSchemeHodgeR0205.Cotangent':'ArithmeticThetaPalomarIdentity357.cotangent'
    }.items(): typ=typ.replace(old,new)
    typ=typ.replace('ArithmeticThetaMultiplierKeyR0217.','ArithmeticThetaPalomarKey466.')
    c+='theorem '+name+' :\n'+typ+' := by\n  sorry\n'
    simp='[ArithmeticThetaPalomarAlphaDescent459.descends_iff, isKey_iff, alphaNatural_iff, evaluationSquareCompatible_iff, productComparison_eq_original]'
    originalargs=args.replace(' _ _','')
    # The premises Descends have a compiled equivalence; all other assumptions retain exact definitions.
    origprem=originalargs.replace('hβ','((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mp hβ)').replace('hγ','((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mp hγ)')
    s+='theorem '+name+' :\n'+typ+' := by\n  intro '+args+'\n  have h := '+o['declaration']+' '+origprem+'\n  convert h using 1 <;> (try simp only '+simp+') <;> rfl\n'
    reverse=originalargs.replace('hβ','((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mpr hβ)').replace('hγ','((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mpr hγ)')
    s+='theorem recover_original_'+ident[-3:]+' :\n'+o['type']+' := by\n  intro '+args+'\n  have h := '+name+' '+reverse+'\n  convert h using 1 <;> (try simp only '+simp+') <;> rfl\n'
c+='end ArithmeticThetaPalomarKey466\n';s+='end ArithmeticThetaPalomarKey466\n'
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
    (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t)
    assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v)
    (p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(base/'comparator.json'));cfg['theorem_names']+=['SheafOfModules.presheafW_isMonoidal','ArithmeticThetaPalomarDual465.canonicalGlobalSectionsEquiv','ArithmeticThetaPalomarKey466.phaseFreeKey','ArithmeticThetaPalomarKey466.phaseFreeKeyNaturality']
(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
(p/'compile.py').write_text(read(base/'compile.py'))
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
