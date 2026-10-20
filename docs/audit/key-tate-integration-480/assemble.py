from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
b=w/'evidence/compact-key-surface-469';c=read(b/'Challenge.lean');s=read(b/'Solution.lean').replace('public import Mathlib','public import Mathlib\npublic import PhaseFreeKeyTateNormalizationR0220',1)
c=c[:c.index('variable {T : Scheme.{u}} (F : Family T) (Q : EvenPoint F) (b : T ⟶ S)',c.index('namespace ArithmeticThetaPalomarKey466'))]+'end ArithmeticThetaPalomarKey466\n'
c=re.sub(r'/-! Full original053/054.*?-/', '',c,flags=re.S)
t=read(w/'evidence/tate-alpha-package-445/Challenge.lean');extra=t[t.index('namespace ArithmeticThetaTateSeries\n'):t.index('namespace ArithmeticThetaPalomarTateAlpha445')]
# res already occurs in the key interface.
a=extra.index('namespace ArithmeticThetaRelativeDiscriminantR0171\ndef res');z=extra.index('end ArithmeticThetaRelativeDiscriminantR0171',a)+len('end ArithmeticThetaRelativeDiscriminantR0171\n');extra=extra[:a]+extra[z:]
c+=extra
bound=extra[extra.index('namespace ArithmeticThetaPalomarBoundary445'):];s+=bound
head='''namespace ArithmeticThetaPalomarAffineHodge478
open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204 ArithmeticThetaSchemeFourCharacterR0215 ArithmeticThetaPalomarSchemeAlpha437
open ArithmeticThetaPalomarDifferential365
variable {S : Scheme.{u}} (E : Family S) (M : FullLevel E 4) (P : AffineTest E M)
'''
ideal='''theorem idealComparison : ∃! i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker, ArithmeticThetaPalomarSchemeAlpha437.AffineIdealCompatible E M P i := by
'''
defi='''def idealIso := (idealComparison E M P).exists.choose
'''
isiso='''theorem hodgeIsIso (i : (Scheme.Modules.pullback P.comparison).obj (idealModule E.zero.ker) ≅ idealModule (ArithmeticThetaRelativeKatoR0169.origin P.ring P.equation).ker) : IsIso (ArithmeticThetaPalomarSchemeAlpha437.affineHodgeMap E M P i) := by
'''
hodge='''def hodgeIso : (Scheme.Modules.pullback P.base).obj (ArithmeticThetaPalomarSchemeAlpha437.Cotangent E) ≅ ArithmeticThetaRelativeDiscriminantR0171.Hodge P.ring P.equation := by
  letI := hodgeIsIso E M P (idealIso E M P)
  exact asIso (ArithmeticThetaPalomarSchemeAlpha437.affineHodgeMap E M P (idealIso E M P))
'''
c+=head+ideal+'  sorry\n'+defi+isiso+'  sorry\n'+hodge+'end ArithmeticThetaPalomarAffineHodge478\n'
s+=head+ideal+'''  exact ArithmeticThetaSchemeFourCharacterR0215.MarkedAffineTestComparison.ideal_comparison E M P
'''+defi+isiso+'''  rw [ArithmeticThetaPalomarSchemeAlpha437.affineHodgeMap_eq]
  exact ArithmeticThetaSchemeFourCharacterR0215.MarkedAffineTestComparison.hodge_isIso E M P i
'''+hodge+'''theorem idealIso_eq_original : idealIso E M P = ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.idealIso E M P := by
  apply (ArithmeticThetaSchemeFourCharacterR0215.MarkedAffineTestComparison.ideal_comparison E M P).choose_spec.2
  exact (idealComparison E M P).exists.choose_spec
theorem hodgeIso_eq_original : hodgeIso E M P = ArithmeticThetaSchemeFourCharacterR0215.SchemeAlphaSection.hodgeIso E M P := by
  apply Iso.ext
  change ArithmeticThetaPalomarSchemeAlpha437.affineHodgeMap E M P (idealIso E M P) = _
  rw [ArithmeticThetaPalomarSchemeAlpha437.affineHodgeMap_eq, idealIso_eq_original]
  rfl
end ArithmeticThetaPalomarAffineHodge478
'''
t=read(w/'project/Proof/KeyTateDefinitionsR0220.lean');defs=t[t.index('namespace ArithmeticThetaKeyTateR0220'):]
defs=defs.replace('ArithmeticThetaKeyTateR0220','ArithmeticThetaPalomarKeyTate478').replace('ArithmeticThetaSchemeHodgeR0205','ArithmeticThetaPalomarIdentity357').replace('ArithmeticThetaMultiplierKeyR0217','ArithmeticThetaPalomarAlphaDescent459').replace('Cotangent','cotangent').replace('SchemeAlphaSection.hodgeIso','ArithmeticThetaPalomarAffineHodge478.hodgeIso').replace('ArithmeticThetaBoundaryHodgeR0182','ArithmeticThetaPalomarBoundary445')
start=defs.index('  let first :=');end=defs.index('\n/-- The target frame',start)
defs=defs[:start]+'''  let first := ((ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor A.map
    (cotangent E) L (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L) c (Iso.refl _)).exists.choose).hom.app ⊤
      (pullbackGlobalSection A.map (productLine E L) s)
  ((ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor B.base
    (cotangent A.family) ((Scheme.Modules.pullback A.map).obj L)
    (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k N))
    (tateMultiplier k N T E P L A B) (ArithmeticThetaPalomarAffineHodge478.hodgeIso A.family A.marking (B.affine k N T))
    (Iso.refl _)).exists.choose).hom.app ⊤ (pullbackGlobalSection B.base _ first)
'''+defs[end:]
# Reuse the original structural TateTest name in the Challenge; Solution imports it.
prefix=defs[:defs.index('/-- The conormal-to-Hodge')].replace('ArithmeticThetaPalomarKeyTate478','ArithmeticThetaKeyTateR0220')
c+=prefix+'end ArithmeticThetaKeyTateR0220\n'
body=defs[defs.index('variable {S : Scheme} (E : Family S)'):]
header=defs[:defs.index('/-- The actual level-four')]+ 'open ArithmeticThetaKeyTateR0220\nvariable (k : Type) [Field k] [CharZero k] (N : ℕ) (T : ArithmeticThetaTateCuspsR0181.TateLevel k N)\n'
defs=header+body
c+=defs;s+=defs
s+='''namespace ArithmeticThetaPalomarBinaryTensor458
theorem canonical_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) (H K : Y.Modules) (M N : X.Modules) (e : (Scheme.Modules.pullback f).obj H ≅ M) (d : (Scheme.Modules.pullback f).obj K ≅ N) :
    (canonicalBinaryTensor f H K M N e d).exists.choose = ArithmeticThetaPullback.pullback_sheafTensor_iso X Y f H K ≪≫ ArithmeticThetaPullback.sheafTensorCongr X e d :=
  (compatible_iff_original f H K M N e d _).mp (canonicalBinaryTensor f H K M N e d).exists.choose_spec
end ArithmeticThetaPalomarBinaryTensor458
namespace ArithmeticThetaPalomarKeyTate478
open CategoryTheory AlgebraicGeometry ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaEvenMarkingTorsorR0216 ArithmeticThetaPhaseFreeKeyR0219 ArithmeticThetaPalomarIdentity357 ArithmeticThetaPalomarAlphaDescent459 ArithmeticThetaKeyTateR0220
variable (k : Type) [Field k] [CharZero k] (N : ℕ) (T : ArithmeticThetaTateCuspsR0181.TateLevel k N)
variable {S : Scheme} (E : Family S) (P : EvenPoint E) (L : S.Modules) (A : MarkedTest E P) (B : TateTest k N T A.family A.marking)
theorem productAt_eq_original (c : (Scheme.Modules.pullback A.map).obj (cotangent E) ≅ cotangent A.family) (s : Γ(productLine E L, ⊤)) :
    productAt k N T E P L A B c s = ArithmeticThetaKeyTateR0220.productAt k N T E P L A B c s := by
  unfold productAt
  rw [ArithmeticThetaPalomarBinaryTensor458.canonical_eq_original, ArithmeticThetaPalomarBinaryTensor458.canonical_eq_original, ArithmeticThetaPalomarAffineHodge478.hodgeIso_eq_original]
  rfl
end ArithmeticThetaPalomarKeyTate478
'''
obs=json.loads(read(w/'project/docs/SourceObligations.json'));o=next(x for x in obs if x['id']=='accepted-055');typ=o['type']
for old,new in {
'ArithmeticThetaMultiplierKeyR0217.productLine':'ArithmeticThetaPalomarAlphaDescent459.productLine',
'ArithmeticThetaPhaseFreeKeyR0219.Descends':'ArithmeticThetaPalomarAlphaDescent459.Descends',
'ArithmeticThetaSchemeHodgeR0205.CotangentCompatible':'ArithmeticThetaPalomarIdentity357.CotangentCompatible',
'ArithmeticThetaSchemeHodgeR0205.Cotangent':'ArithmeticThetaPalomarIdentity357.cotangent',
'ArithmeticThetaMultiplierKeyR0217.':'ArithmeticThetaPalomarKey466.',
'ArithmeticThetaBoundaryHodgeR0182.':'ArithmeticThetaPalomarBoundary445.',
'ArithmeticThetaKeyTateR0220.':'ArithmeticThetaPalomarKeyTate478.'}.items():typ=typ.replace(old,new)
typ=typ.replace('ArithmeticThetaPalomarKeyTate478.TateTest','ArithmeticThetaKeyTateR0220.TateTest')
name='ArithmeticThetaPalomarKeyTate478.phaseFreeKeyTateNormalization'
c+='theorem '+name+' :\n'+typ+' := by sorry\n'
args='k _ _ N hN h4 T S E P L m hm β hβ e he κ hκ A B c hc δ hδ';actual=args.replace(' _ _','')
s+='theorem '+name+' :\n'+typ+''' := by
  intro '''+args+'''
  have h := ArithmeticThetaKeyTateR0220.phase_free_key_tate_normalization '''+actual.replace('hβ','((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mp hβ)').replace('hκ','((ArithmeticThetaPalomarKey466.isKey_iff _ _ _ _ _ _).mp hκ)')+'''
  rw [ArithmeticThetaPalomarKey466.evaluationSquare_eq_original, ArithmeticThetaPalomarKeyTate478.productAt_eq_original]
  exact h
'''
s+='theorem ArithmeticThetaPalomarKeyTate478.recover_original_055 :\n'+o['type']+''' := by
  intro '''+args+'''
  have h := '''+name+' '+actual.replace('hβ','((ArithmeticThetaPalomarAlphaDescent459.descends_iff _ _ _ _ _).mpr hβ)').replace('hκ','((ArithmeticThetaPalomarKey466.isKey_iff _ _ _ _ _ _).mpr hκ)')+'''
  rw [ArithmeticThetaPalomarKey466.evaluationSquare_eq_original, ArithmeticThetaPalomarKeyTate478.productAt_eq_original] at h
  exact h
'''
tree=ast.parse((w/'evidence/period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if not n.startswith('ArithmeticThetaPalomarKey466.phaseFreeKey')]+['ArithmeticThetaPalomarAffineHodge478.idealComparison','ArithmeticThetaPalomarAffineHodge478.hodgeIsIso',name if False else 'ArithmeticThetaPalomarKeyTate478.phaseFreeKeyTateNormalization'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
