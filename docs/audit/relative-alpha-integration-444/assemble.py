from pathlib import Path
import re,ast,json,hashlib
r=Path(__file__).resolve().parent;e=r.parent;project=e.parent/'project';inputs={}
def read(p):
 inputs[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest();return p.read_text()
def span(s,a,b):
 i=s.index(a);return s[i:s.index(b,i)]
c=read(e/'scheme-alpha-character-package-437/Challenge.uncompressed.lean.txt')
s=read(e/'scheme-alpha-character-package-437/Solution.uncompressed.lean.txt')
pc=read(e/'pointed-differential-comparison-387/Challenge.lean');ps=read(e/'pointed-differential-comparison-387/Solution.lean');bridge=read(e/'pointed-differential-comparison-387/Bridge.lean')
c+=pc[pc.index('namespace ArithmeticThetaPalomarPointed387'):]
s+='''section PointedProvider442
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange
namespace ArithmeticThetaPointedComparison387
'''+bridge[bridge.index('section Pointed'):]+ 'end PointedProvider442\n'
s+=ps[ps.index('namespace ArithmeticThetaPalomarPointed387'):]
base='''namespace ArithmeticThetaRelativeDiscriminantR0171
def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (s : Γ(F, U)) : Γ(F, V) := F.presheaf.map (homOfLE h).op s
def IsFrame {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (s : Γ(F,U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective (fun a : Γ(X,V) => a • res F h s)
def baseMap (R : Type u) [CommRing R] (S : Type u) [CommRing S] (ι : R →+* S) : Base S ⟶ Base R :=
  Spec.map (CommRingCat.ofHom ι)
end ArithmeticThetaRelativeDiscriminantR0171
namespace ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaRelativeKatoR0169
variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (G : Law R W)
variable (S : Type u) [CommRing S] [IsDomain S] (Ws : WeierstrassCurve S) (Gs : Law S Ws)
'''+span(read(project/'Proof/RelativeKatoNaturalityDefinitionsR0170.lean'),'def IsBaseChange','variable [IsIntegral (Curve S Ws)]')+'end ArithmeticThetaRelativeKatoNaturalityR0170\n'
c+=base
head='''namespace ArithmeticThetaPalomarRelativeAlpha442
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
theorem weierstrassSmooth : SmoothOfRelativeDimension 1 (structureMap R W) := by
'''
c+=head+'  sorry\n';s+=head+'  exact (relative_curve_geometry R W).2.2.2.2.2.1\n'
defs='''variable (G : Law R W) (S : Type u) [CommRing S] [IsDomain S]
  (Ws : WeierstrassCurve S) (Gs : Law S Ws) (ι : R →+* S)
  (b : Curve S Ws ⟶ Curve R W)
  (hb : ArithmeticThetaRelativeKatoNaturalityR0170.IsBaseChange R W G S Ws Gs ι b)
def hodgeComparison :
    (Scheme.Modules.pullback (baseMap R S ι)).obj (Hodge R W) ≅ Hodge S Ws := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := weierstrassSmooth R W
  exact (ArithmeticThetaPalomarPointed387.pointed_comparison_exists_unique
    (structureMap R W) (structureMap S Ws) b hb.1 (origin R W) (origin S Ws) hb.2.1).exists.choose
def pullAlpha (a : Γ(Hodge R W, ⊤)) : Γ(Hodge S Ws, ⊤) :=
  (hodgeComparison R W G S Ws Gs ι b hb).hom.app ⊤
    (ArithmeticThetaPullback.pullbackGlobalSection (baseMap R S ι) (Hodge R W) a)
'''
c+=defs;s+=defs
s+='''omit [IsDomain S] in
theorem hodgeComparison_eq_original :
    hodgeComparison R W G S Ws Gs ι b hb =
      ArithmeticThetaGlobalFourTorsionR0190.hodgeComparison R W G S Ws Gs ι b hb := by
  letI : Algebra R S := ι.toAlgebra
  letI : SmoothOfRelativeDimension 1 (structureMap R W) := weierstrassSmooth R W
  exact (ArithmeticThetaPalomarPointed387.pointed_compatible_iff
    (structureMap R W) (structureMap S Ws) b hb.1 (origin R W) (origin S Ws) hb.2.1 _).mp
      (ArithmeticThetaPalomarPointed387.pointed_comparison_exists_unique
        (structureMap R W) (structureMap S Ws) b hb.1 (origin R W) (origin S Ws) hb.2.1).exists.choose_spec
omit [IsDomain S] in
theorem pullAlpha_eq_original (a : Γ(Hodge R W,⊤)) :
    pullAlpha R W G S Ws Gs ι b hb a =
      ArithmeticThetaGlobalFourTorsionR0190.pullAlpha R W G S Ws Gs ι b hb a := by
  unfold pullAlpha
  rw [hodgeComparison_eq_original]
  rfl
'''
obs={x['id']:x for x in json.loads(read(project/'docs/SourceObligations.json'))}
for id,name in [('accepted-038','relativeFourTorsionRoot'),('accepted-039','relativeAlphaNaturality')]:
 o=obs[id];typ=o['type'].replace('ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha','ArithmeticThetaPalomarAffineAlpha437.RealizesAlpha').replace('ArithmeticThetaGlobalFourTorsionR0190.pullAlpha','pullAlpha')
 declaration='theorem '+name+' :\n'+typ+' := by\n';c+=declaration+'  sorry\n';s+=declaration
 if id=='accepted-038':s+='  exact ArithmeticThetaGlobalFourTorsionR0190.relative_four_torsion_root\n'
 else:s+='''  intro R _ _ _ _ _ W _ G hG L hL h4 M
  simpa only [ArithmeticThetaPalomarSchemeAlpha437.affineAlpha_iff, pullAlpha_eq_original] using
    (ArithmeticThetaGlobalFourTorsionR0190.relative_alpha_naturality R W G hG L hL h4 M)
'''
 s+='theorem recover_original_'+id[-3:]+' :\n'+o['type']+' := by\n'
 if id=='accepted-038':s+='  exact relativeFourTorsionRoot\n'
 else:s+='''  intro R _ _ _ _ _ W _ G hG L hL h4 M
  simpa only [ArithmeticThetaPalomarSchemeAlpha437.affineAlpha_iff, pullAlpha_eq_original] using
    (relativeAlphaNaturality R W G hG L hL h4 M)
'''
c+='end ArithmeticThetaPalomarRelativeAlpha442\n';s+='end ArithmeticThetaPalomarRelativeAlpha442\n'
tree=ast.parse((e/'period-one-package-404/assemble.py').read_text());fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (r/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);assert re.sub(r'\s+','',fmt['uncomment'](t))==re.sub(r'\s+','',v);(r/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(e/'scheme-alpha-character-package-437/comparator.json'));cfg['theorem_names']+=['ArithmeticThetaPalomarPointed387.pointed_comparison_exists_unique','ArithmeticThetaPalomarRelativeAlpha442.weierstrassSmooth','ArithmeticThetaPalomarRelativeAlpha442.relativeFourTorsionRoot','ArithmeticThetaPalomarRelativeAlpha442.relativeAlphaNaturality'];(r/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(r/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
