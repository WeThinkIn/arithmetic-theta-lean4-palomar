from pathlib import Path
import hashlib, json

p = Path(__file__).resolve().parent
w = p.parent.parent
inputs = {}
def read(f):
    inputs[str(f)] = hashlib.sha256(f.read_bytes()).hexdigest()
    return f.read_text()

internal = read(w/'project/Proof/Definitions/Def_PresheafOfModules_InternalHom.lean')
monoidal = read(w/'project/Proof/Definitions/Def_SheafOfModules_Monoidal.lean')
monoidal = monoidal[monoidal.index('@[expose] public section'):]
monoidal = monoidal.replace('universe u\n', '')
monoidal = monoidal.replace('  PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf 𝒪 (ringSheaf 𝒪 h𝒪) (𝟙 _)','  by sorry')
sections = read(w/'project/Proof/Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean')
sections = sections[sections.index('namespace AlgebraicGeometry.Scheme.Modules'):sections.index('lemma tensorSections_def')]
sections += 'end Sections\nend AlgebraicGeometry.Scheme.Modules\n'
ideal = '''namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
namespace Scheme.IdealSheafData
def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)
def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit
def invModule (I : X.IdealSheafData) : X.Modules := Scheme.Modules.dual I.module
def invModuleSection (I : X.IdealSheafData) : 𝟙_ X.Modules ⟶ I.invModule :=
  MonoidalClosed.curry' I.moduleι
end Scheme.IdealSheafData
end AlgebraicGeometry
'''
for src in ['Def_AlgebraicGeometry_IdealSheafModule','Def_AlgebraicGeometry_ModulesSectionZeroScheme','Def_AlgebraicGeometry_ModulesIhomSections']:
    read(w/f'project/Proof/Definitions/{src}.lean')
head = '''namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
/-- Every open and every local vector fixes the global section-to-morphism map. -/
def Compatible (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) : Prop :=
  ∀ (t : Γ((ihom M).obj N, ⊤)) (U : X.Opens) (m : Γ(M, U)),
    (e t).app U m = ((ihom.ev M).app N).app U
      (Scheme.Modules.tensorSections m (((ihom M).obj N).presheaf.map (homOfLE le_top).op t))
theorem canonicalGlobalSectionsEquiv :
    ∃! e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N), Compatible M N e := by
'''
tail = '''def globalSectionsEquiv : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N) :=
  (canonicalGlobalSectionsEquiv M N).exists.choose
end ArithmeticThetaPalomarDual465
'''
c = internal + '\n' + monoidal + '\nnoncomputable section\n' + sections + ideal + head + '  sorry\n' + tail
s = '''module
public import Mathlib
public import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
public import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
universe u
open CategoryTheory MonoidalCategory Limits Opposite
''' + head + '''  let e := Scheme.Modules.ihomGlobalSectionsEquiv M N
  have he : Compatible M N e := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply AddEquiv.ext
  intro t
  ext U m
  exact (he' t U m).trans (he t U m).symm
''' + tail + '''namespace ArithmeticThetaPalomarDual465
open AlgebraicGeometry
variable {X : Scheme.{u}} (M N : X.Modules)
theorem compatible_iff_original (e : Γ((ihom M).obj N, ⊤) ≃+ (M ⟶ N)) :
    Compatible M N e ↔ e = Scheme.Modules.ihomGlobalSectionsEquiv M N := by
  have he : Compatible M N (Scheme.Modules.ihomGlobalSectionsEquiv M N) := by
    intro t U m
    rw [Scheme.Modules.ihom_ev_app_tensorSections]
    exact Scheme.Modules.ihomGlobalSectionsEquiv_app_apply t U m
  constructor
  · intro h
    exact (canonicalGlobalSectionsEquiv M N).unique h he
  · rintro rfl
    exact he
theorem globalSectionsEquiv_eq_original :
    globalSectionsEquiv M N = Scheme.Modules.ihomGlobalSectionsEquiv M N :=
  (compatible_iff_original M N _).mp (canonicalGlobalSectionsEquiv M N).exists.choose_spec
theorem evaluationSection_eq_original (φ : M ⟶ N) :
    (globalSectionsEquiv M N).symm φ = (Scheme.Modules.ihomGlobalSectionsEquiv M N).symm φ := by
  rw [globalSectionsEquiv_eq_original]
end ArithmeticThetaPalomarDual465
'''
for name, text in [('Challenge', c), ('Solution', s)]:
    (p/f'{name}.lean').write_text(text)
    print(name, len(text.splitlines()))
base = w/'evidence/canonical-binary-tensor-458'
(p/'compile.py').write_text(read(base/'compile.py'))
targets = '``SheafOfModules.presheafW_isMonoidal, ``ArithmeticThetaPalomarDual465.canonicalGlobalSectionsEquiv'
for name in ['ChallengeAudit', 'SolutionAudit']:
    a = read(base/f'{name}.lean').replace('``ArithmeticThetaPalomarBinaryTensor458.canonicalBinaryTensor', targets)
    (p/f'{name}.lean').write_text(a)
a = read(base/'DefinitionCompatibility.lean').replace('canonical-binary-tensor-458', p.name)
(p/'DefinitionCompatibility.lean').write_text(a)
(p/'input-bindings.json').write_text(json.dumps(inputs, indent=2)+'\n')
(p/'comparator.json').write_text(json.dumps({'theorem_names': ['SheafOfModules.presheafW_isMonoidal', 'ArithmeticThetaPalomarDual465.canonicalGlobalSectionsEquiv']},indent=2)+'\n')
