from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
b=read(w/'evidence/component-hodge-degree-package-495/Challenge.lean');c=b[:b.index('namespace ArithmeticThetaPalomarComponent485')]
c+=ns('ArithmeticThetaFullLevelCoverR0175','variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)\n'+cut('FullLevelCoverDefinitionsR0175','def coordinatePoint','def torsionStructure'),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171')
c+=ns('ArithmeticThetaLegendreComparisonR0177',cut('LegendreComparisonDefinitionsR0177','def chartScalar','def HasCoordinates'),'ArithmeticThetaRelativeKatoR0169')
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','def scalar','/-- Local-frame formula'),'ArithmeticThetaRelativeDiscriminantR0171')
c+=ns('ArithmeticThetaPullback','''def pullbackGlobalSection {X Y : Scheme.{u}} (p : X ⟶ Y) (M : Y.Modules) : Γ(M, ⊤) → Γ((Scheme.Modules.pullback p).obj M, p ⁻¹ᵁ (⊤ : Y.Opens)) :=
  fun s => ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤ s
''')
c+=ns('ArithmeticThetaTateCuspsR0181','variable (k : Type u) [Field k] [CharZero k] (L : ℕ)\n'+cut('TateCuspDefinitionsR0181','def CanonicalMarking','/-- The actual invariant'),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaFullLevelCoverR0175')
c+=ns('ArithmeticThetaTateSeries',cut('TateSeriesDefinitions','def theta (','/-- Exact equality of all coefficients'))
t=cut('GlobalFourTorsionDefinitionsR0190','variable (R :','section BaseChange')+cut('GlobalFourTorsionDefinitionsR0190','section LevelBase','end ArithmeticThetaGlobalFourTorsionR0190')
c+=ns('ArithmeticThetaGlobalFourTorsionR0190',t,'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaFullLevelCoverR0175 ArithmeticThetaLegendreComparisonR0177 ArithmeticThetaTensorPower ArithmeticThetaPullback')
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-041');claim='theorem compactFullLevelAlpha :\n'+o['type']+' := by\n';c+=ns('ArithmeticThetaPalomarCompactAlpha501',claim+'  sorry\n')
s='''module
public import CompactFullLevelAlphaR0190
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
'''+ns('ArithmeticThetaPalomarCompactAlpha501',claim+'  exact ArithmeticThetaGlobalFourTorsionR0190.compact_full_level_alpha\n'+'theorem recover_original_041 :\n'+o['type']+' := compactFullLevelAlpha\n')
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(w/'evidence/component-hodge-degree-package-495/comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if not n.startswith(('ArithmeticThetaComponentDegreeR0184.','ArithmeticThetaPalomarComponent485.','ArithmeticThetaPalomarHodge495.'))]+['ArithmeticThetaPalomarCompactAlpha501.compactFullLevelAlpha'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((w/'evidence/component-hodge-degree-package-495/compile.py').read_bytes())
