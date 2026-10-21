from pathlib import Path
import re,json,hashlib,shutil,ast
p=Path(__file__).resolve().parent;w=p.parent.parent;b=p.parent/'field-unary-package-519';src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
marker='namespace ArithmeticThetaPalomarField519\ntheorem fieldCompactUnary'
c=read(b/'Challenge.lean');c=c[:c.rindex(marker)];s=read(b/'Solution.lean');s=s[:s.rindex(marker)]
for kind,t in [('Challenge',c),('Solution',s)]:
 t=re.sub(r'namespace ArithmeticThetaPalomarUnary514.BoundaryHodge\n.*?end ArithmeticThetaPalomarUnary514.BoundaryHodge\n','',t,flags=re.S)
 a=t.index('def DiskCoefficient');z=t.index('end ArithmeticThetaPalomarUnary514',a);t=t[:a]+t[z:]
 if kind=='Solution':
  a=t.index('theorem diskCoefficient_iff_original');z=t.index('end ArithmeticThetaPalomarUnary514',a);t=t[:a]+t[z:]
 if kind=='Challenge':c=t
 else:s=t
opens='ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower ArithmeticThetaPalomarField519.Level'
record='variable (k : Type) [Field k] [CharZero k] (L : ℕ)\nvariable {l : Type} [Field l] [CharZero l]\n'+cut('GeometricCanonicalHodgeDescentR0235','structure CoefficientMap','lemma coefficientMap_exists');record=record.replace('ArithmeticThetaLevelConstantsR0234.Extends','ArithmeticThetaPalomarField519.Level.Extends')
common=ns('ArithmeticThetaPalomarNaturality525',record,opens);c+=common;s+=common
transport=cut('OpenDiscriminantFullTateExpansionR0182','def transportSection','lemma transportSection_injective')+cut('ArithmeticSectionsDefinitionsR0236','def powerTransport','/-- Full discriminant realization');transport=transport.replace('ArithmeticThetaBoundaryHodgeR0182.OpenDiscriminantFullTateExpansionR0182.transportSection','transportSection').replace('(tensorComparison f','(ArithmeticThetaPalomarD2_509.HodgeBaseChange.tensorComparison f')
common=ns('ArithmeticThetaPalomarNaturality525',transport,opens+' ArithmeticThetaRelativeDiscriminantR0171');c+=common;s+=common
bridges='''variable (k : Type) [Field k] [CharZero k] (L : ℕ)
variable {l : Type} [Field l] [CharZero l] (ι : k →+* l)
variable {D : LevelData k L} {E : LevelData l L} {X : Compactification k L D} {Y : Compactification l L E}
def toOriginal (C : CoefficientMap k L ι D E X Y) : ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y where
  openMap := C.openMap
  compactMap := C.compactMap
  classifies := C.classifies
  extendsOpen := C.extendsOpen
  hodgeMap := C.hodgeMap
  normalized := (ArithmeticThetaPalomarField519.hodgeCompatible_iff_original ι D E C.openMap C.hodgeMap).mp C.normalized
def ofOriginal (C : ArithmeticThetaArithmeticSectionsR0236.Comparison k L ι D E X Y) : CoefficientMap k L ι D E X Y where
  openMap := C.openMap
  compactMap := C.compactMap
  classifies := C.classifies
  extendsOpen := C.extendsOpen
  hodgeMap := C.hodgeMap
  normalized := (ArithmeticThetaPalomarField519.hodgeCompatible_iff_original ι D E C.openMap C.hodgeMap).mpr C.normalized
theorem compactCompatible_iff_original (f : OpenBase l L E ⟶ OpenBase k L D) (F : Y.space ⟶ X.space) (hF : ArithmeticThetaPalomarField519.Level.Extends ι D E X Y f F) (e : (Scheme.Modules.pullback f).obj (weight D) ≅ weight E) (H : Extension k L D X) (J : Extension l L E Y) (a : (Scheme.Modules.pullback F).obj H.line ≅ J.line) : ArithmeticThetaPalomarField519.Boundary.CompactCompatible ι f F hF e H J a ↔ ArithmeticThetaBoundaryConstantsR0235.CompactCompatible ι f F hF e H J a := by rfl
'''
s+=ns('ArithmeticThetaPalomarNaturality525',bridges,opens)
s+=ns('ArithmeticThetaPalomarNaturality525','''theorem powerTransport_eq_original {X Y : Scheme.{0}} (f : Y ⟶ X) (M : X.Modules) (N : Y.Modules) (e : (Scheme.Modules.pullback f).obj M ≅ N) (n : ℕ) (s : Γ(tensorPower X M n, ⊤)) : powerTransport f M N e n s = ArithmeticThetaArithmeticSectionsR0236.powerTransport f M N e n s := by
  simp only [powerTransport, ArithmeticThetaArithmeticSectionsR0236.powerTransport, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original]
  rfl
''',opens)
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-070');typ=o['type']
for a,z in [('ArithmeticThetaArithmeticSectionsR0236.Comparison','ArithmeticThetaPalomarNaturality525.CoefficientMap'),('ArithmeticThetaBoundaryConstantsR0235.GeometricallyCanonical','ArithmeticThetaPalomarField519.Boundary.GeometricallyCanonical'),('ArithmeticThetaBoundaryConstantsR0235.CompactCompatible','ArithmeticThetaPalomarField519.Boundary.CompactCompatible'),('ArithmeticThetaCompactUnaryR0183.OpenPower','ArithmeticThetaPalomarUnary514.OpenPower'),('ArithmeticThetaBoundaryHodgeR0182.restrictPower','ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower'),('ArithmeticThetaBoundaryHodgeR0182.pullToOpen','ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen'),('ArithmeticThetaArithmeticSectionsR0236.powerTransport','ArithmeticThetaPalomarNaturality525.powerTransport')]:typ=typ.replace(a,z)
claim='theorem fieldUnaryCompactNaturality : '+typ+' := by\n';c+=ns('ArithmeticThetaPalomarNaturality525',claim+'  sorry\n')
rewrites='[ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]'
body='''  intro k l _ _ _ _ ι m N hm hmeven hN hNeven hmN D E X Y C H J hH hgH hJ hgJ a b hab A A' s t hs ht
  have hs' : ArithmeticThetaBoundaryHodgeR0182.restrictPower k (ArithmeticThetaCompactUnaryR0183.level N) H (ArithmeticThetaCompactUnaryR0183.weight N) s = ArithmeticThetaBoundaryHodgeR0182.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_ := by
    simpa only REWRITES using hs
  have ht' : ArithmeticThetaBoundaryHodgeR0182.restrictPower l (ArithmeticThetaCompactUnaryR0183.level N) J (ArithmeticThetaCompactUnaryR0183.weight N) t = ArithmeticThetaBoundaryHodgeR0182.pullToOpen l (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A'.section_ := by
    simpa only REWRITES using ht
  have h := ArithmeticThetaArithmeticSectionsR0236.field_unary_compact_naturality k l ι m N hm hmeven hN hNeven hmN D E X Y (toOriginal k _ ι C) H J hH ((ArithmeticThetaPalomarField519.geometric_iff_original H).mp hgH) hJ ((ArithmeticThetaPalomarField519.geometric_iff_original J).mp hgJ) a b hab (ArithmeticThetaPalomarUnary514.toOriginal k m N A) (ArithmeticThetaPalomarUnary514.toOriginal l m N A') s t hs' ht'
  simpa only [toOriginal, compactCompatible_iff_original, powerTransport_eq_original] using h
'''.replace('REWRITES',rewrites)
reverse='''  intro k l _ _ _ _ ι m N hm hmeven hN hNeven hmN D E X Y C H J hH hgH hJ hgJ a b hab A A' s t hs ht
  have hs' : ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower k (ArithmeticThetaCompactUnaryR0183.level N) H (ArithmeticThetaCompactUnaryR0183.weight N) s = ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen k (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A.section_ := by
    simpa only REWRITES using hs
  have ht' : ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower l (ArithmeticThetaCompactUnaryR0183.level N) J (ArithmeticThetaCompactUnaryR0183.weight N) t = ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen l (ArithmeticThetaCompactUnaryR0183.level N) (ArithmeticThetaCompactUnaryR0183.weight N) A'.section_ := by
    simpa only REWRITES using ht
  have h := fieldUnaryCompactNaturality k l ι m N hm hmeven hN hNeven hmN D E X Y (ofOriginal k _ ι C) H J hH ((ArithmeticThetaPalomarField519.geometric_iff_original H).mpr hgH) hJ ((ArithmeticThetaPalomarField519.geometric_iff_original J).mpr hgJ) a b hab (ArithmeticThetaPalomarUnary514.ofOriginal k m N A) (ArithmeticThetaPalomarUnary514.ofOriginal l m N A') s t hs' ht'
  simpa only [ofOriginal, compactCompatible_iff_original, powerTransport_eq_original] using h
'''.replace('REWRITES',rewrites)
s+=ns('ArithmeticThetaPalomarNaturality525',claim+body+'theorem recover_original_070 : '+o['type']+' := by\n'+reverse)
tree=ast.parse(read(p.parent/'period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for n,t in [('Challenge',c),('Solution',s)]:
 (p/(n+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(n+'.lean')).write_text(v);print(n,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names'][-1]='ArithmeticThetaPalomarNaturality525.fieldUnaryCompactNaturality';(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');targets='['+', '.join('``'+n for n in cfg['theorem_names'])+']'
for n in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','TargetTypeAudit','TargetHoleAudit']:
 t=read(b/(n+'.lean')).replace(str(b),str(p));t=re.sub(r'let targets : List Name := \[.*\]',lambda m:'let targets : List Name := '+targets,t);(p/(n+'.lean')).write_text(t)
(p/'OriginalEndpointAudit.lean').write_text('module\nimport all Solution\nset_option maxRecDepth 8192\nset_option backward.isDefEq.respectTransparency false\nexample : ArithmeticThetaPalomarNaturality525.recover_original_070 = '+o['declaration']+' := by rfl\n#print axioms ArithmeticThetaPalomarNaturality525.fieldUnaryCompactNaturality\n#print axioms ArithmeticThetaPalomarNaturality525.powerTransport_eq_original\n#print axioms ArithmeticThetaPalomarField519.geometric_iff_original\n')
for n in ['compile.py','finalize.py','compact.py','pack_fields.py']:shutil.copyfile(b/n,p/n)
(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n')
