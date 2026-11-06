from pathlib import Path
import ast,re,json,hashlib
p=Path(__file__).resolve().parent;w=p.parent.parent;src=w/'project/Proof';inputs={}
def read(f):inputs[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest();return f.read_text()
def cut(f,a,z):s=read(src/(f+'.lean'));return s[s.index(a):s.index(z,s.index(a))]
def ns(n,t,opens=''):return 'namespace '+n+'\n'+('open '+opens+'\n' if opens else '')+t+'\nend '+n+'\n'
b=w/'evidence/component-discriminant-package-509';marker='namespace ArithmeticThetaPalomarD2_509\ntheorem componentDiscriminantDivisor';c=read(b/'Challenge.lean');c=c[:c.rindex(marker)]
a=c.index('namespace ArithmeticThetaPalomarComponent485');z=c.index('namespace ArithmeticThetaSheafTensor',a);c=c[:a]+c[z:]
a=c.index('namespace ArithmeticThetaPalomarD2_509.NormalizedSections');c=c[:a]
a=c.index('namespace ArithmeticThetaLevelCount');z=c.index('end ArithmeticThetaLevelCount',a)+len('end ArithmeticThetaLevelCount');c=c[:a]+c[z:]
s=read(b/'Solution.lean');s=s[:s.rindex(marker)];s=s.replace('public import ComponentDiscriminantDivisorR0184','public import CompactUnaryHodgeRealizationR0183')
a=s.index('namespace ArithmeticThetaPalomarD2_509.NormalizedSections');z=s.index('namespace ArithmeticThetaPalomarD2_509\n',a);s=s[:a]+s[z:]
a=s.index('theorem compactD2_iff_original');z=s.index('end ArithmeticThetaPalomarD2_509',a);s=s[:a]+s[z:]
c+=ns('ArithmeticThetaFullLevelCoverR0175','variable (R : Type u) [CommRing R] (W : WeierstrassCurve R) (G : Law R W)\n'+cut('FullLevelCoverDefinitionsR0175','def coordinatePoint','def torsionStructure'), 'NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171')
c+=ns('ArithmeticThetaRelativeKatoNaturalityR0170','variable (R : Type u) [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [IsIntegral (Curve R W)]\n'+cut('RelativeKatoNaturalityDefinitionsR0170','def HasValue','end ArithmeticThetaRelativeKatoNaturalityR0170'),'ArithmeticThetaRelativeKatoR0169')
c+=ns('ArithmeticThetaOpenHodgeR0180',cut('OpenHodgeDescentDefinitionsR0180','def IsKatoValue','end ArithmeticThetaOpenHodgeR0180'),'NeronModelInfra ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeKatoNaturalityR0170 ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaTensorPower')
c+=ns('ArithmeticThetaTateCuspsR0181','variable (k : Type u) [Field k] [CharZero k] (L : ℕ)\n'+cut('TateCuspDefinitionsR0181','def CanonicalMarking','/-- The actual invariant'),'ArithmeticThetaRelativeKatoR0169 ArithmeticThetaFullLevelCoverR0175')
a=read(w/'evidence/unary-geometric-package-489/Challenge.lean');z=a.index('namespace ArithmeticThetaUnaryProduct');q=a.index('namespace ArithmeticThetaDiscriminant',z);c+=a[z:q]
c+=ns('ArithmeticThetaUnaryKatoPowerR0160',cut('UnaryKatoPowerDefinitionsR0160','def integerSeries','/-- The displayed D₂'))
c+=ns('ArithmeticThetaBoundaryHodgeR0182',cut('BoundaryHodgeDefinitionsR0182','def unaryResidue','def ExactD2'))
c+=ns('ArithmeticThetaCompactUnaryR0183',cut('CompactUnaryDefinitionsR0183','abbrev level','variable (k :'))
common=ns('ArithmeticThetaPalomarUnary514.BoundaryHodge','variable (k : Type) [Field k] [CharZero k] (L : ℕ)\n'+cut('BoundaryHodgeDefinitionsR0182','def diskPower','/-- The designated source characteristic').replace('ArithmeticThetaPullback.pullback_tensorPower_iso','ArithmeticThetaPalomarHalf505.powerComparison'),'ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaTensorPower ArithmeticThetaTateCuspsR0181 ArithmeticThetaRelativeDiscriminantR0171')
t=cut('CompactUnaryDefinitionsR0183','variable (k :','/-- Membership in the actual integral Tate lattice')+cut('CompactUnaryDefinitionsR0183','def DiskCoefficient','end ArithmeticThetaCompactUnaryR0183')
t=t.replace('ArithmeticThetaOpenHodgeR0180.IsD2','ArithmeticThetaPalomarD2_509.OpenHodge.IsD2').replace('diskPower k','BoundaryHodge.diskPower k').replace('restrictPower k','ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower k').replace('pullToOpen k','ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen k')
opens='ArithmeticThetaCompactUnaryR0183 ArithmeticThetaTensorPower ArithmeticThetaRelativeDiscriminantR0171 ArithmeticThetaLevelCompactificationR0179 ArithmeticThetaTateCuspsR0181 ArithmeticThetaBoundaryHodgeR0182'
common+=ns('ArithmeticThetaPalomarUnary514',t,opens);c+=common;s+=common
var='variable (k : Type) [Field k] [CharZero k] (m N : ℕ)\n'
bridges=''
for name,source,target in [('toOriginal','OpenPower','ArithmeticThetaCompactUnaryR0183.OpenPower'),('ofOriginal','ArithmeticThetaCompactUnaryR0183.OpenPower','OpenPower')]:
 bridges+='def '+name+' {D : LevelData k (level N)} {a b : Fin N} (A : '+source+' k m N D a b) : '+target+' k m N D a b where\n'
 for field in ['quotient','discriminant','value','value_spec','section_','normalized']:bridges+='  '+field+' := A.'+field+'\n'
 bridges+='  intrinsic := (ArithmeticThetaPalomarD2_509.isD2_iff_original _ _).'+('mp' if name=='toOriginal' else 'mpr')+' A.intrinsic\n'
bridges+='''theorem diskCoefficient_iff_original {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (V : DiskTest k (level N) D X) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) (f : PowerSeries k) : DiskCoefficient k N H V s f ↔ ArithmeticThetaCompactUnaryR0183.DiskCoefficient k N H V s f := by
  simp only [DiskCoefficient, ArithmeticThetaCompactUnaryR0183.DiskCoefficient, BoundaryHodge.diskPower, ArithmeticThetaBoundaryHodgeR0182.diskPower, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem realizes_toOriginal {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : RealizesUnary k m N H ν A s ↔ ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν (toOriginal k m N A) s := by
  simp only [RealizesUnary, ArithmeticThetaCompactUnaryR0183.RealizesUnary, toOriginal, diskCoefficient_iff_original, ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
theorem realizes_ofOriginal {D : LevelData k (level N)} {X : Compactification k (level N) D} (H : Extension k (level N) D X) (ν : ℤ) {a b : Fin N} (A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b) (s : Γ(tensorPower X.space H.line (weight N), ⊤)) : RealizesUnary k m N H ν (ofOriginal k m N A) s ↔ ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by
  simp only [RealizesUnary, ArithmeticThetaCompactUnaryR0183.RealizesUnary, ofOriginal, diskCoefficient_iff_original, ArithmeticThetaPalomarD2_509.BoundaryHodge.restrictPower, ArithmeticThetaBoundaryHodgeR0182.restrictPower, ArithmeticThetaPalomarD2_509.BoundaryHodge.pullToOpen, ArithmeticThetaBoundaryHodgeR0182.pullToOpen, ArithmeticThetaPalomarD2_509.tensorComparison_eq_original, ArithmeticThetaPalomarHalf505.powerComparison_eq_original]
'''
s+=ns('ArithmeticThetaPalomarUnary514',var+bridges,opens)
o=next(x for x in json.loads(read(w/'project/docs/SourceObligations.json')) if x['id']=='accepted-028');typ=o['type'].replace('ArithmeticThetaCompactUnaryR0183.OpenPower','ArithmeticThetaPalomarUnary514.OpenPower').replace('ArithmeticThetaCompactUnaryR0183.RealizesUnary','ArithmeticThetaPalomarUnary514.RealizesUnary');claim='theorem compactUnaryHodgeRealization :\n'+typ+' := by\n';c+=ns('ArithmeticThetaPalomarUnary514',claim+'  sorry\n')
s+=ns('ArithmeticThetaPalomarUnary514',claim+'''  intro k _ _ _ m N hm hmeven hN hNeven hmN D X H hH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := ArithmeticThetaCompactUnaryR0183.compact_unary_hodge_realization k m N hm hmeven hN hNeven hmN D X H hH ν hν
  refine ⟨a,b,ha,hb,ofOriginal k m N A, ?_⟩
  simpa only [realizes_ofOriginal] using hA
'''+ 'theorem recover_original_028 :\n'+o['type']+''' := by
  intro k _ _ _ m N hm hmeven hN hNeven hmN D X H hH ν hν
  obtain ⟨a,b,ha,hb,A,hA⟩ := compactUnaryHodgeRealization k m N hm hmeven hN hNeven hmN D X H hH ν hν
  refine ⟨a,b,ha,hb,toOriginal k m N A, ?_⟩
  simpa only [realizes_toOriginal] using hA
''')
tree=ast.parse(read(w/'evidence/period-one-package-404/assemble.py'));fmt={'re':re};exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in ['uncomment','compact']],type_ignores=[]),'format','exec'),fmt)
for name,t in [('Challenge',c),('Solution',s)]:
 (p/(name+'.uncompressed.lean.txt')).write_text(t);v=fmt['compact'](t);(p/(name+'.lean')).write_text(v);print(name,len(v.splitlines()),len(v.encode()))
cfg=json.loads(read(b/'comparator.json'));cfg['theorem_names']=[n for n in cfg['theorem_names'] if not n.startswith(('ArithmeticThetaPalomarComponent485.','ArithmeticThetaComponentDegreeR0184.','ArithmeticThetaPalomarD2_509.'))]+['ArithmeticThetaPalomarUnary514.compactUnaryHodgeRealization'];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n');(p/'input-bindings.json').write_text(json.dumps(inputs,indent=2)+'\n');(p/'compile.py').write_bytes((b/'compile.py').read_bytes())
