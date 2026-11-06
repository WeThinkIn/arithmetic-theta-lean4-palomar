from pathlib import Path
import json,re
p=Path(__file__).resolve().parent;w=p.parent.parent;base=w/'evidence/compact-alpha-package-501';names=json.loads((p/'comparator.json').read_text())['theorem_names'];lis='['+', '.join('``'+n for n in names)+']'
for name in ['ChallengeAudit','SolutionAudit','DefinitionCompatibility','TargetTypeAudit','TargetHoleAudit']:
 s=(base/(name+'.lean')).read_text().replace(str(base),str(p));s=re.sub(r'let targets : List Name := \[.*?\]', 'let targets : List Name := '+lis,s)
 (p/(name+'.lean')).write_text(s)
s='''module
import all Solution
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
example : ArithmeticThetaPalomarHalf505.recover_original_042 = ArithmeticThetaSquareLinesR0192.compact_alpha_canonical_half_line := by rfl
#print axioms ArithmeticThetaPalomarHalf505.recover_original_042
#print axioms ArithmeticThetaPalomarHalf505.binary_eq_original
#print axioms ArithmeticThetaPalomarHalf505.powerComparison_eq_original
#print axioms ArithmeticThetaPalomarHalf505.branch_iff_original
''';(p/'OriginalEndpointAudit.lean').write_text(s)
