from pathlib import Path
import json,re,hashlib
p=Path(__file__).resolve().parent
src=p/'Challenge.attempt02.lean.txt'
if not src.exists():src.write_bytes((p/'Challenge.lean').read_bytes())
text=src.read_text();rows=json.loads((p/'DependencyProbe-check-01.log').read_text());needed=set()
for r in rows:
 if r['needed'] and r['start'] is not None:needed.update(range(r['start'],r['end']+1))
remove=set();removed=[]
# Leave instance synthesis and local semantic helpers intact; drop only unrelated public theorem targets and naturality data.
for r in rows:
 if r['needed'] or r['start'] is None:continue
 span=set(range(r['start'],r['end']+1))
 if span&needed:continue
 if r['name'].startswith(('ArithmeticThetaPhaseFreeKeyR0219.RelativeTestMap','ArithmeticThetaPhaseFreeKeyR0219.testSquare','ArithmeticThetaPhaseFreeKeyR0219.Compatible','ArithmeticThetaPhaseFreeKeyR0219.PreservesFrames','ArithmeticThetaPalomarMultiplier450.phaseFreeMultiplier','ArithmeticThetaPalomarAlphaDescent459.phaseFreeAlphaDescent','ArithmeticThetaPalomarSchemeAlpha437.schemeAlphaCharacter')):
  remove|=span;removed.append(r['name'])
lines=[l for i,l in enumerate(text.splitlines(),1) if i not in remove]
# Pack only declaration type/expression continuations, preserving tactic and structure layout.
out=[];i=0
starts=re.compile(r'^(?:@\[[^\]]+\]\s*)?(?:(?:noncomputable|private|local|protected)\s+)*(?:def|abbrev|theorem|lemma|instance)\b')
while i<len(lines):
 line=lines[i];i+=1
 if starts.match(line):
  while ':=' not in line and not re.search(r'\bwhere\s*$',line) and i<len(lines) and lines[i].startswith('  '):
   line+=' '+lines[i].strip();i+=1
  if ':=' in line:
   rhs=line.split(':=',1)[1]
   if not re.search(r'\b(by|do|where|let|letI|have|haveI|match)\b',rhs):
    body=[]
    while i<len(lines) and lines[i].startswith('  '):body.append(lines[i]);i+=1
    if not any(re.search(r'\b(by|do|where|let|letI|have|haveI|match)\b',l) or l.lstrip().startswith('|') for l in body):
     for l in body:
      if len(line)+1+len(l.strip())>360:out.append(line);line=l
      else:line+=' '+l.strip()
    else:out.append(line);out.extend(body);continue
 out.append(line)
# Only field types (no term layout), on structures retaining their separate field lines.
packed=[];i=0
while i<len(out):
 line=out[i];i+=1
 if re.match(r'^  [A-Za-z_][\w\']*\s*:',line) and not re.search(r'\b(by|do|where|let|letI|have|haveI|match)\b|:=',line):
  while i<len(out) and out[i].startswith('    ') and not re.search(r'\b(by|do|where|let|letI|have|haveI|match)\b|:=',out[i]):
   line+=' '+out[i].strip();i+=1
 packed.append(line)
# All retained lexical tokens unchanged (apart from removed declarations).
original='\n'.join(lines);joined='\n'.join(packed)+'\n'
assert re.sub(r'\s+','',original)==re.sub(r'\s+','',joined)
(p/'Challenge.lean').write_text(joined)
cfg=json.loads((p/'comparator.json').read_text());cfg['theorem_names']=[n for n in cfg['theorem_names'] if n not in removed];(p/'comparator.json').write_text(json.dumps(cfg,indent=2)+'\n')
(p/'compact-receipt.json').write_text(json.dumps({'original_sha256':hashlib.sha256(text.encode()).hexdigest(),'removed_names':removed,'removed_lines':sorted(remove),'retained_tokens_unchanged':True,'lines':len(packed),'bytes':len(joined.encode())},indent=2)+'\n');print(len(packed),len(joined.encode()))
