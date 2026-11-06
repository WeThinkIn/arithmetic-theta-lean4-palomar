from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent;f=p/'Challenge.lean';text=f.read_text();(p/'Challenge-before-packing.lean.txt').write_text(text);lines=text.splitlines();out=[];i=0
starts=re.compile(r'^(?:@\[[^\]]+\]\s*)?(?:(?:noncomputable|private|local|protected)\s+)*(?:def|abbrev|theorem|lemma|instance)\b')
while i<len(lines):
 line=lines[i];i+=1
 if starts.match(line):
  while ':=' not in line and not re.search(r'\bwhere\s*$',line) and i<len(lines) and lines[i].startswith('  '):line+=' '+lines[i].strip();i+=1
  if ':=' in line:
   rhs=line.split(':=',1)[1]
   if not re.search(r'\b(by|do|where|let|letI|have|haveI|match)\b',rhs):
    body=[]
    while i<len(lines) and lines[i].startswith('  '):body.append(lines[i]);i+=1
    if not any(re.search(r'\b(by|do|where|let|letI|have|haveI|match)\b',l) or l.lstrip().startswith('|') for l in body):
     for l in body:
      if len(line)+1+len(l.strip())>400:out.append(line);line=l
      else:line+=' '+l.strip()
    else:out.append(line);out.extend(body);continue
 out.append(line)
packed=[];i=0
while i<len(out):
 line=out[i];i+=1
 if re.match(r'^theorem \w+\s*:\s*$',line) and i<len(out) and out[i].startswith('∀ '):line+=' '+out[i];i+=1
 if line.endswith(':= by') and i<len(out) and out[i].strip() in ['sorry','rfl','infer_instance']:line+=' '+out[i].strip();i+=1
 packed.append(line)
joined='\n'.join(packed)+'\n';assert re.sub(r'\s+','',text)==re.sub(r'\s+','',joined);f.write_text(joined)
(p/'packing.json').write_text(json.dumps(dict(original_lines=len(lines),packed_lines=len(packed),bytes=len(joined.encode()),tokens_preserved=True),indent=2)+'\n');print((p/'packing.json').read_text())
