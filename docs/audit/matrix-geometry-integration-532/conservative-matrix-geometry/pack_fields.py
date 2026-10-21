from pathlib import Path
import re,json
p=Path(__file__).resolve().parent;f=p/'Challenge.lean';s=f.read_text();out=[];i=0;lines=s.splitlines();banned=re.compile(r'\b(by|do|where|let|letI|have|haveI|match)\b')
while i<len(lines):
 line=lines[i];i+=1
 if re.match(r'^  [A-Za-z_][\w\u0080-\uffff]*(?:\s|\s*[:(])',line) and ':' in line and ':=' not in line and not banned.search(line):
  body=[]
  while i<len(lines) and lines[i].startswith('    '):body.append(lines[i]);i+=1
  if not any(banned.search(x) or x.lstrip().startswith('|') for x in body):
   for x in body:
    if len(line)+1+len(x.strip())<=450:line+=' '+x.strip()
    else:out.append(line);line=x
  else:out.append(line);out.extend(body);continue
 out.append(line)
t='\n'.join(out)+'\n';assert re.sub(r'\s+','',s)==re.sub(r'\s+','',t)
(p/'Challenge-before-fields.lean.txt').write_text(s);f.write_text(t);(p/'field-packing.json').write_text(json.dumps({'before':len(lines),'after':len(out),'tokens_preserved':True},indent=2)+'\n');print(len(lines),len(out))
