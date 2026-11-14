# Source-only preparation tool. It never substitutes codec implementations.
import subprocess,re,hashlib,argparse
from pathlib import Path
parser=argparse.ArgumentParser(description='Inventory complete generated codec declarations; does not compile or qualify them')
parser.add_argument('--repo',default='.')
parser.add_argument('--output',required=True)
args=parser.parse_args()
path='src/compiler/20.hir/generated/hir_codec.spl'
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=args.repo,text=True).strip()
source=subprocess.check_output(['git','show',commit+':'+path],cwd=args.repo,text=True)
starts=list(re.finditer(r'^(?:pub )?fn ([A-Za-z_][A-Za-z_0-9]*)\(',source,re.M))
blocks={m.group(1):source[m.start():starts[i+1].start() if i+1<len(starts) else len(source)] for i,m in enumerate(starts)}
graph={name:set(re.findall(r'\b(hc_[A-Za-z_0-9]+)\b',body))&blocks.keys() for name,body in blocks.items()}
roots=['hc_enc_hir_module','hc_dec_hir_module']; reachable=set();queue=roots[:]
while queue:
 n=queue.pop()
 if n in reachable:continue
 reachable.add(n);queue.extend(graph[n]-reachable)
index=0;stack=[];on=set();ids={};low={};groups=[]
def visit(v):
 global index
 ids[v]=low[v]=index;index+=1;stack.append(v);on.add(v)
 for w in graph[v]:
  if w not in ids:visit(w);low[v]=min(low[v],low[w])
  elif w in on:low[v]=min(low[v],ids[w])
 if low[v]==ids[v]:
  group=[]
  while True:
   w=stack.pop();on.remove(w);group.append(w)
   if w==v:break
  groups.append(group)
for n in sorted(reachable):
 if n not in ids:visit(n)
rows=sorted([(sum(len(blocks[n].splitlines()) for n in g),len(g),sorted(g)) for g in groups],reverse=True)
report={'total_functions':len(blocks),'reachable_functions':len(reachable),'reachable_lines':sum(len(blocks[n].splitlines()) for n in reachable),'scc_count':len(rows),'largest_scc':rows[:6],'largest_functions':sorted([(len(v.splitlines()),k) for k,v in blocks.items() if k in reachable],reverse=True)[:8]}
lines=['schema: warm_codec_closure_inventory_v1','status: source_only_uncompiled',
       'commit: "'+commit+'"','path: "'+path+'"',
       'sha256: "'+hashlib.sha256(source.encode()).hexdigest()+'"',
       'total_functions: '+str(len(blocks)),'retained_functions: '+str(len(reachable)),
       'retained_lines: '+str(report['reachable_lines']),
       'analysis: "Whole function bodies; identifier references include function values; non-codec support closure still required"',
       'retained_declarations:']
lines += ['  - '+name for name in sorted(reachable)]
lines += ['strong_components:']
for count,size,names in rows:
 lines += ['  - lines: '+str(count),'    functions: '+str(size),'    declarations: "'+','.join(names)+'"']
Path(args.output).write_text('\n'.join(lines)+'\n')
print('complete codec closure:',report['reachable_functions'],'functions',report['reachable_lines'],'lines; SCCs:',len(rows))
print('largest SCC sizes:',[(r[0],r[1]) for r in rows[:6]])
