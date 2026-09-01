#!/usr/bin/env python3
# Probe sweep: .sweep.py <start> <end> — probe .todo.txt[start:end], append >80 to .done.txt,
# write <=80 to .todo2.txt (dedup at end)
import subprocess, sys, os
os.chdir('/tmp/mod6')
todo=[l.strip() for l in open('.todo.txt') if l.strip()]
a,b=int(sys.argv[1]),int(sys.argv[2])
fast=[]
for path in todo[a:b]:
    if not os.path.exists(path):
        with open('.skip.txt','a') as f: f.write('%s\tMISSING\n'%path)
        continue
    r = subprocess.run(['/mnt/data/worktrees/simple-main/bin/simple','/mnt/data/worktrees/simple-main/probe_sspec_scores.spl','/tmp/mod6/'+path],capture_output=True,text=True)
    lines=r.stdout.strip().splitlines()
    s=-1
    if lines:
        cols=lines[-1].split('\t')
        if len(cols)>=2:
            try: s=int(cols[1])
            except ValueError: pass
    if s>80:
        fast.append(path)
        with open('.done.txt','a') as f: f.write(path+'\n')
        print('%s FAST %d'%(path,s)); sys.stdout.flush()
print('SWEEP done, fast=%d of %d'%(len(fast),b-a))
