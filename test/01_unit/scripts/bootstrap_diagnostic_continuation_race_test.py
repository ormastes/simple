#!/usr/bin/env python3
"""Actual collector race regressions; no synthetic provider admits artifacts."""
import json,os,pathlib,runpy,sys,tempfile
collector=pathlib.Path(sys.argv[1]).resolve()
for mode in ['disappeared','swapped_symlink']:
 with tempfile.TemporaryDirectory() as tmp:
  root=pathlib.Path(tmp)/'root';source=root/'build/bootstrap/lineage.env';source.parent.mkdir(parents=True);source.write_bytes(b'identity');outside=pathlib.Path(tmp)/'outside';outside.write_bytes(b'SECRET');out=pathlib.Path(tmp)/'out'
  original=pathlib.Path.lstat;counter=[0]
  def metadata(self,*args,**kwargs):
   if self==source:
    counter[0]+=1
    if counter[0]==1:
     self.unlink()
     if mode=='swapped_symlink':self.symlink_to(outside)
   return original(self,*args,**kwargs)
  pathlib.Path.lstat=metadata;sys.argv=[str(collector),str(root),str(out),'1000']
  try:runpy.run_path(str(collector),run_name='__main__')
  finally:pathlib.Path.lstat=original
  receipt=json.loads((out/'receipt.json').read_text());assert receipt['rejected'];assert not receipt['files'];assert receipt['preserved_bytes']==0;assert not receipt['runtime_archives_present'];assert not list((out/'files').rglob('*.env')) if (out/'files').exists() else True
print('PASS: disappeared and swapped-symlink source produce truthful rejected receipts without exporting bytes')
