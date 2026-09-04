import re,os,json,subprocess
R='/mnt/data/audit-registry-gap'
src=open(R+'/src/compiler_rust/common/src/runtime_symbols.rs').read()
def arr(name):
    i=src.index('pub const %s: &[&str] = &['%name); j=src.index('\n];',i)
    return set(re.findall(r'"([A-Za-z0-9_]+)"',src[i:j]))
core=arr('CORE_REQUIRED_RUNTIME_SYMBOLS'); allsym=arr('RUNTIME_SYMBOL_NAMES')
reg=core|allsym
# handled set from interpreter_extern/**
ie=R+'/src/compiler_rust/compiler/src/interpreter_extern'
handled=set(); prefixes=set()
mod=open(ie+'/mod.rs').read()
tbl=mod[mod.index('fn init_dispatch_table'):]
# cut at end of function: find the test module marker
end=tbl.find('\n#[cfg(test)]')
tblbody=tbl[:end if end>0 else len(tbl)]
handled|=set(re.findall(r'insert_simple!\(\s*"([A-Za-z0-9_]+)"',tblbody))
handled|=set(re.findall(r'm\.insert\(\s*\n?\s*"([A-Za-z0-9_]+)"',tblbody))
# prefix arms in dispatch fn (whole mod, minus tests)
modnotest=mod[:mod.index('\n#[cfg(test)]')] if '\n#[cfg(test)]' in mod else mod
prefixes|=set(re.findall(r'name\.starts_with\("([A-Za-z0-9_]+)"\)',modnotest))
# per-module match arms across all files (exclude #[cfg(test)] blocks crudely by file split)
for root,d,fs in os.walk(ie):
    for f in fs:
        if not f.endswith('.rs'): continue
        p=os.path.join(root,f); t=open(p).read()
        if '\n#[cfg(test)]' in t: t=t[:t.index('\n#[cfg(test)]')]
        handled|=set(re.findall(r'"(rt_[A-Za-z0-9_]+)"\s*=>',t))
        handled|=set(re.findall(r'name\s*==\s*"(rt_[A-Za-z0-9_]+)"',t))
        prefixes|=set(re.findall(r'starts_with\("(rt_[A-Za-z0-9_]+)"\)',t))
def is_handled(n):
    if n in handled: return True
    return any(n.startswith(p) for p in prefixes)
unh=sorted(n for n in reg if not is_handled(n))
# reachable from src/lib
libext=set()
out=subprocess.run(['grep','-rhoE',r'extern[^\n]*\bfn\s+[A-Za-z0-9_]+','--include=*.spl',R+'/src/lib'],capture_output=True,text=True).stdout
libext=set(re.findall(r'fn\s+([A-Za-z0-9_]+)',out))
live=[n for n in unh if n in libext]
json.dump({'registered':len(reg),'core':len(core),'all':len(allsym),'handled_literal':len(handled),'prefixes':sorted(prefixes),'unhandled':unh,'live':live},open(R+'/.audit/gap.json','w'),indent=1)
print('registered',len(reg),'handled_literal',len(handled),'prefix_families',len(prefixes))
print('unhandled',len(unh),'live(reachable from src/lib)',len(live))
print('live sample:',live[:40])
