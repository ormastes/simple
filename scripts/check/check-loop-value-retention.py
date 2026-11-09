#!/usr/bin/env python3
"""Compare actual interpreter loop arms with former assignment retention.
Only timeout, nested evaluation and context-restoration effects are adapted.
Arc/Weak probes observe retention and destructor traces, including unwinding.
"""
import argparse
from pathlib import Path
import re
import subprocess
ap=argparse.ArgumentParser()
ap.add_argument('--output',required=True)
ap.add_argument('--rustc',default='rustc')
ap.add_argument('--negative-only',action='store_true')
a=ap.parse_args();root=Path(__file__).resolve().parents[2]
out=Path(a.output).resolve();out.mkdir(parents=True,exist_ok=True)
source=(root/'src/compiler_rust/compiler/src/interpreter_call/block_execution.rs').read_text()
loops=[]
for match in re.finditer(r'Node::Loop\(loop_stmt\) => loop \{',source):
    start=source.index('loop {',match.start());end=source.index('{',start)+1;depth=1
    while depth:
        depth+=(source[end]=='{')-(source[end]=='}');end+=1
    text=source[start:end]
    text=text.replace('crate::interpreter::is_timeout_exceeded()','fixture_timeout()')
    text=text.replace('crate::interpreter::timeout_limit_secs()','7')
    text,n=re.subn(r'exec_block_closure_mut\([\s\S]*?\n\s*\)','fixture_body()',text)
    assert n==1
    text,n=re.subn(r'CONST_NAMES.with\([^\n]+;', 'fixture_restore("const");',text)
    text,n=re.subn(r'IMMUTABLE_VARS.with\([^\n]+;', 'fixture_restore("immutable");',text)
    assert 'Ok(val) => drop(std::mem::replace(&mut last_value, val)),' in text
    loops.append(text)
assert len(loops)==2
pre=r"""
use std::{cell::RefCell, collections::{BTreeMap, VecDeque}, panic::{catch_unwind, AssertUnwindSafe}, sync::{Arc, Weak}};
thread_local! {
    static LOG: RefCell<Vec<String>> = const {RefCell::new(Vec::new())};
    static PANIC_DROP: RefCell<Option<u32>> = const {RefCell::new(None)};
    static WITNESSES: RefCell<BTreeMap<u32,Weak<Trace>>> = const {RefCell::new(BTreeMap::new())};
    static INPUT: RefCell<(VecDeque<Step>,usize,Option<usize>)> = const {RefCell::new((VecDeque::new(),0,None))};
}
fn event(s:String) {LOG.with(|x|x.borrow_mut().push(s));}
#[derive(Debug)] struct Trace(u32);
impl Drop for Trace {
    fn drop(&mut self) {
        event(format!("drop:{}",self.0));
        if PANIC_DROP.with(|x|{let mut x=x.borrow_mut();if *x==Some(self.0){*x=None;true}else{false}}) {panic!("drop probe")}
    }
}
#[derive(Debug)] enum Value {Nil, Token(Arc<Trace>)}
impl Value {
    fn new(id:u32)->Self {
        let v=Arc::new(Trace(id));WITNESSES.with(|x|{x.borrow_mut().insert(id,Arc::downgrade(&v));});Self::Token(v)
    }
    fn id(&self)->u32 {match self {Self::Nil=>999,Self::Token(v)=>v.0}}
}
#[derive(Clone)] enum Step {Ok(u32), Continue, Break(Option<u32>), Error}
#[derive(Debug)] enum CompileError {LoopBreak(Option<Value>), LoopContinue, TimeoutExceeded {timeout_secs:u64}, Failure}
fn fixture_timeout()->bool {
    INPUT.with(|x|{let x=x.borrow();event(format!("timeout:{}",x.1));x.2==Some(x.1)})
}
fn fixture_restore(which:&str) {event(format!("restore:{which}"));}
fn fixture_body()->Result<Value,CompileError> {
    let alive=WITNESSES.with(|x|x.borrow().iter().filter(|(_,v)|v.strong_count()>0).map(|(id,_)|*id).collect::<Vec<_>>());
    INPUT.with(|x|{
        let mut x=x.borrow_mut();event(format!("body:{}:alive={alive:?}",x.1));x.1+=1;
        match x.0.pop_front().expect("finite scenario") {
            Step::Ok(id)=>Ok(Value::new(id)),Step::Continue=>Err(CompileError::LoopContinue),
            Step::Break(id)=>Err(CompileError::LoopBreak(id.map(Value::new))),Step::Error=>Err(CompileError::Failure)
        }
    })
}
"""
functions=''
for i,text in enumerate(loops):
    for kind in ['current','former']:
        body=text if kind=='current' else text.replace('drop(std::mem::replace(&mut last_value, val))','last_value = val')
        attribute='#[allow(unused_assignments)]\n' if kind=='former' else ''
        functions+=attribute+f'fn loop_{i}_{kind}()->Result<u32,CompileError>{{\nlet mut last_value=Value::new(0);\n'+body+'\nOk(last_value.id())\n}\n'
post=r"""
fn run(f:fn()->Result<u32,CompileError>,steps:&[Step],timeout:Option<usize>,panic_on:Option<u32>)->(String,Vec<String>) {
    LOG.with(|x|x.borrow_mut().clear());WITNESSES.with(|x|x.borrow_mut().clear());PANIC_DROP.with(|x|*x.borrow_mut()=panic_on);
    INPUT.with(|x|*x.borrow_mut()=(steps.iter().cloned().collect(),0,timeout));
    let result=catch_unwind(AssertUnwindSafe(f));
    let status=match result {
        Ok(Err(CompileError::TimeoutExceeded{timeout_secs}))=>format!("timeout:{timeout_secs}"),
        Ok(result)=>format!("{result:?}"),Err(_)=>"panic".to_owned()
    };
    (status,LOG.with(|x|x.borrow().clone()))
}
#[test]fn all_exit_and_panicking_destructor_traces_match() {
    let cases=[
        (vec![Step::Ok(1),Step::Continue,Step::Ok(2),Step::Break(Some(3))],None),
        (vec![Step::Ok(1),Step::Continue,Step::Error],None),
        (vec![Step::Ok(1),Step::Continue],Some(2)),(vec![],Some(0)),
        (vec![Step::Break(None)],None),
        (vec![Step::Continue,Step::Ok(1),Step::Ok(2),Step::Break(None)],None),
        (vec![Step::Error],None),(vec![Step::Break(Some(3))],None)
    ];
    for (current,former) in [(loop_0_current as fn()->_,loop_0_former as fn()->_), (loop_1_current as fn()->_,loop_1_former as fn()->_)] {
        for (steps,timeout) in &cases {for panic_on in [None,Some(0),Some(1),Some(2),Some(3)] {
            assert_eq!(run(current,steps,*timeout,panic_on),run(former,steps,*timeout,panic_on));
        }}
    }
}
#[test]fn returned_values_remain_owned_across_continue() {
    for current in [loop_0_current,loop_1_current] {
        let (status,log)=run(current,&[Step::Ok(1),Step::Continue,Step::Ok(2),Step::Break(Some(3))],None,None);
        assert_eq!(status,"Ok(3)");
        assert!(log.iter().any(|x|x=="body:1:alive=[1]"));
        assert!(log.iter().any(|x|x=="body:2:alive=[1]"));
        assert!(log.iter().any(|x|x=="body:3:alive=[2]"));
        assert_eq!(log.last().unwrap(),"drop:3");
    }
}
"""
f=out/'loop-production.rs';f.write_text(pre+functions+post)
exe=out/'loop-production.exe'
if not a.negative_only:
    subprocess.run([a.rustc,'--edition=2021','--test','-Dwarnings',str(f),'-o',str(exe)],check=True)
    subprocess.run([str(exe)],check=True)
negative=out/'loop-unused-negative.rs'
negative.write_text((pre+functions+post).replace('#[allow(unused_assignments)]\n',''))
r=subprocess.run([a.rustc,'--edition=2021','--test','-Dunused_assignments',str(negative),'-o',str(out/'negative.exe')],capture_output=True,text=True)
(out/'loop-unused-negative.log').write_text(r.stdout+r.stderr)
assert r.returncode!=0 and r.stderr.count('Ok(val) => last_value = val,')==2,r.stderr
print('both former loop assignment warnings negative control: PASS')
