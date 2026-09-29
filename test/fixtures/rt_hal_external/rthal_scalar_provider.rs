//! Test-only Rust comparator for the frozen `rthal-scalar-v2` protocol.
//! Pure Simple owns execution and effects, but this child independently derives
//! its result so a wrong Pure oracle is falsifiable. For lane `i` in `0..4`:
//!
//! `base = op[i] ^ rotl(input[(i+1)%4], 7+11*i) ^ (GOLDEN+FNV_PRIME*i)`
//!
//! Replay additionally XORs `rotl(pure_trace[(i+2)%4], 13+7*i)` and
//! `EFFECT_DOMAIN`. Outcome is the SplitMix64 finalizer of base. Error is zero.
//! Query trace is `mix64(base ^ TRACE_DOMAIN)`; replay trace is the supplied
//! Pure trace. Query receives no expected receipt argv; replay receives only
//! trace as effect-replay input. Arithmetic
//! wraps at 64 bits and work/storage remain fixed O(1).

use std::env;
use std::io::{self, Read, Write};
use std::process::ExitCode;
use std::sync::atomic::{AtomicI64, Ordering};

const QUERY_ARGC: usize = 13;
const REPLAY_ARGC: usize = 17;
const IO_CAP: usize = 1_048_576;
const IO_HEADER: usize = 32;
const IO_TYPE_FIXED: usize = 56;
const GOLDEN: u64 = 0x9e37_79b9_7f4a_7c15;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
const EFFECT_DOMAIN: u64 = 0xd1b5_4a32_d192_ed03;
const TRACE_DOMAIN: u64 = 0x94d0_49bb_1331_11eb;

// The provider is single-process/single-request. Keep all HIO2 material in
// fixed process-lifetime storage like the C sibling: typed exit handling must
// not put four 1 MiB arrays on a worker stack or retain prior exit frames.
static mut IO_REQ: [u8; IO_CAP] = [0; IO_CAP];
static mut IO_EFF: [u8; IO_CAP] = [0; IO_CAP];
static mut IO_OUT: [u8; IO_CAP] = [0; IO_CAP];
static RECORDED_CASE: AtomicI64 = AtomicI64::new(-1);
static RECORDED_SCHEMA: AtomicI64 = AtomicI64::new(-1);

fn valid_i64(value: &str) -> bool {
    let digits = value.strip_prefix('-').unwrap_or(value);
    !digits.is_empty()
        && digits.bytes().all(|byte| byte.is_ascii_digit())
        && value.parse::<i64>().is_ok()
}

fn parse_word(value: &str) -> u64 {
    value.parse::<i64>().expect("validated signed word") as u64
}

fn mix64(mut value: u64) -> u64 {
    value ^= value >> 30;
    value = value.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value ^= value >> 27;
    value = value.wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn u32le(b: &[u8], p: usize) -> Option<u32> {
    Some(u32::from_le_bytes(b.get(p..p.checked_add(4)?)?.try_into().ok()?))
}
fn u64le(b: &[u8], p: usize) -> Option<u64> {
    Some(u64::from_le_bytes(b.get(p..p.checked_add(8)?)?.try_into().ok()?))
}
fn push(out: &mut [u8; IO_CAP], n: &mut usize, src: &[u8]) -> bool {
    let Some(end) = n.checked_add(src.len()) else { return false };
    if end > IO_CAP { return false }
    out[*n..end].copy_from_slice(src); *n = end; true
}
fn push64(out: &mut [u8; IO_CAP], n: &mut usize, v: u64) -> bool {
    push(out, n, &v.to_le_bytes())
}
fn hex(byte: u8) -> Option<u8> { match byte { b'0'..=b'9'=>Some(byte-b'0'), b'a'..=b'f'=>Some(byte-b'a'+10), _=>None } }
fn read_hex<R: Read>(r: &mut R, out: &mut [u8], n: usize) -> bool {
    if n > out.len() { return false }
    let mut pair=[0u8;2];
    for slot in &mut out[..n] {
        if r.read_exact(&mut pair).is_err() { return false }
        let Some(a)=hex(pair[0]) else{return false}; let Some(b)=hex(pair[1]) else{return false}; *slot=a*16+b;
    }
    true
}
fn outer<R: Read>(r: &mut R) -> Option<(usize,usize)> {
    let mut line=[0u8;96]; let mut n=0usize;
    loop { if n==line.len(){return None} r.read_exact(&mut line[n..n+1]).ok()?; if line[n]==b'\n'{break} n+=1; }
    let mut f=std::str::from_utf8(&line[..n]).ok()?.split(' ');
    if f.next()? != "RTHAL2" { return None }
    let a=f.next()?.parse().ok()?; let b=f.next()?.parse().ok()?; if f.next().is_some(){return None} Some((a,b))
}
fn transcript(b:&[u8], p:usize, count:usize, domain:u64)->bool {
    let Some(bytes)=count.checked_mul(16) else{return false}; let Some(end)=p.checked_add(bytes) else{return false};
    count>=2 && count<=IO_CAP/16 && end<=b.len() && u64le(b,p)==Some(1) && u64le(b,p+8).map(|x|x>>32)==Some(domain) && u64le(b,end-16)==Some(2)
}
fn unit_descriptor(bytes:&[u8])->bool { bytes==b"v2;unit" }
fn unit(out:&mut [u8;IO_CAP],n:&mut usize,domain:u64)->bool {
    [6,3,0,1,domain<<32,11,0,2,0].into_iter().all(|v|push64(out,n,v))
}
fn descriptor_is(bytes:&[u8], expected:&[u8])->bool { bytes==expected }
fn text_events(bytes:&[u8], payload:usize, domain:u64)->bool {
    bytes.len()==64 && u64le(bytes,0)==Some(1) && u64le(bytes,8).map(|v|v>>32)==Some(domain) &&
    u64le(bytes,16)==Some(25) && u64le(bytes,24)==Some(payload as u64) &&
    u64le(bytes,32)==Some(26) && u64le(bytes,40)==Some(0) && u64le(bytes,48)==Some(2) && u64le(bytes,56)==Some(0)
}
fn bytes_events(bytes:&[u8], payload:usize, domain:u64)->bool {
    bytes.len()==64 && u64le(bytes,0)==Some(1) && u64le(bytes,8).map(|v|v>>32)==Some(domain) &&
    u64le(bytes,16)==Some(23) && u64le(bytes,24)==Some(payload as u64) &&
    u64le(bytes,32)==Some(24) && u64le(bytes,40)==Some(0) && u64le(bytes,48)==Some(2) && u64le(bytes,56)==Some(0)
}
fn canonical_utf8_identity(bytes:&[u8])->bool {
    !bytes.is_empty() && !bytes.contains(&0) && std::str::from_utf8(bytes).is_ok()
}
/* HIO2 V2 itself is the typed request. The provider receives operation,
 * descriptor, canonical parameter transcript and payload only—never a Pure
 * exit seed. A cold startup binding admits exactly one operation identity and
 * one bounded semantic adapter. */
struct ProviderRegistry<'a>{ operation:&'a [u8], adapter:u8 }
fn execute_idempotent_record(req:&[u8])->bool{
    let Some(case_id)=u64le(req,8).map(|v|v as i64) else{return false};let Some(schema)=u64le(req,24).map(|v|v as i64) else{return false};
    if case_id<0||schema<=0{return false}
    let observed_case=RECORDED_CASE.load(Ordering::Acquire);let observed_schema=RECORDED_SCHEMA.load(Ordering::Acquire);
    if(observed_case>=0&&observed_case!=case_id)||(observed_schema>=0&&observed_schema!=schema){return false}
    RECORDED_CASE.store(case_id,Ordering::Release);RECORDED_SCHEMA.store(schema,Ordering::Release);true
}
#[derive(Clone,Copy)] struct EnvSpan{start:usize,len:usize}
#[derive(Clone,Copy)] struct EnvTool{id:EnvSpan}
#[derive(Clone,Copy)] struct EnvProbe{id:EnvSpan,args:i64,timeout:i64,out:i64,err:i64}
fn env_eq(b:&[u8],a:EnvSpan,c:EnvSpan)->bool{a.len==c.len&&b[a.start..a.start+a.len]==b[c.start..c.start+c.len]}
fn env_control(v:&[u8])->bool{v.iter().any(|x|*x<32||*x==127)}
fn env_blank(v:&[u8])->bool{v.iter().all(|x|*x==b' ')}
fn env_contains(v:&[u8],s:&[u8])->bool{v.windows(s.len()).any(|w|w==s)}
fn env_identifier(v:&[u8])->bool{!v.is_empty()&&v.len()<=128&&!v.iter().any(|x|matches!(*x,b'/'|b'\\'|b':'|b' '))}
fn env_abs_path(v:&[u8])->bool{!v.is_empty()&&v.len()<=4096&&!v.contains(&b'\\')&&!env_contains(v,b"/../")&&!env_contains(v,b"//")&&!v.ends_with(b"/..")&&(v[0]==b'/'||(v.len()>=3&&v[1]==b':'&&v[2]==b'/'))}
fn env_sha(v:&[u8])->bool{v.len()==71&&&v[..7]==b"sha256:"&&v[7..].iter().all(|x|x.is_ascii_digit()||matches!(*x,b'a'..=b'f'))}
fn env_u32(b:&[u8],at:&mut usize)->Option<u32>{let v=u32le(b,*at)?;*at=at.checked_add(4)?;Some(v)}
fn env_i64(b:&[u8],at:&mut usize)->Option<i64>{let v=u64le(b,*at)? as i64;*at=at.checked_add(8)?;Some(v)}
fn env_text(b:&[u8],at:&mut usize,cap:usize)->Option<EnvSpan>{let n=env_u32(b,at)? as usize;if n>cap||*at>b.len()||n>b.len()-*at{return None}let out=EnvSpan{start:*at,len:n};*at+=n;if out.len>0&&(!canonical_utf8_identity(&b[out.start..out.start+out.len])||env_control(&b[out.start..out.start+out.len])){return None}Some(out)}
fn env_plan_body(b:&[u8])->bool{
    let mut at=0usize;let Some(version)=env_u32(b,&mut at)else{return false};if version!=1{return false};let Some(plan)=env_text(b,&mut at,128)else{return false};let Some(root)=env_text(b,&mut at,4096)else{return false};if plan.len==0||env_blank(&b[plan.start..plan.start+plan.len])||!env_abs_path(&b[root.start..root.start+root.len])||root.len==1||b[root.start+root.len-1]==b'/'{return false};let Some(total)=env_i64(b,&mut at)else{return false};let Some(processes)=env_i64(b,&mut at)else{return false};if total<=0||total>67108864||processes<0||processes>64{return false}
    let Some(tool_count)=env_u32(b,&mut at)else{return false};if tool_count>64{return false}let mut tools=[EnvTool{id:EnvSpan{start:0,len:0}};64];for i in 0..tool_count as usize{let(Some(id),Some(path),Some(hash))=(env_text(b,&mut at,128),env_text(b,&mut at,4096),env_text(b,&mut at,128))else{return false};if !env_identifier(&b[id.start..id.start+id.len])||!env_abs_path(&b[path.start..path.start+path.len])||!env_sha(&b[hash.start..hash.start+hash.len]){return false}for prior in 0..i{if env_eq(b,id,tools[prior].id){return false}}tools[i]=EnvTool{id};}
    let Some(probe_count)=env_u32(b,&mut at)else{return false};if probe_count>64{return false}let mut probes=[EnvProbe{id:EnvSpan{start:0,len:0},args:0,timeout:0,out:0,err:0};64];for i in 0..probe_count as usize{let(Some(id),Some(schema),Some(args),Some(timeout),Some(out),Some(err))=(env_text(b,&mut at,128),env_text(b,&mut at,128),env_i64(b,&mut at),env_i64(b,&mut at),env_i64(b,&mut at),env_i64(b,&mut at))else{return false};if !env_identifier(&b[id.start..id.start+id.len])||!env_identifier(&b[schema.start..schema.start+schema.len])||args<0||args>64||timeout<=0||timeout>600000||out<0||out>16777216||err<0||err>16777216{return false}for prior in 0..i{if env_eq(b,id,probes[prior].id){return false}}probes[i]=EnvProbe{id,args,timeout,out,err};}
    let Some(instruction_count)=env_u32(b,&mut at)else{return false};if instruction_count>1024{return false}let(mut used,mut spawned)=(0i64,0i64);for _ in 0..instruction_count{let(Some(kind),Some(resource),Some(argc))=(env_u32(b,&mut at),env_text(b,&mut at,4096),env_u32(b,&mut at))else{return false};if kind<1||kind>24||argc>64{return false}let mut arg_bytes=0usize;for _ in 0..argc{let Some(arg)=env_text(b,&mut at,1024)else{return false};if arg_bytes>4096-arg.len{return false}arg_bytes+=arg.len;}let(Some(timeout),Some(out),Some(err))=(env_i64(b,&mut at),env_i64(b,&mut at),env_i64(b,&mut at))else{return false};if timeout<=0||timeout>600000||out<0||out>16777216||err<0||err>16777216||out>total-used{return false}used+=out;if err>total-used{return false}used+=err;let rv=&b[resource.start..resource.start+resource.len];if(resource.len==0&&kind!=2)||((kind!=2)&&env_blank(rv))||(kind==2&&(resource.len!=0||argc!=0)){return false}if kind==3&&(argc!=0||resource.len==0||rv[0]==b'/'||rv.contains(&b'\\')||rv.contains(&b':')||rv==b".."||rv.starts_with(b"../")||env_contains(rv,b"/../")||rv.ends_with(b"/..")){return false}if(kind==1||(5..=23).contains(&kind))&&!env_identifier(rv){return false}if kind==4{if !(0..tool_count as usize).any(|i|env_eq(b,resource,tools[i].id)){return false}spawned+=1}if(5..=23).contains(&kind){let mut admitted=false;for i in 0..probe_count as usize{if env_eq(b,resource,probes[i].id){if argc as i64>probes[i].args||timeout>probes[i].timeout||out>probes[i].out||err>probes[i].err{return false}admitted=true;}}if !admitted{return false}}}
    spawned<=processes&&at==b.len()
}
fn tuple_bytes(events:&[u8], payload:usize)->bool { events.len()==96&&u64le(events,0)==Some(1)&&u64le(events,8).map(|v|v>>32)==Some(2)&&u64le(events,16)==Some(3)&&u64le(events,24)==Some(1)&&u64le(events,32)==Some(23)&&u64le(events,40)==Some(payload as u64)&&u64le(events,48)==Some(24)&&u64le(events,56)==Some(0)&&u64le(events,64)==Some(4)&&u64le(events,72)==Some(0)&&u64le(events,80)==Some(2)&&u64le(events,88)==Some(0) }
fn tuple_text(events:&[u8], payload:usize)->bool { events.len()==96&&u64le(events,0)==Some(1)&&u64le(events,8).map(|v|v>>32)==Some(2)&&u64le(events,16)==Some(3)&&u64le(events,24)==Some(1)&&u64le(events,32)==Some(25)&&u64le(events,40)==Some(payload as u64)&&u64le(events,48)==Some(26)&&u64le(events,56)==Some(0)&&u64le(events,64)==Some(4)&&u64le(events,72)==Some(0)&&u64le(events,80)==Some(2)&&u64le(events,88)==Some(0) }
fn emit_result(req:&[u8],bs:&[usize;5],dl:&[usize;5],payload:&[u8],tag:u64,width:u64,out:&mut [u8;IO_CAP])->Result<(),u8>{
    let mut n=0usize;if !push(out,&mut n,b"RTHIOV2\0")||!push64(out,&mut n,2)||!push64(out,&mut n,u64le(req,8).ok_or(73)?)||!push64(out,&mut n,u64le(req,16).ok_or(73)?)||!push64(out,&mut n,0)||!push64(out,&mut n,u64le(req,24).ok_or(73)?)||!push64(out,&mut n,0)||!push64(out,&mut n,1)||!push64(out,&mut n,0){return Err(76)}
    for start in bs{for q in 0..6{if !push64(out,&mut n,u64le(req,*start+q*8).ok_or(73)?){return Err(76)}}if !push64(out,&mut n,1){return Err(76)}}
    for b in 0..5{if !push(out,&mut n,&req[bs[b]+IO_TYPE_FIXED..bs[b]+IO_TYPE_FIXED+dl[b]]){return Err(76)}}
    let count=if tag==20{3}else{4};if !push64(out,&mut n,6)||!push64(out,&mut n,count)||!push64(out,&mut n,payload.len() as u64)||!push64(out,&mut n,1)||!push64(out,&mut n,3u64<<32)||!push64(out,&mut n,tag)||!push64(out,&mut n,width){return Err(76)}
    if tag!=20&&(!push64(out,&mut n,tag+1)||!push64(out,&mut n,0)){return Err(76)}
    if !push64(out,&mut n,2)||!push64(out,&mut n,0)||!push(out,&mut n,payload)||!unit(out,&mut n,4)||!unit(out,&mut n,5){return Err(76)}
    let stdout=io::stdout();let mut w=stdout.lock();write!(w,"RTHAL2 {}\n",n).map_err(|_|77)?;emit_hex(&mut w,&out[..n]).map_err(|_|77)?;Ok(())
}
fn emit_effect_result(req:&[u8],bs:&[usize;5],dl:&[usize;5],payload:&[u8],out:&mut [u8;IO_CAP])->Result<(),u8>{
    let mut n=0usize;if !push(out,&mut n,b"RTHIOV2\0")||!push64(out,&mut n,2)||!push64(out,&mut n,u64le(req,8).ok_or(73)?)||!push64(out,&mut n,u64le(req,16).ok_or(73)?)||!push64(out,&mut n,0)||!push64(out,&mut n,u64le(req,24).ok_or(73)?)||!push64(out,&mut n,0)||!push64(out,&mut n,1)||!push64(out,&mut n,0){return Err(76)}
    for start in bs{for q in 0..6{if !push64(out,&mut n,u64le(req,*start+q*8).ok_or(73)?){return Err(76)}}if !push64(out,&mut n,1){return Err(76)}}
    for b in 0..5{if !push(out,&mut n,&req[bs[b]+IO_TYPE_FIXED..bs[b]+IO_TYPE_FIXED+dl[b]]){return Err(76)}}
    if !unit(out,&mut n,3)||!unit(out,&mut n,4)||!push64(out,&mut n,6)||!push64(out,&mut n,4)||!push64(out,&mut n,payload.len() as u64)||!push64(out,&mut n,1)||!push64(out,&mut n,5u64<<32)||!push64(out,&mut n,23)||!push64(out,&mut n,payload.len() as u64)||!push64(out,&mut n,24)||!push64(out,&mut n,0)||!push64(out,&mut n,2)||!push64(out,&mut n,0)||!push(out,&mut n,payload){return Err(76)}
    let stdout=io::stdout();let mut w=stdout.lock();write!(w,"RTHAL2 {}\n",n).map_err(|_|77)?;emit_hex(&mut w,&out[..n]).map_err(|_|77)?;Ok(())
}
fn run_registered_operation(req:&[u8],bs:&[usize;5],dl:&[usize;5],input:usize,inn:usize,op:usize,op_ev:usize,ope:usize,opn:usize,in_ev:usize,ine:usize,registry:&ProviderRegistry,scratch:&mut [u8;IO_CAP],out:&mut [u8;IO_CAP])->Result<(),u8>{
    let operation=&req[op..op+opn];let params=&req[input..input+inn];let events=&req[in_ev..in_ev+ine];let input_desc=&req[bs[1]+IO_TYPE_FIXED..bs[1]+IO_TYPE_FIXED+dl[1]];let meta=bs[4]+IO_TYPE_FIXED+dl[4];
    if !descriptor_is(&req[bs[0]+IO_TYPE_FIXED..bs[0]+IO_TYPE_FIXED+dl[0]],b"v2;text:utf8")||!text_events(&req[op_ev..op_ev+ope],opn,1)||!canonical_utf8_identity(operation)||!transcript(req,in_ev,ine/16,2)||u32le(req,meta)!=Some(0)||u32le(req,meta+4)!=Some(6)||u32le(req,meta+8)!=Some(0)||u32le(req,meta+20)!=Some(6)||u32le(req,meta+24)!=Some(1)||u32le(req,meta+36)!=Some(6)||u32le(req,meta+40)!=Some(6)||u32le(req,meta+44)!=Some(6){return Err(74)}
    if operation!=registry.operation{return Err(78)}
    let unit_ok=unit_descriptor(&req[bs[3]+IO_TYPE_FIXED..bs[3]+IO_TYPE_FIXED+dl[3]])&&unit_descriptor(&req[bs[4]+IO_TYPE_FIXED..bs[4]+IO_TYPE_FIXED+dl[4]]);
    match registry.adapter {
        1 if input_desc==b"v2;tuple;1;8:v2;bytes"&&descriptor_is(&req[bs[2]+IO_TYPE_FIXED..bs[2]+IO_TYPE_FIXED+dl[2]],b"v2;bytes")&&tuple_bytes(events,inn)&&unit_ok => emit_result(req,bs,dl,params,23,inn as u64,out),
        2 if input_desc==b"v2;tuple;1;8:v2;bytes"&&descriptor_is(&req[bs[2]+IO_TYPE_FIXED..bs[2]+IO_TYPE_FIXED+dl[2]],b"v2;u64")&&tuple_bytes(events,inn)&&unit_ok => {let mut x=0u64;for(i,b)in params.iter().enumerate(){x^=(*b as u64)<<(8*(i&7));}let value=x.to_le_bytes();emit_result(req,bs,dl,&value,20,8,out)},
        3 if input_desc==b"v2;tuple;1;12:v2;text:utf8"&&descriptor_is(&req[bs[2]+IO_TYPE_FIXED..bs[2]+IO_TYPE_FIXED+dl[2]],b"v2;text:utf8")&&tuple_text(events,inn)&&canonical_utf8_identity(params)&&unit_ok => {if params.iter().any(|b|b&0x80!=0){return Err(78)}for i in 0..inn{scratch[i]=params[inn-1-i];}emit_result(req,bs,dl,&scratch[..inn],25,inn as u64,out)},
        _=>Err(78)
    }
}
fn run_registered_effect(req:&[u8],bs:&[usize;5],dl:&[usize;5],op:usize,op_ev:usize,ope:usize,opn:usize,effect:&[u8],registry:&ProviderRegistry,out:&mut [u8;IO_CAP])->Result<(),u8>{
    let meta=bs[4]+IO_TYPE_FIXED+dl[4];let operation=&req[op..op+opn];
    if registry.adapter!=4||operation!=registry.operation||!descriptor_is(&req[bs[0]+IO_TYPE_FIXED..bs[0]+IO_TYPE_FIXED+dl[0]],b"v2;text:utf8")||!text_events(&req[op_ev..op_ev+ope],opn,1)||!canonical_utf8_identity(operation)||!unit_descriptor(&req[bs[2]+IO_TYPE_FIXED..bs[2]+IO_TYPE_FIXED+dl[2])||!unit_descriptor(&req[bs[3]+IO_TYPE_FIXED..bs[3]+IO_TYPE_FIXED+dl[3])||!descriptor_is(&req[bs[4]+IO_TYPE_FIXED..bs[4]+IO_TYPE_FIXED+dl[4]],b"v2;bytes")||u32le(req,meta)!=Some(1)||u32le(req,meta+4)!=Some(6)||u32le(req,meta+8)!=Some(0)||u32le(req,meta+20)!=Some(6)||u32le(req,meta+24)!=Some(1)||u32le(req,meta+36)!=Some(6)||u32le(req,meta+40)!=Some(6)||u32le(req,meta+44)!=Some(6)||effect.len()<8{return Err(78)}
    let payload=u32le(effect,0).ok_or(78)? as usize;let events=u32le(effect,4).ok_or(78)? as usize;
    if events!=64||payload>IO_CAP||payload>effect.len()-8||events!=effect.len()-8-payload||!bytes_events(&effect[8+payload..],payload,5)||payload<21||&effect[8..17]!=b"RTHALENV3"||u32le(effect,17)!=Some(3)||u32le(effect,21)!=Some(1)||u32le(effect,25)!=Some((payload-21)as u32)||!env_plan_body(&effect[29..8+payload])||!execute_idempotent_record(req){return Err(78)}
    emit_effect_result(req,bs,dl,&effect[8..8+payload],out)
}
fn emit_hex<W:Write>(w:&mut W,b:&[u8])->io::Result<()> {
    const D:&[u8;16]=b"0123456789abcdef"; let mut pair=[0u8;2];
    for x in b { pair[0]=D[(x>>4)as usize];pair[1]=D[(x&15)as usize];w.write_all(&pair)?; } Ok(())
}

fn run_io(replay:bool, registry:Option<&ProviderRegistry>)->Result<(),u8>{
    // There is exactly one child request per provider process. The unsafe
    // references are non-aliasing within this synchronous entrypoint.
    unsafe {
        let req=&mut *std::ptr::addr_of_mut!(IO_REQ);
        let eff=&mut *std::ptr::addr_of_mut!(IO_EFF);
        let out=&mut *std::ptr::addr_of_mut!(IO_OUT);
        run_io_fixed(replay,req,eff,out,registry)
    }
}
fn run_io_fixed(replay:bool, req_buf:&mut [u8;IO_CAP], eff_buf:&mut [u8;IO_CAP], out:&mut [u8;IO_CAP], registry:Option<&ProviderRegistry>)->Result<(),u8>{
    let stdin=io::stdin();let mut r=stdin.lock();let(rn,en)=outer(&mut r).ok_or(70)?;
    if rn==0||rn>IO_CAP||en>IO_CAP||(!replay&&en!=0)||(replay&&en<8){return Err(71)}
    if !read_hex(&mut r,req_buf,rn)||!read_hex(&mut r,eff_buf,en){return Err(72)}
    let req=&req_buf[..rn];
    if rn<IO_HEADER||u32le(req,0)!=Some(0x324f4948)||req[4]!=2||req[5]!=0||req[6]!=0||req[7]!=0{return Err(73)}
    let mut at=IO_HEADER;let mut bs=[0usize;5];let mut dl=[0usize;5];
    for b in 0..5 { bs[b]=at;at=at.checked_add(IO_TYPE_FIXED).filter(|x|*x<=rn).ok_or(73)?;let d=u64le(req,bs[b]+40).ok_or(73)?;let n=u32le(req,bs[b]+52).ok_or(73)? as usize;
        if req[bs[b]+48]!=1||req[bs[b]+49..bs[b]+52]!=[0,0,0]||d!=n as u64||n==0{return Err(73)} at=at.checked_add(n).filter(|x|*x<=rn).ok_or(73)?;dl[b]=n; }
    let meta=at;at=at.checked_add(48).filter(|x|*x<=rn).ok_or(73)?;
    let opn=u32le(req,meta+12).ok_or(73)? as usize;let ope=u32le(req,meta+16).ok_or(73)? as usize;let inn=u32le(req,meta+28).ok_or(73)? as usize;let ine=u32le(req,meta+32).ok_or(73)? as usize;
    if u32le(req,meta)!=Some(if replay{1}else{0})||ope%16!=0||ine%16!=0{return Err(74)}
    at=at.checked_add(opn).filter(|x|*x<=rn).ok_or(73)?;let op_ev=at;at=at.checked_add(ope).filter(|x|*x<=rn).ok_or(73)?;let input=at;at=at.checked_add(inn).filter(|x|*x<=rn).ok_or(73)?;let input_ev=at;at=at.checked_add(ine).filter(|x|*x==rn).ok_or(73)?;let _=at;
    if !transcript(req,op_ev,ope/16,1)||!transcript(req,input_ev,ine/16,2){return Err(74)}
    if let Some(registry)=registry {if replay{return run_registered_effect(req,&bs,&dl,op,op_ev,ope,opn,&eff_buf[..en],registry,out)}return run_registered_operation(req,&bs,&dl,input,inn,op,op_ev,ope,opn,input_ev,ine,registry,eff_buf,out)}
    if u32le(req,meta+4)!=Some(6)||u32le(req,meta+8)!=Some(0)||u32le(req,meta+20)!=Some(6)||u32le(req,meta+24)!=Some(1)||u32le(req,meta+36)!=Some(6)||u32le(req,meta+40)!=Some(6)||u32le(req,meta+44)!=Some(6){return Err(74)}
    if dl[1]!=dl[2]||req[bs[1]..bs[1]+48]!=req[bs[2]..bs[2]+48]||req[bs[1]+IO_TYPE_FIXED..bs[1]+IO_TYPE_FIXED+dl[1]]!=req[bs[2]+IO_TYPE_FIXED..bs[2]+IO_TYPE_FIXED+dl[2]]||!unit_descriptor(&req[bs[3]+IO_TYPE_FIXED..bs[3]+IO_TYPE_FIXED+dl[3]])||(!replay&&!unit_descriptor(&req[bs[4]+IO_TYPE_FIXED..bs[4]+IO_TYPE_FIXED+dl[4]])){return Err(74)}
    let eff=&eff_buf[..en];
    let(ep,ee,eea)=if replay {let p=u32le(eff,0).ok_or(75)? as usize;let e=u32le(eff,4).ok_or(75)? as usize;let ea=8usize.checked_add(p).ok_or(75)?;if ea.checked_add(e)!=Some(en)||e%16!=0||!transcript(eff,ea,e/16,5){return Err(75)}(p,e,ea)}else{(0,0,8)};
    let mut n=0usize;if !push(&mut out,&mut n,b"RTHIOV2\0")||!push64(&mut out,&mut n,2)||!push64(&mut out,&mut n,u64le(req,8).ok_or(73)?)||!push64(&mut out,&mut n,u64le(req,16).ok_or(73)?)||!push64(&mut out,&mut n,0)||!push64(&mut out,&mut n,u64le(req,24).ok_or(73)?)||!push64(&mut out,&mut n,0)||!push64(&mut out,&mut n,1)||!push64(&mut out,&mut n,0){return Err(76)}
    for start in bs {for q in 0..6{if !push64(&mut out,&mut n,u64le(req,start+q*8).ok_or(73)?){return Err(76)}}if !push64(&mut out,&mut n,1){return Err(76)}}
    for b in 0..5{if !push(&mut out,&mut n,&req[bs[b]+IO_TYPE_FIXED..bs[b]+IO_TYPE_FIXED+dl[b]]){return Err(76)}}
    if !push64(&mut out,&mut n,6)||!push64(&mut out,&mut n,(ine/16)as u64)||!push64(&mut out,&mut n,inn as u64){return Err(76)}let copied=n;if !push(&mut out,&mut n,&req[input_ev..input_ev+ine]){return Err(76)}let arg=u64le(&out,copied+8).ok_or(76)?;out[copied+8..copied+16].copy_from_slice(&((arg&0xffff_ffff)|(3u64<<32)).to_le_bytes());
    if !push(&mut out,&mut n,&req[input..input+inn])||!unit(&mut out,&mut n,4){return Err(76)}
    if replay {if !push64(&mut out,&mut n,6)||!push64(&mut out,&mut n,(ee/16)as u64)||!push64(&mut out,&mut n,ep as u64)||!push(&mut out,&mut n,&eff[eea..eea+ee])||!push(&mut out,&mut n,&eff[8..8+ep]){return Err(76)}}else if !unit(&mut out,&mut n,5){return Err(76)}
    let stdout=io::stdout();let mut w=stdout.lock();write!(w,"RTHAL2 {}\n",n).map_err(|_|77)?;emit_hex(&mut w,&out[..n]).map_err(|_|77)?;Ok(())
}

fn run() -> Result<(), u8> {
    // Fixed-capacity capture keeps malformed/excess argv bounded without a
    // growable Vec. Query leaves the four replay-only slots empty.
    let mut incoming = env::args();
    let args: [String; REPLAY_ARGC] =
        std::array::from_fn(|_| incoming.next().unwrap_or_default());
    if args[0].is_empty() || incoming.next().is_some() {
        return Err(64);
    }
    if args[1] == "rthal-io-v2" {
        if args[3..].iter().any(|x|!x.is_empty()){return Err(64)}
        if args[2]=="compare"{return run_io(false,None)} if args[2]=="replay"{return run_io(true,None)} return Err(66)
    }
    if args[1] == "rthal-io-v3" {
        if args[5..].iter().any(|x|!x.is_empty())||args[3].is_empty()||args[3].len()>4096||!canonical_utf8_identity(args[3].as_bytes()){return Err(64)}
        let adapter: u8=args[4].parse().map_err(|_|64)?;if adapter<1||adapter>4{return Err(64)}
        let registry=ProviderRegistry{operation:args[3].as_bytes(),adapter};
        if args[2]=="compare"{if adapter==4{return Err(64)}return run_io(false,Some(&registry))}
        if args[2]=="replay"{if adapter!=4{return Err(64)}return run_io(true,Some(&registry))}
        return Err(66)
    }
    if args[..QUERY_ARGC].iter().any(String::is_empty) { return Err(64); }
    if args[1] != "rthal-scalar-v2" {
        return Err(65);
    }
    if args[2] != "compare" && args[2] != "replay" {
        return Err(66);
    }
    if args[4] != "0" && args[4] != "1" {
        return Err(67);
    }
    let effect = args[4] == "1";
    if (!effect && args[2] != "compare") || (effect && args[2] != "replay") {
        return Err(67);
    }
    if (!effect && args[QUERY_ARGC..].iter().any(|value| !value.is_empty())) ||
        (effect && args[QUERY_ARGC..].iter().any(String::is_empty)) {
        return Err(64);
    }
    let argument_count = if effect { REPLAY_ARGC } else { QUERY_ARGC };
    if args[3..argument_count].iter().any(|value| !valid_i64(value)) {
        return Err(68);
    }

    let operation: [u64; 4] = std::array::from_fn(|i| parse_word(&args[5 + i]));
    let input: [u64; 4] = std::array::from_fn(|i| parse_word(&args[9 + i]));
    let replay_trace: [u64; 4] = std::array::from_fn(|i| {
        if effect { parse_word(&args[13 + i]) } else { 0 }
    });
    let mut outcome = [0_u64; 4];
    let mut trace = [0_u64; 4];
    for i in 0..4 {
        let mut base = operation[i]
            ^ input[(i + 1) & 3].rotate_left((7 + 11 * i) as u32)
            ^ GOLDEN.wrapping_add(FNV_PRIME.wrapping_mul(i as u64));
        if effect {
            base ^= replay_trace[(i + 2) & 3].rotate_left((13 + 7 * i) as u32)
                ^ EFFECT_DOMAIN;
        }
        outcome[i] = mix64(base);
        trace[i] = if effect { replay_trace[i] } else { mix64(base ^ TRACE_DOMAIN) };
    }

    let stdout = io::stdout();
    let mut output = stdout.lock();
    output.write_all(b"RTHAL1").map_err(|_| 69)?;
    for word in outcome { write!(output, " {}", word as i64).map_err(|_| 69)?; }
    for _ in 0..4 { output.write_all(b" 0").map_err(|_| 69)?; }
    for word in trace { write!(output, " {}", word as i64).map_err(|_| 69)?; }
    output.write_all(b"\n").map_err(|_| 69)?;
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => { if code==78 { eprintln!("RTHAL-PROVIDER-E-UNKNOWN-OP"); } ExitCode::from(code) },
    }
}
