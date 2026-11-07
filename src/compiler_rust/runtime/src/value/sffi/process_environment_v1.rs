//! Canonical Rust runtime lane of the private child-environment boundary.
//! Own RuntimeValue strings and Child registry; never borrow C heap receipts.
use super::{rt_array_get, rt_array_len, rt_string_data, rt_string_len, rt_string_new, RuntimeValue};
use std::cell::UnsafeCell;

struct Receipt { words: [i64; 4], text: [RuntimeValue; 2] }
impl Receipt {
    fn replace(&mut self, out: &[u8], err: &[u8], status: i64, flags: i64) -> *mut i64 {
        for value in self.text { if value != RuntimeValue::NIL { crate::value::collections::rt_string_free(value); } }
        self.text = [rt_string_new(out.as_ptr(), out.len() as u64), rt_string_new(err.as_ptr(), err.len() as u64)];
        self.words = [self.text[0].to_raw() as i64, self.text[1].to_raw() as i64, status, flags];
        self.words.as_mut_ptr()
    }
}
impl Drop for Receipt {
    fn drop(&mut self) { for value in self.text { if value != RuntimeValue::NIL { crate::value::collections::rt_string_free(value); } } }
}
thread_local! { static RECEIPT: UnsafeCell<Receipt> = const { UnsafeCell::new(Receipt { words: [3,3,-1,8], text: [RuntimeValue::NIL;2] }) }; }
fn receipt(out: &[u8], err: &[u8], status: i64, flags: i64) -> *mut i64 {
    RECEIPT.with(|cell| unsafe { (&mut *cell.get()).replace(out,err,status,flags) })
}

unsafe fn text(value: RuntimeValue) -> Result<String, String> {
    if value == RuntimeValue::NIL { return Ok(String::new()); }
    let len = rt_string_len(value);
    if !(0..=16_777_216).contains(&len) { return Err("invalid child environment text extent".into()); }
    let ptr = rt_string_data(value);
    if len > 0 && ptr.is_null() { return Err("invalid child environment text pointer".into()); }
    let bytes = if len == 0 { &[][..] } else { std::slice::from_raw_parts(ptr,len as usize) };
    if bytes.contains(&0) { return Err("child environment text contains NUL".into()); }
    std::str::from_utf8(bytes).map(str::to_owned).map_err(|_| "child environment text is not UTF8".into())
}

#[cfg(windows)]
mod windows {
    use super::*;
    use std::{cmp::Ordering, ffi::OsString, os::windows::ffi::OsStringExt, process::{Command,Stdio}};
    #[link(name="kernel32")]
    extern "system" {
        fn CompareStringOrdinal(a:*const u16,alen:i32,b:*const u16,blen:i32,ignore:i32)->i32;
        fn GetEnvironmentStringsW()->*mut u16;
        fn FreeEnvironmentStringsW(block:*mut u16)->i32;
        fn PeekNamedPipe(pipe:*mut std::ffi::c_void,buffer:*mut std::ffi::c_void,size:u32,read:*mut u32,available:*mut u32,left:*mut u32)->i32;
    }
    type Pair = (Vec<u16>,Vec<u16>);
    fn compare(a:&[u16],b:&[u16])->Ordering {
        match unsafe { CompareStringOrdinal(a.as_ptr(),a.len() as i32,b.as_ptr(),b.len() as i32,1) } {
            1=>Ordering::Less,2=>Ordering::Equal,3=>Ordering::Greater,_=>unreachable!("validated ordinal comparison")
        }
    }
    fn valid_key(key:&[u16])->bool {
        !key.is_empty() && key.len()<=32767 && !key.contains(&0) &&
        (if key[0]==61 { key.len()==3 && key[2]==58 && ((65..=90).contains(&key[1]) || (97..=122).contains(&key[1])) } else { !key.contains(&61) })
    }
    fn sorted(mut pairs:Vec<Pair>)->Result<Vec<Pair>,String> {
        if pairs.len()>65536 { return Err("child environment entry bound exceeded".into()); }
        pairs.sort_by(|a,b|compare(&a.0,&b.0));
        if pairs.windows(2).any(|p|compare(&p[0].0,&p[1].0)==Ordering::Equal) { return Err("duplicate child environment alias".into()); }
        Ok(pairs)
    }
    unsafe fn inherited()->Result<Vec<Pair>,String> {
        struct Block(*mut u16);
        impl Drop for Block { fn drop(&mut self){unsafe{FreeEnvironmentStringsW(self.0);}} }
        let raw=GetEnvironmentStringsW();if raw.is_null(){return Err("environment snapshot failed".into());}
        let block=Block(raw);let mut offset=0;let mut result=Vec::new();
        while offset<1_048_576 && *block.0.add(offset)!=0 {
            let start=offset;
            while offset<1_048_576 && *block.0.add(offset)!=0 {offset+=1;}
            if offset==1_048_576{return Err("environment snapshot bound exceeded".into());}
            let item=std::slice::from_raw_parts(block.0.add(start),offset-start);
            let split=item.iter().enumerate().skip(1).find(|(_,c)|**c==61).map(|(i,_)|i).ok_or("invalid inherited environment assignment")?;
            if !valid_key(&item[..split]) {return Err("invalid inherited environment name".into());}
            result.push((item[..split].to_vec(),item[split+1..].to_vec()));offset+=1;
        }
        if offset>=1_048_576{return Err("environment snapshot bound exceeded".into());}
        sorted(result)
    }
    unsafe fn environment(array:RuntimeValue,mode:i64)->Result<Vec<Pair>,String> {
        if mode!=0 && mode!=1{return Err("invalid child environment mode".into());}
        let count=if array==RuntimeValue::NIL {0}else{rt_array_len(array)};
        if !(0..=65536).contains(&count){return Err("invalid child environment array".into());}
        let mut input=Vec::new();let mut bytes=0usize;
        for n in 0..count {
            let item=text(rt_array_get(array,n))?;bytes=bytes.checked_add(item.len()).ok_or("child environment byte overflow")?;
            if bytes>4_194_304{return Err("child environment byte bound exceeded".into());}
            let split=item.as_bytes().iter().enumerate().skip(1).find(|(_,c)|**c==b'=').map(|(i,_)|i).ok_or("invalid child environment assignment")?;
            let key:Vec<u16>=item[..split].encode_utf16().collect();let value:Vec<u16>=item[split+1..].encode_utf16().collect();
            if !valid_key(&key){return Err("invalid child environment name".into());}input.push((key,value));
        }
        let mut requested=sorted(input)?.into_iter().peekable();
        let mut inherited=(if mode==0 {inherited()?}else{Vec::new()}).into_iter().peekable();
        let mut result=Vec::new();
        while let (Some(parent),Some(overlay))=(inherited.peek(),requested.peek()) {
            match compare(&parent.0,&overlay.0) {
                Ordering::Less=>result.push(inherited.next().unwrap()),
                Ordering::Equal=>{inherited.next();result.push(requested.next().unwrap());},
                Ordering::Greater=>result.push(requested.next().unwrap())
            }
        }
        result.extend(inherited);result.extend(requested);
        if result.len()>65536{return Err("child environment entry bound exceeded".into());}
        let units=result.iter().try_fold(1usize,|sum,p|sum.checked_add(p.0.len()+p.1.len()+2)).ok_or("environment unit overflow")?;
        if units>1_048_576{return Err("child environment unit bound exceeded".into());}Ok(result)
    }
    pub(super) unsafe fn command(ptr:*const u8,len:u64,args:RuntimeValue,env:RuntimeValue,mode:i64)->Result<Command,String> {
        if ptr.is_null() || len==0 || len>1_048_576{return Err("invalid child command extent".into());}
        let raw=std::slice::from_raw_parts(ptr,len as usize);if raw.contains(&0){return Err("invalid child command NUL".into());}
        let name=std::str::from_utf8(raw).map_err(|_|"invalid child command UTF8")?;
        let count=if args==RuntimeValue::NIL {0}else{rt_array_len(args)};
        if !(0..=32768).contains(&count){return Err("invalid child arguments".into());}
        let mut command=Command::new(name);
        for n in 0..count {command.arg(text(rt_array_get(args,n))?);}
        command.env_clear();
        for (key,value) in environment(env,mode)? {command.env(OsString::from_wide(&key),OsString::from_wide(&value));}
        Ok(command)
    }
    // Poll the actual scope-owned pipe; no detached IO workers or handle transfer.
    fn poll<R:std::io::Read+std::os::windows::io::AsRawHandle>(pipe:&mut R,bytes:&mut Vec<u8>,cap:usize)->Result<bool,String> {
        let mut available=0;
        let ok=unsafe{PeekNamedPipe(pipe.as_raw_handle(),std::ptr::null_mut(),0,std::ptr::null_mut(),&mut available,std::ptr::null_mut())};
        if ok==0 {
            let error=std::io::Error::last_os_error();
            return if error.raw_os_error()==Some(109){Ok(true)}else{Err(error.to_string())};
        }
        if available==0{return Ok(false);}
        let mut chunk=[0u8;8192];let extent=(available as usize).min(chunk.len());
        let count=pipe.read(&mut chunk[..extent]).map_err(|e|e.to_string())?;
        let keep=(cap-bytes.len()).min(count);bytes.extend_from_slice(&chunk[..keep]);Ok(count==0)
    }
    fn stop(child:&mut std::process::Child,job:&super::super::process_bytes_windows::CaptureJob)->Result<std::process::ExitStatus,String> {
        use std::time::{Instant,Duration};
        let job_error=job.terminate().err();
        if !matches!(child.try_wait(),Ok(Some(_))) {let _=child.kill();}
        let deadline=Instant::now()+Duration::from_secs(5);
        loop {
            match child.try_wait(){
                Ok(Some(status))=>return if let Some(error)=job_error {Err(error.to_string())}else{Ok(status)},
                Ok(None)=>{},Err(error)=>return Err(error.to_string())
            }
            if Instant::now()>=deadline{return Err("child termination/reap deadline exceeded".into());}
            std::thread::sleep(Duration::from_millis(1));
        }
    }
    pub(super) fn capture(mut command:Command,timeout:i64,cap:i64)->Result<(Vec<u8>,Vec<u8>,i64,i64),String> {
        use std::time::{Instant,Duration};
        command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
        let (mut child,job)=super::super::process_bytes_windows::spawn(&mut command).map_err(|e|e.to_string())?;
        let deadline=match Instant::now().checked_add(Duration::from_millis(timeout as u64)) {
            Some(value)=>value,None=>{let _=stop(&mut child,&job);return Err("child deadline overflow".into());}
        };
        let mut out=Vec::new();let mut err=Vec::new();let mut out_eof=false;let mut err_eof=false;
        let mut status=None;let mut drain_deadline=None;let mut timed=false;
        let result=(|| {
            loop {
                if status.is_none() {
                    status=child.try_wait().map_err(|e|e.to_string())?;
                    if status.is_some() {job.terminate().map_err(|e|e.to_string())?;drain_deadline=Some(Instant::now()+Duration::from_secs(5));}
                }
                if !out_eof {out_eof=poll(child.stdout.as_mut().ok_or("missing child stdout")?,&mut out,cap as usize+1)?;}
                if !err_eof {err_eof=poll(child.stderr.as_mut().ok_or("missing child stderr")?,&mut err,cap as usize+1)?;}
                if status.is_some()&&out_eof&&err_eof {return Ok::<_,String>(());}
                if !timed&&status.is_none()&&Instant::now()>=deadline {
                    timed=true;status=Some(stop(&mut child,&job)?);drain_deadline=Some(Instant::now()+Duration::from_secs(5));
                }
                if drain_deadline.is_some_and(|end|Instant::now()>=end) {return Err("child pipe EOF drain deadline exceeded".into());}
                std::thread::sleep(Duration::from_millis(1));
            }
        })();
        if let Err(error)=result {let cleanup=stop(&mut child,&job);return Err(match cleanup {Ok(_)=>error,Err(cleanup)=>error+"; cleanup: "+&cleanup});}
        let status=status.ok_or("child exit receipt missing")?;
        // C capture reserves -1 for the requested deadline outcome even after
        // cleanup obtains the real terminated-child exit receipt.
        let exit_code=if timed {-1}else{status.code().map(i64::from).unwrap_or(-1)};
        let flags=(timed as i64)|(((out.len()>cap as usize) as i64)<<1)|(((err.len()>cap as usize) as i64)<<2);
        if flags!=0 {Ok((Vec::new(),Vec::new(),exit_code,flags))}
        else {
            std::str::from_utf8(&out).map_err(|_|"child stdout is not UTF8")?;
            std::str::from_utf8(&err).map_err(|_|"child stderr is not UTF8")?;
            Ok((out,err,exit_code,0))
        }
    }
}

/// Borrowed per-thread raw four-word receipt, copied before the next call.
#[no_mangle]
pub unsafe extern "C" fn rt_process_run_bounded_environment_tuple_v1(ptr:*const u8,len:u64,args:RuntimeValue,env:RuntimeValue,mode:i64,timeout:i64,cap:i64)->*mut i64 {
    #[cfg(windows)] {
        if timeout<=0 || !(1..=16_777_216).contains(&cap){return receipt(b"",b"invalid child capture limits",-1,8);}
        match windows::command(ptr,len,args,env,mode).and_then(|cmd|windows::capture(cmd,timeout,cap)) {
            Ok((out,err,status,flags))=>receipt(&out,&err,status,flags),Err(error)=>receipt(b"",error.as_bytes(),-1,8)
        }
    }
    #[cfg(not(windows))] {let _=(ptr,len,args,env,mode,timeout,cap);std::ptr::null_mut()}
}

/// ABI twin for admission-bounded capture. This Rust lane has no pre-exec /
/// suspended-resume admission handshake, so it must reject before spawning.
/// Only the admitted core-C owner implements that capability; invoking the
/// ordinary Rust capture here would silently reintroduce the deadline race.
#[no_mangle]
pub unsafe extern "C" fn rt_process_run_bounded_admitted_tuple_v1(
    ptr: *const u8, len: u64, args: RuntimeValue, env: RuntimeValue, mode: i64,
    timeout: i64, cap: i64, expires_at_unix_ms: i64,
) -> *mut i64 {
    let _ = (ptr, len, args, env, mode, timeout, cap, expires_at_unix_ms);
    receipt(b"", b"admitted capture requires native core-C owner", -1, 8 | 64)
}

/// This lane does not provide the native authoritative capture-limit receipt.
#[no_mangle]
pub unsafe extern "C" fn rt_process_run_bounded_observed_tuple_v1(
    ptr: *const u8, len: u64, args: RuntimeValue, timeout: i64, cap: i64,
) -> *mut i64 {
    let _ = (ptr, len, args, timeout, cap);
    receipt(b"", b"observed capture requires native core-C owner", -1, 8 | 64)
}

/// The Rust lane has no shared native PTY owner-thread binding. Refuse; a
/// thread DWORD or fresh per-call HANDLE cannot authorize the C/Simple owner.
#[no_mangle]
pub unsafe extern "C" fn rt_windows_pty_owner_thread_guard_v1() -> i64 { 0 }

/// Uses the same Rust Child registry consumed by wait, kill and liveness.
#[no_mangle]
pub unsafe extern "C" fn rt_process_spawn_async_environment_v1(ptr:*const u8,len:u64,args:RuntimeValue,env:RuntimeValue,mode:i64)->i64 {
    #[cfg(windows)] {
        let mut command=match windows::command(ptr,len,args,env,mode){Ok(cmd)=>cmd,Err(_)=>return -22};
        command.stdin(std::process::Stdio::null()).stdout(std::process::Stdio::inherit()).stderr(std::process::Stdio::inherit());
        match command.spawn(){Ok(child)=>super::publish_spawned_child(&super::SPAWNED_CHILDREN,child),Err(_)=>-1}
    }
    #[cfg(not(windows))] {let _=(ptr,len,args,env,mode);-95}
}
