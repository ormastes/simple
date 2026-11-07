//! Interpreter projection of the shared raw owner. Never round-trip through
//! native RuntimeValue collections: allocation after COMMIT could lose a lease
//! or consume output before the interpreter owns its final typed value.
use crate::error::CompileError;
use crate::value::{ArrayData, Value};
use simple_runtime::value::interactive_process_abi_v1::*;
use simple_runtime::value::interactive_process_protocol_v1::*;
use core::mem::size_of;
use std::sync::Arc;

fn arity(args: &[Value], count: usize) -> Result<(), CompileError> {
    if args.len() == count { Ok(()) } else { Err(CompileError::runtime(format!("interactive v1: expected {count} arguments, got {}",args.len()))) }
}
fn integer(args: &[Value], index: usize) -> Result<i64, CompileError> {
    match args.get(index) { Some(Value::Int(value))=>Ok(*value), _=>Err(CompileError::runtime(format!("interactive v1: argument {index} must be i64"))) }
}
fn range(value:i64,max:u64,positive:bool)->Option<u64>{
    if value<0 || positive && value==0 || value as u64>max {None}else{Some(value as u64)}
}
fn reserve_error()->CompileError{CompileError::runtime("interactive v1: projection allocation failed before native effects")}
fn words(count:usize)->Result<Value,CompileError>{
    let mut values=Vec::new();values.try_reserve_exact(count).map_err(|_|reserve_error())?;
    values.resize(count,Value::Int(0));Ok(Value::array(values))
}
fn words_mut(value:&mut Value)->Result<&mut ArrayData,CompileError>{
    match value {Value::Array(values)=>Arc::get_mut(values).ok_or_else(reserve_error),_=>Err(reserve_error())}
}
fn fill(out:&mut ArrayData,input:&[u64]){
    // Only a uniquely owned Boxed array, fully sized before effects, reaches here.
    for (index,word) in input.iter().enumerate(){out.assign_index(index,Value::Int(*word as i64));}
}
fn bytes(max:usize)->Result<Value,CompileError>{
    let mut values=Vec::new();values.try_reserve_exact(max).map_err(|_|reserve_error())?;values.resize(max,0);
    Ok(Value::byte_array(values))
}
fn bytes_mut(value:&mut Value)->Result<&mut Vec<u8>,CompileError>{
    match value{Value::ByteArray(values)=>Arc::get_mut(values).ok_or_else(reserve_error),_=>Err(reserve_error())}
}
fn complete(out:&mut ArrayData,receipt:&mut Oiv1Receipt,transport:i64){
    let valid=transport==0 && valid_receipt(receipt,0,0);
    fill(out,&prepared_receipt_words(receipt,valid));
    let _=finish_projection(receipt,valid);
    if !valid{projection_failure(receipt);}
    fill(out,&receipt_words(receipt));
}
fn argument_strings(value:&Value,command_len:usize)->Result<Option<Vec<String>>,CompileError>{
    let values=match value{Value::Array(values)|Value::FrozenArray(values)=>values,
        _=>return Err(CompileError::runtime("interactive v1: argv must be [text]"))};
    if values.len()>OIV1_ARG_COUNT_MAX as usize || command_len>OIV1_ARG_BYTES_MAX as usize{return Ok(None);}
    let mut owned=Vec::new();owned.try_reserve_exact(values.len()).map_err(|_|reserve_error())?;
    let mut total=command_len;
    for index in 0..values.len(){
        let value=values.get_value(index).ok_or_else(reserve_error)?;
        let text=match &value{Value::Str(text)=>text.as_str(),_=>return Err(CompileError::runtime("interactive v1: argv elements must be text"))};
        total=match total.checked_add(text.len()){Some(n)if n<=OIV1_ARG_BYTES_MAX as usize=>n,_=>return Ok(None)};
        let mut copy=String::new();copy.try_reserve_exact(text.len()).map_err(|_|reserve_error())?;copy.push_str(text);owned.push(copy);
    }
    Ok(Some(owned))
}
fn byte_window(value:&Value,offset:i64,max:i64,out:&mut[u8;OIV1_WRITE_QUANTUM as usize])->Result<Option<usize>,CompileError>{
    let Some(max)=range(max,OIV1_WRITE_QUANTUM,false)else{return Ok(None)};
    if offset<0{return Ok(None);}let offset=offset as usize;
    match value{
        Value::ByteArray(data)|Value::FrozenByteArray(data)=>{
            if offset>data.len(){return Ok(None);}let n=(max as usize).min(data.len()-offset);out[..n].copy_from_slice(&data[offset..offset+n]);Ok(Some(n))
        }
        Value::Array(data)|Value::FrozenArray(data)=>{
            if offset>data.len(){return Ok(None);}let n=(max as usize).min(data.len()-offset);
            for index in 0..n{out[index]=match data.get_value(offset+index){
                Some(Value::Int(n))if(0..=255).contains(&n)=>n as u8,
                Some(Value::UInt{value:n,..})if n<=255=>n as u8,_=>return Ok(None)};}
            Ok(Some(n))
        }
        _=>Err(CompileError::runtime("interactive v1: bytes must be [u8]")),
    }
}
pub fn capabilities(args:&[Value])->Result<Value,CompileError>{
    arity(args,0)?;let mut out=words(16)?;let target=words_mut(&mut out)?;
    let mut value:Oiv1Capabilities=unsafe{core::mem::zeroed()};
    let result=unsafe{simple_owned_interactive_v1_capabilities(&mut value,size_of::<Oiv1Capabilities>() as u64)};
    if result!=0 || value.version!=OIV1_VERSION || value.size!=size_of::<Oiv1Capabilities>() as u64{
        value=unsafe{core::mem::zeroed()};value.version=OIV1_VERSION;value.size=size_of::<Oiv1Capabilities>() as u64;
        value.status=OIV1_STATUS_PROJECTIONFAILURE;value.error_domain=OIV1_ERROR_ABI;value.error_code=1;
    }
    fill(target,&capability_words(&value));Ok(out)
}
pub fn deadline(args:&[Value])->Result<Value,CompileError>{
    arity(args,1)?;let timeout=integer(args,0)?;let mut out=words(8)?;let target=words_mut(&mut out)?;
    let request=Oiv1DeadlineRequest{version:OIV1_VERSION,size:size_of::<Oiv1DeadlineRequest>() as u64,timeout_ms:timeout as u64};
    let mut value:Oiv1Deadline=unsafe{core::mem::zeroed()};let mut receipt=zero_receipt();
    let result=unsafe{simple_owned_interactive_v1_deadline(&request,size_of::<Oiv1DeadlineRequest>() as u64,&mut value,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    if result!=0 || !valid_receipt(&receipt,0,0){projection_failure(&mut receipt);}
    fill(target,&deadline_words(&value,&receipt));Ok(out)
}
pub fn start(args:&[Value])->Result<Value,CompileError>{
    arity(args,7)?;
    let command=match &args[0]{Value::Str(text)=>text.as_str(),_=>return Err(CompileError::runtime("interactive v1: command must be text"))};
    let clock=integer(args,2)?;let expires=integer(args,3)?;
    let capacities=(range(integer(args,4)?,OIV1_STDIN_MAX,true),range(integer(args,5)?,OIV1_STDOUT_MAX,true),range(integer(args,6)?,OIV1_STDERR_MAX,true));
    let mut out=words(32)?;let target=words_mut(&mut out)?;
    let (Some(stdin_capacity),Some(stdout_capacity),Some(stderr_capacity))=capacities else{fill(target,&receipt_words(&invalid_receipt()));return Ok(out)};
    if command.is_empty() || command.len()>OIV1_ARG_BYTES_MAX as usize{fill(target,&receipt_words(&invalid_receipt()));return Ok(out);}
    let Some(owned_args)=argument_strings(&args[1],command.len())?else{fill(target,&receipt_words(&invalid_receipt()));return Ok(out)};
    let mut spans=[Oiv1ConstSpan{data:core::ptr::null(),len:0};OIV1_ARG_COUNT_MAX as usize];
    for(index,text)in owned_args.iter().enumerate(){spans[index]=Oiv1ConstSpan{data:text.as_ptr(),len:text.len() as u64};}
    let request=Oiv1StartRequest{version:OIV1_VERSION,size:size_of::<Oiv1StartRequest>() as u64,
        command:Oiv1ConstSpan{data:command.as_ptr(),len:command.len() as u64},args:Oiv1Argv{data:spans.as_ptr(),count:owned_args.len() as u64},
        deadline:simple_runtime::value::interactive_process_protocol_v1::deadline(clock,expires),stdin_capacity,stdout_capacity,stderr_capacity,flags:0};
    let mut receipt=zero_receipt();
    let result=unsafe{simple_owned_interactive_v1_start_begin(&request,size_of::<Oiv1StartRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    complete(target,&mut receipt,result);Ok(out)
}
pub fn write_some(args:&[Value])->Result<Value,CompileError>{
    arity(args,7)?;let handle=integer(args,0)?;let offset=integer(args,2)?;let max=integer(args,3)?;let expected=integer(args,4)?;let clock=integer(args,5)?;let expires=integer(args,6)?;
    let mut out=words(32)?;let target=words_mut(&mut out)?;let mut buffer=[0u8;OIV1_WRITE_QUANTUM as usize];
    let Some(count)=byte_window(&args[1],offset,max,&mut buffer)?else{fill(target,&receipt_words(&invalid_receipt()));return Ok(out)};
    let request=Oiv1WriteRequest{version:OIV1_VERSION,size:size_of::<Oiv1WriteRequest>() as u64,handle,
        bytes:Oiv1ConstSpan{data:buffer.as_ptr(),len:count as u64},data_offset:0,max_bytes:count as u64,expected_accepted_total:expected as u64,
        deadline:simple_runtime::value::interactive_process_protocol_v1::deadline(clock,expires)};
    let mut receipt=zero_receipt();let result=unsafe{simple_owned_interactive_v1_write_some(&request,size_of::<Oiv1WriteRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    complete(target,&mut receipt,result);Ok(out)
}
pub fn poll(args:&[Value])->Result<Value,CompileError>{
    arity(args,6)?;let handle=integer(args,0)?;let clock=integer(args,1)?;let expires=integer(args,2)?;
    let params=match(range(integer(args,3)?,OIV1_POLL_WAIT_MAX_MS,false),range(integer(args,4)?,OIV1_OUTPUT_CHUNK_MAX,false),range(integer(args,5)?,OIV1_OUTPUT_CHUNK_MAX,false)){
        (Some(wait),Some(out),Some(err))=>Some((wait,out,err)),_=>None};
    let(wait,out_cap,err_cap)=params.unwrap_or((0,0,0));
    let mut fields=Vec::new();fields.try_reserve_exact(3).map_err(|_|reserve_error())?;
    fields.push(bytes(out_cap as usize)?);fields.push(bytes(err_cap as usize)?);fields.push(words(32)?);
    let mut out=Value::Tuple(fields);
    let fields=match &mut out{Value::Tuple(fields)=>fields,_=>unreachable!()};
    let [out_value,err_value,receipt_value]=fields.as_mut_slice() else{return Err(reserve_error())};
    let stdout=bytes_mut(out_value)?;let stderr=bytes_mut(err_value)?;let target=words_mut(receipt_value)?;
    if params.is_none(){fill(target,&receipt_words(&invalid_receipt()));return Ok(out);}
    let request=Oiv1PollRequest{version:OIV1_VERSION,size:size_of::<Oiv1PollRequest>() as u64,handle,
        deadline:simple_runtime::value::interactive_process_protocol_v1::deadline(clock,expires),wait_ms:wait,
        stdout_buffer:Oiv1MutableSpan{data:stdout.as_mut_ptr(),capacity:out_cap},stderr_buffer:Oiv1MutableSpan{data:stderr.as_mut_ptr(),capacity:err_cap}};
    let mut receipt=zero_receipt();let result=unsafe{simple_owned_interactive_v1_poll_begin(&request,size_of::<Oiv1PollRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    let valid=result==0 && valid_receipt(&receipt,out_cap,err_cap);
    stdout.truncate(if valid{receipt.stdout_count as usize}else{0});stderr.truncate(if valid{receipt.stderr_count as usize}else{0});
    fill(target,&prepared_receipt_words(&receipt,valid));
    let published=finish_projection(&mut receipt,valid);
    if !valid{projection_failure(&mut receipt);}
    stdout.truncate(if published{receipt.stdout_count as usize}else{0});stderr.truncate(if published{receipt.stderr_count as usize}else{0});
    fill(target,&receipt_words(&receipt));Ok(out)
}
type Control=unsafe extern "C" fn(*const Oiv1ControlRequest,u64,*mut Oiv1Receipt,u64)->i64;
fn control(args:&[Value],discard:bool,function:Control)->Result<Value,CompileError>{
    arity(args,if discard{4}else{3})?;let handle=integer(args,0)?;let clock=integer(args,1)?;let expires=integer(args,2)?;
    let flags=if discard{match &args[3]{Value::Bool(value)=>*value as u64,_=>return Err(CompileError::runtime("interactive v1: discard_unread must be bool"))}}else{0};
    let mut out=words(32)?;let target=words_mut(&mut out)?;let request=Oiv1ControlRequest{version:OIV1_VERSION,size:size_of::<Oiv1ControlRequest>() as u64,handle,
        deadline:simple_runtime::value::interactive_process_protocol_v1::deadline(clock,expires),flags};
    let mut receipt=zero_receipt();let result=unsafe{function(&request,size_of::<Oiv1ControlRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    complete(target,&mut receipt,result);Ok(out)
}
pub fn close_stdin(args:&[Value])->Result<Value,CompileError>{control(args,false,simple_owned_interactive_v1_close_stdin)}
pub fn cancel(args:&[Value])->Result<Value,CompileError>{control(args,false,simple_owned_interactive_v1_cancel)}
pub fn collect(args:&[Value])->Result<Value,CompileError>{control(args,true,simple_owned_interactive_v1_collect)}
pub fn release(args:&[Value])->Result<Value,CompileError>{
    arity(args,1)?;let handle=integer(args,0)?;let mut out=words(32)?;let target=words_mut(&mut out)?;
    let request=Oiv1ReleaseRequest{version:OIV1_VERSION,size:size_of::<Oiv1ReleaseRequest>() as u64,handle};
    let mut receipt=zero_receipt();let result=unsafe{simple_owned_interactive_v1_release(&request,size_of::<Oiv1ReleaseRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    complete(target,&mut receipt,result);Ok(out)
}

#[cfg(all(test,windows,target_pointer_width="64"))]
mod projection_tests {
 use super::*;
 mod driver { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../common/tests/fixtures/interactive_process_projection_driver.rs")); }
 struct Interpreter;
 fn invoke(name:&str,args:&[Value])->Value{
  let mut env=crate::value::Env::new();let mut functions=std::collections::HashMap::new();let mut classes=std::collections::HashMap::new();
  let enums=std::collections::HashMap::new();let impls=std::collections::HashMap::new();
  // Actual interpreter registry, including the host-import policy check.
  super::super::call_extern_function_with_values(name,args,&mut env,&mut functions,&mut classes,&enums,&impls).unwrap()
 }
 fn integers(value:Value,n:usize)->Vec<u64>{match value{Value::Array(data)=>{assert_eq!(data.len(),n);(0..n).map(|i|match data.get_value(i){Some(Value::Int(n))=>n as u64,other=>panic!("word representation changed: {other:?}")}).collect()},other=>panic!("receipt array missing: {other:?}")}}
 fn reply(name:&str,args:&[Value])->driver::Receipt{integers(invoke(name,args),32).try_into().unwrap()}
 fn integer(n:u64)->Value{Value::Int(n as i64)}
 impl driver::Projection for Interpreter{
  fn capabilities()->Vec<u64>{integers(invoke("rt_process_owned_interactive_v1_capabilities_value",&[]),16)}
  fn deadline(ms:i64)->[u64;8]{integers(invoke("rt_process_owned_interactive_v1_deadline_value",&[Value::Int(ms)]),8).try_into().unwrap()}
  fn start(command:&str,args:&[&str],d:[u64;8],input:i64)->driver::Receipt{
   reply("rt_process_owned_interactive_v1_start_value",&[Value::text(command),Value::array(args.iter().map(|s|Value::text(*s)).collect::<Vec<_>>()),integer(d[2]),integer(d[3]),Value::Int(input),Value::Int(262144),Value::Int(262144)])
  }
  fn write(h:i64,data:&[u8],offset:i64,max:i64,expected:u64,d:[u64;8])->driver::Receipt{
   reply("rt_process_owned_interactive_v1_write_some_value",&[Value::Int(h),Value::byte_array(data.to_vec()),Value::Int(offset),Value::Int(max),integer(expected),integer(d[2]),integer(d[3])])
  }
  fn poll(h:i64,d:[u64;8],wait:i64,out:i64,err:i64)->driver::Poll{
   let value=invoke("rt_process_owned_interactive_v1_poll_value",&[Value::Int(h),integer(d[2]),integer(d[3]),Value::Int(wait),Value::Int(out),Value::Int(err)]);
   match value{Value::Tuple(mut fields)=>{assert_eq!(fields.len(),3);let receipt=integers(fields.pop().unwrap(),32).try_into().unwrap();
    let stderr=match fields.pop().unwrap(){Value::ByteArray(data)=>(*data).clone(),other=>panic!("stderr byte family changed: {other:?}")};
    let stdout=match fields.pop().unwrap(){Value::ByteArray(data)=>(*data).clone(),other=>panic!("stdout byte family changed: {other:?}")};driver::Poll{stdout,stderr,receipt}},other=>panic!("poll tuple changed: {other:?}")}
  }
  fn close(h:i64,d:[u64;8])->driver::Receipt{reply("rt_process_owned_interactive_v1_close_stdin_value",&[Value::Int(h),integer(d[2]),integer(d[3])])}
  fn cancel(h:i64,d:[u64;8])->driver::Receipt{reply("rt_process_owned_interactive_v1_cancel_value",&[Value::Int(h),integer(d[2]),integer(d[3])])}
  fn collect(h:i64,d:[u64;8],discard:bool)->driver::Receipt{reply("rt_process_owned_interactive_v1_collect_value",&[Value::Int(h),integer(d[2]),integer(d[3]),Value::Bool(discard)])}
  fn release(h:i64)->driver::Receipt{reply("rt_process_owned_interactive_v1_release_value",&[Value::Int(h)])}
 }
 #[test]fn interactive_interpreter_availability_and_clock(){driver::availability_and_clock::<Interpreter>();}
 #[test]fn interactive_interpreter_invalid_ranges_and_stale(){driver::invalid_ranges_and_stale::<Interpreter>();}
 #[test]fn interactive_interpreter_expired_start_is_unowned(){driver::expired_start_is_unowned::<Interpreter>();}
 #[test]fn interactive_interpreter_wrong_clock_is_unowned(){driver::wrong_clock_is_unowned::<Interpreter>();}
 #[test]#[ignore="requires hash-pinned shared C peer and bounded qualification runner"]
 fn interactive_interpreter_persistent_raw_exchange(){driver::persistent_exchange::<Interpreter>();}
 #[test]#[ignore="requires hash-pinned shared C peer and bounded qualification runner"]
 fn interactive_interpreter_cancel_collects_real_owner(){driver::cancel_collects_real_owner::<Interpreter>();}
 #[test]fn interactive_interpreter_full_word_receipt_and_private_tickets(){
  let mut receipt=zero_receipt();receipt.accepted_total=u64::MAX;receipt.exit_value=i64::MIN;receipt.ticket0=17;receipt.ticket3=u64::MAX;
  let mut out=words(32).unwrap();fill(words_mut(&mut out).unwrap(),&receipt_words(&receipt));let data=integers(out,32);
  assert_eq!(data[14],u64::MAX);assert_eq!(data[10],i64::MIN as u64);assert_eq!(&data[28..],&[0,0,0,0]);
 }
}
