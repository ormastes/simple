//! Rust-value projection of the one C interactive-process owner.
//! All result storage is allocated before effects; typed profile-local buffers
//! are cached before admission. No RuntimeValue boxing/allocation follows a call.
use super::interactive_process_abi_v1::*;
use super::interactive_process_protocol_v1::*;
use super::collections::{RuntimeArray, RuntimeString, rt_array_new_with_cap_u64, rt_array_free,
    rt_byte_array_new_len, rt_tuple_new, rt_tuple_set, rt_tuple_free};
use super::heap::{get_typed_ptr, get_typed_ptr_packed, HeapObjectType, gc_flags};
use super::RuntimeValue;
use core::mem::size_of;

struct Words { value: RuntimeValue, data: *mut u64, count: usize }
impl Words {
    fn new(count: usize) -> Option<Self> {
        let value = rt_array_new_with_cap_u64(count as i64);
        if value.is_nil() { return None; }
        // This pointer comes from the Rust allocator above, NOT a C-profile
        // collection. Only this unpublished owner may mutate its typed storage.
        let array = value.as_heap_ptr().cast::<RuntimeArray>();
        unsafe {
            if array.is_null() || (*array).header.object_type != HeapObjectType::Array ||
                !(*array).is_u64_packed() || (*array).capacity < count as u64 || (*array).data.is_null() {
                rt_array_free(value); return None;
            }
            (*array).header.gc_flags |= gc_flags::LAZY_WORDS;
            (*array).len = count as u64;
            let data = (*array).data.cast::<u64>();
            core::ptr::write_bytes(data, 0, count);
            Some(Self { value, data, count })
        }
    }
    fn fill(&mut self, words: &[u64]) {
        assert_eq!(words.len(), self.count);
        unsafe { core::ptr::copy_nonoverlapping(words.as_ptr(), self.data, self.count); }
    }
    fn take(mut self) -> RuntimeValue { let value = self.value; self.value = RuntimeValue::NIL; value }
    fn disarm(&mut self) { self.value = RuntimeValue::NIL; }
}
impl Drop for Words { fn drop(&mut self) { if !self.value.is_nil() { rt_array_free(self.value); } } }
struct Bytes { value: RuntimeValue, array: *mut RuntimeArray, data: *mut u8, max: u64 }
impl Bytes {
    fn new(max: u64) -> Option<Self> {
        let value = rt_byte_array_new_len(max);
        if value.is_nil() { return None; }
        let array = value.as_heap_ptr().cast::<RuntimeArray>();
        unsafe {
            if array.is_null() || !(*array).is_byte_packed() || (*array).capacity < max || (*array).data.is_null() {
                rt_array_free(value); return None;
            }
            Some(Self { value, array, data: (*array).data.cast(), max })
        }
    }
    fn span(&self) -> Oiv1MutableSpan { Oiv1MutableSpan { data: self.data, capacity: self.max } }
    fn truncate(&mut self, count: u64) { assert!(count <= self.max); unsafe { (*self.array).len = count; } }
    fn disarm(&mut self) { self.value = RuntimeValue::NIL; }
}
impl Drop for Bytes { fn drop(&mut self) { if !self.value.is_nil() { rt_array_free(self.value); } } }
struct Tuple(RuntimeValue);
impl Drop for Tuple { fn drop(&mut self) { if !self.0.is_nil() { rt_tuple_free(self.0); } } }
fn finish(mut storage: Words, mut receipt: Oiv1Receipt, transport: i64) -> RuntimeValue {
    let valid = transport == 0 && valid_receipt(&receipt, 0, 0);
    storage.fill(&prepared_receipt_words(&receipt, valid));
    if !valid { let _ = finish_projection(&mut receipt, false); projection_failure(&mut receipt); }
    else { let _ = finish_projection(&mut receipt, true); }
    storage.fill(&receipt_words(&receipt)); storage.take()
}
fn invalid(mut storage: Words) -> RuntimeValue { storage.fill(&receipt_words(&invalid_receipt())); storage.take() }
fn capacity(value: i64, max: u64, positive: bool) -> Option<u64> {
    if value < 0 || positive && value == 0 || value as u64 > max { None } else { Some(value as u64) }
}
fn argv_spans(args: RuntimeValue, spans: &mut [Oiv1ConstSpan; OIV1_ARG_COUNT_MAX as usize], command_len: u64) -> Option<u64> {
    let array = get_typed_ptr_packed::<RuntimeArray>(args, HeapObjectType::Array)?;
    unsafe {
        if (*array).is_byte_packed() || (*array).is_u64_packed() || (*array).len > OIV1_ARG_COUNT_MAX { return None; }
        let mut bytes = command_len;
        for index in 0..(*array).len as usize {
            let value = *(*array).data.add(index);
            let string = get_typed_ptr::<RuntimeString>(value, HeapObjectType::String)?;
            let data = (*string).as_bytes();
            bytes = bytes.checked_add(data.len() as u64)?;
            if bytes > OIV1_ARG_BYTES_MAX { return None; }
            spans[index] = Oiv1ConstSpan { data: data.as_ptr(), len: data.len() as u64 };
        }
        Some((*array).len)
    }
}
fn bytes_window(value: RuntimeValue, offset: i64, max: i64, output: &mut [u8; OIV1_WRITE_QUANTUM as usize]) -> Option<usize> {
    let max = capacity(max, OIV1_WRITE_QUANTUM, false)? as usize;
    if offset < 0 { return None; }
    let array = get_typed_ptr_packed::<RuntimeArray>(value, HeapObjectType::Array)?;
    unsafe {
        let offset = offset as u64;
        if offset > (*array).len { return None; }
        let count = max.min(((*array).len - offset) as usize);
        for index in 0..count {
            let position = offset as usize + index;
            let byte = if (*array).is_byte_packed() { *(*array).data.cast::<u8>().add(position) as u64 }
                else if (*array).is_u64_packed() { *(*array).data.cast::<u64>().add(position) }
                else {
                    let item = *(*array).data.add(position);
                    let number = if item.is_int() { item.as_int() as u64 }
                        else if let Some(value) = item.as_heap_u64() { value }
                        else if let Some(value) = item.as_heap_i64() { value as u64 }
                        else { return None; };
                    if number > 255 { return None; }
                    number
                };
            if byte > 255 { return None; }
            output[index] = byte as u8;
        }
        Some(count)
    }
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_capabilities_value() -> RuntimeValue {
    let Some(mut out) = Words::new(16) else { return RuntimeValue::NIL; };
    let mut value: Oiv1Capabilities = unsafe { core::mem::zeroed() };
    let result = unsafe { simple_owned_interactive_v1_capabilities(&mut value, size_of::<Oiv1Capabilities>() as u64) };
    if result != 0 || value.version != OIV1_VERSION || value.size != size_of::<Oiv1Capabilities>() as u64 {
        value = unsafe { core::mem::zeroed() }; value.version = OIV1_VERSION; value.size = size_of::<Oiv1Capabilities>() as u64;
        value.status = OIV1_STATUS_PROJECTIONFAILURE; value.error_domain = OIV1_ERROR_ABI; value.error_code = 1;
    }
    out.fill(&capability_words(&value)); out.take()
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_deadline_value(timeout_ms: i64) -> RuntimeValue {
    let Some(mut out) = Words::new(8) else { return RuntimeValue::NIL; };
    let request = Oiv1DeadlineRequest { version: OIV1_VERSION, size: size_of::<Oiv1DeadlineRequest>() as u64, timeout_ms: timeout_ms as u64 };
    let mut value: Oiv1Deadline = unsafe { core::mem::zeroed() }; let mut receipt = zero_receipt();
    let result = unsafe { simple_owned_interactive_v1_deadline(&request, size_of::<Oiv1DeadlineRequest>() as u64, &mut value, &mut receipt, size_of::<Oiv1Receipt>() as u64) };
    if result != 0 || !valid_receipt(&receipt, 0, 0) { projection_failure(&mut receipt); }
    out.fill(&deadline_words(&value, &receipt)); out.take()
}
#[no_mangle]
pub unsafe extern "C" fn rt_process_owned_interactive_v1_start_value(command: *const u8, command_len: u64,
    args: RuntimeValue, clock_tag: i64, expires_ms: i64, stdin_cap: i64, stdout_cap: i64, stderr_cap: i64) -> RuntimeValue {
    let Some(out) = Words::new(32) else { return RuntimeValue::NIL; };
    let (Some(stdin_capacity),Some(stdout_capacity),Some(stderr_capacity)) =
        (capacity(stdin_cap,OIV1_STDIN_MAX,true),capacity(stdout_cap,OIV1_STDOUT_MAX,true),capacity(stderr_cap,OIV1_STDERR_MAX,true))
        else { return invalid(out); };
    if command_len == 0 || command_len > OIV1_ARG_BYTES_MAX || command.is_null() { return invalid(out); }
    let mut spans = [Oiv1ConstSpan { data: core::ptr::null(), len: 0 }; OIV1_ARG_COUNT_MAX as usize];
    let Some(count) = argv_spans(args,&mut spans,command_len) else { return invalid(out); };
    let request = Oiv1StartRequest { version: OIV1_VERSION, size: size_of::<Oiv1StartRequest>() as u64,
        command: Oiv1ConstSpan { data: command, len: command_len }, args: Oiv1Argv { data: spans.as_ptr(), count },
        deadline: deadline(clock_tag, expires_ms), stdin_capacity, stdout_capacity, stderr_capacity, flags: 0 };
    let mut receipt = zero_receipt();
    let result = unsafe { simple_owned_interactive_v1_start_begin(&request,size_of::<Oiv1StartRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64) };
    finish(out,receipt,result)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_write_some_value(handle: i64, bytes: RuntimeValue,
    offset: i64, max_bytes: i64, expected_accepted_total: i64, clock_tag: i64, expires_ms: i64) -> RuntimeValue {
    let Some(out) = Words::new(32) else { return RuntimeValue::NIL; };
    let mut buffer = [0u8; OIV1_WRITE_QUANTUM as usize];
    let Some(count) = bytes_window(bytes,offset,max_bytes,&mut buffer) else { return invalid(out); };
    let request = Oiv1WriteRequest { version: OIV1_VERSION, size: size_of::<Oiv1WriteRequest>() as u64, handle,
        bytes: Oiv1ConstSpan { data: buffer.as_ptr(), len: count as u64 }, data_offset: 0, max_bytes: count as u64,
        expected_accepted_total: expected_accepted_total as u64, deadline: deadline(clock_tag,expires_ms) };
    let mut receipt = zero_receipt();
    let result = unsafe { simple_owned_interactive_v1_write_some(&request,size_of::<Oiv1WriteRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64) };
    finish(out,receipt,result)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_poll_value(handle: i64, clock_tag: i64, expires_ms: i64,
    wait_ms: i64, stdout_max: i64, stderr_max: i64) -> RuntimeValue {
    let parameters = match (capacity(stdout_max,OIV1_OUTPUT_CHUNK_MAX,false),capacity(stderr_max,OIV1_OUTPUT_CHUNK_MAX,false),capacity(wait_ms,OIV1_POLL_WAIT_MAX_MS,false)) {
        (Some(out),Some(err),Some(wait)) => Some((out,err,wait)), _ => None,
    };
    let (stdout_max,stderr_max,wait_ms) = parameters.unwrap_or((0,0,0));
    let Some(mut words)=Words::new(32) else{return RuntimeValue::NIL};
    let Some(mut stdout)=Bytes::new(stdout_max) else{return RuntimeValue::NIL};
    let Some(mut stderr)=Bytes::new(stderr_max) else{return RuntimeValue::NIL};
    let mut tuple=Tuple(rt_tuple_new(3)); if tuple.0.is_nil(){return RuntimeValue::NIL;}
    if !rt_tuple_set(tuple.0,0,stdout.value) || !rt_tuple_set(tuple.0,1,stderr.value) || !rt_tuple_set(tuple.0,2,words.value) {return RuntimeValue::NIL;}
    if parameters.is_none() {
        words.fill(&receipt_words(&invalid_receipt()));
        stdout.disarm();stderr.disarm();words.disarm();let value=tuple.0;tuple.0=RuntimeValue::NIL;return value;
    }
    let request=Oiv1PollRequest{version:OIV1_VERSION,size:size_of::<Oiv1PollRequest>() as u64,handle,
        deadline:deadline(clock_tag,expires_ms),wait_ms,stdout_buffer:stdout.span(),stderr_buffer:stderr.span()};
    let mut receipt=zero_receipt();
    let result=unsafe{simple_owned_interactive_v1_poll_begin(&request,size_of::<Oiv1PollRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    let valid=result==0 && valid_receipt(&receipt,stdout_max,stderr_max);
    stdout.truncate(if valid{receipt.stdout_count}else{0});stderr.truncate(if valid{receipt.stderr_count}else{0});
    words.fill(&prepared_receipt_words(&receipt,valid));
    let published=finish_projection(&mut receipt,valid);
    if !valid{projection_failure(&mut receipt);}
    stdout.truncate(if published{receipt.stdout_count}else{0});stderr.truncate(if published{receipt.stderr_count}else{0});
    words.fill(&receipt_words(&receipt));
    stdout.disarm();stderr.disarm();words.disarm();let value=tuple.0;tuple.0=RuntimeValue::NIL;value
}
type Control = unsafe extern "C" fn(*const Oiv1ControlRequest,u64,*mut Oiv1Receipt,u64)->i64;
fn control(handle:i64,clock_tag:i64,expires_ms:i64,flags:u64,function:Control)->RuntimeValue{
    let Some(out)=Words::new(32) else{return RuntimeValue::NIL};
    let request=Oiv1ControlRequest{version:OIV1_VERSION,size:size_of::<Oiv1ControlRequest>() as u64,handle,
        deadline:deadline(clock_tag,expires_ms),flags};let mut receipt=zero_receipt();
    let result=unsafe{function(&request,size_of::<Oiv1ControlRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    finish(out,receipt,result)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_close_stdin_value(handle:i64,clock_tag:i64,expires_ms:i64)->RuntimeValue{
    control(handle,clock_tag,expires_ms,0,simple_owned_interactive_v1_close_stdin)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_cancel_value(handle:i64,clock_tag:i64,expires_ms:i64)->RuntimeValue{
    control(handle,clock_tag,expires_ms,0,simple_owned_interactive_v1_cancel)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_collect_value(handle:i64,clock_tag:i64,expires_ms:i64,discard_unread:bool)->RuntimeValue{
    control(handle,clock_tag,expires_ms,discard_unread as u64,simple_owned_interactive_v1_collect)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_release_value(handle:i64)->RuntimeValue{
    let Some(out)=Words::new(32) else{return RuntimeValue::NIL};
    let request=Oiv1ReleaseRequest{version:OIV1_VERSION,size:size_of::<Oiv1ReleaseRequest>() as u64,handle};let mut receipt=zero_receipt();
    let result=unsafe{simple_owned_interactive_v1_release(&request,size_of::<Oiv1ReleaseRequest>() as u64,&mut receipt,size_of::<Oiv1Receipt>() as u64)};
    finish(out,receipt,result)
}

#[cfg(all(test,windows,target_pointer_width="64"))]
mod projection_tests {
 use super::*;
 use crate::value::{rt_array_new,rt_array_push,rt_string_new,rt_string_free,rt_tuple_len,rt_tuple_get};
 mod driver { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../common/tests/fixtures/interactive_process_projection_driver.rs")); }
 struct Native;
 fn take_words(value:RuntimeValue,n:usize)->Vec<u64>{
  assert!(!value.is_nil(),"projection returned no receipt");let p=get_typed_ptr_packed::<RuntimeArray>(value,HeapObjectType::Array).expect("actual Rust array family");
  let words=unsafe{assert_eq!((*p).len,n as u64);assert!((*p).is_u64_packed());core::slice::from_raw_parts((*p).data.cast::<u64>(),n).to_vec()};rt_array_free(value);words
 }
 fn take_receipt(value:RuntimeValue)->driver::Receipt{take_words(value,32).try_into().unwrap()}
 fn take_bytes(value:RuntimeValue)->Vec<u8>{
  let p=get_typed_ptr_packed::<RuntimeArray>(value,HeapObjectType::Array).expect("actual byte-array family");
  let bytes=unsafe{assert!((*p).is_byte_packed());core::slice::from_raw_parts((*p).data.cast::<u8>(),(*p).len as usize).to_vec()};rt_array_free(value);bytes
 }
 impl driver::Projection for Native {
  fn capabilities()->Vec<u64>{take_words(rt_process_owned_interactive_v1_capabilities_value(),16)}
  fn deadline(ms:i64)->[u64;8]{take_words(rt_process_owned_interactive_v1_deadline_value(ms),8).try_into().unwrap()}
  fn start(command:&str,args:&[&str],d:[u64;8],input_cap:i64)->driver::Receipt{
   let argv=rt_array_new(args.len() as u64);assert!(!argv.is_nil());let mut owned=Vec::new();
   for arg in args{let text=rt_string_new(arg.as_ptr(),arg.len() as u64);assert!(!text.is_nil());assert!(rt_array_push(argv,text));owned.push(text);}
   let result=unsafe{rt_process_owned_interactive_v1_start_value(command.as_ptr(),command.len() as u64,argv,d[2]as i64,d[3]as i64,input_cap,262144,262144)};
   for text in owned{rt_string_free(text);}rt_array_free(argv);take_receipt(result)
  }
  fn write(handle:i64,data:&[u8],offset:i64,max:i64,expected:u64,d:[u64;8])->driver::Receipt{
   let bytes=rt_byte_array_new_len(data.len() as u64);assert!(!bytes.is_nil());let p=bytes.as_heap_ptr().cast::<RuntimeArray>();
   unsafe{core::ptr::copy_nonoverlapping(data.as_ptr(),(*p).data.cast::<u8>(),data.len());}
   let result=rt_process_owned_interactive_v1_write_some_value(handle,bytes,offset,max,expected as i64,d[2]as i64,d[3]as i64);rt_array_free(bytes);take_receipt(result)
  }
  fn poll(handle:i64,d:[u64;8],wait:i64,out:i64,err:i64)->driver::Poll{
   let tuple=rt_process_owned_interactive_v1_poll_value(handle,d[2]as i64,d[3]as i64,wait,out,err);assert_eq!(rt_tuple_len(tuple),3);
   let a=rt_tuple_get(tuple,0);let b=rt_tuple_get(tuple,1);let c=rt_tuple_get(tuple,2);
   let stdout=take_bytes(a);let stderr=take_bytes(b);let receipt=take_receipt(c);rt_tuple_free(tuple);driver::Poll{stdout,stderr,receipt}
  }
  fn close(h:i64,d:[u64;8])->driver::Receipt{take_receipt(rt_process_owned_interactive_v1_close_stdin_value(h,d[2]as i64,d[3]as i64))}
  fn cancel(h:i64,d:[u64;8])->driver::Receipt{take_receipt(rt_process_owned_interactive_v1_cancel_value(h,d[2]as i64,d[3]as i64))}
  fn collect(h:i64,d:[u64;8],discard:bool)->driver::Receipt{take_receipt(rt_process_owned_interactive_v1_collect_value(h,d[2]as i64,d[3]as i64,discard))}
  fn release(h:i64)->driver::Receipt{take_receipt(rt_process_owned_interactive_v1_release_value(h))}
 }
 #[test]fn interactive_native_availability_and_clock(){driver::availability_and_clock::<Native>();}
 #[test]fn interactive_native_invalid_ranges_and_stale(){driver::invalid_ranges_and_stale::<Native>();}
 #[test]fn interactive_native_expired_start_is_unowned(){driver::expired_start_is_unowned::<Native>();}
 #[test]fn interactive_native_wrong_clock_is_unowned(){driver::wrong_clock_is_unowned::<Native>();}
 #[test]#[ignore="requires hash-pinned shared C peer and bounded qualification runner"]
 fn interactive_native_persistent_raw_exchange(){driver::persistent_exchange::<Native>();}
 #[test]#[ignore="requires hash-pinned shared C peer and bounded qualification runner"]
 fn interactive_native_cancel_collects_real_owner(){driver::cancel_collects_real_owner::<Native>();}
 #[test]fn interactive_native_full_word_receipt_and_private_tickets(){
  let mut receipt=zero_receipt();receipt.accepted_total=u64::MAX;receipt.exit_value=i64::MIN;receipt.ticket0=17;receipt.ticket3=u64::MAX;
  let words=receipt_words(&receipt);assert_eq!(&words[28..],&[0,0,0,0]);let mut out=Words::new(32).unwrap();out.fill(&words);
  unsafe{assert_eq!(*out.data.add(14),u64::MAX);assert_eq!(*out.data.add(10),i64::MIN as u64);}
 }
}
