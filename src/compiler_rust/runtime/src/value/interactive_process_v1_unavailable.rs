//! Explicit availability projection for 32-bit hosts. The frozen raw owner ABI
//! is 64-bit only; this never calls it or claims functional process support.
use super::RuntimeValue;
use super::collections::{rt_array_new,rt_array_push,rt_array_free,rt_byte_array_new_len,rt_tuple_new,rt_tuple_set,rt_tuple_free};
const UNSUPPORTED:i64=7;
fn words(values:&[i64])->RuntimeValue{
    let out=rt_array_new(values.len() as u64);if out.is_nil(){return out;}
    for value in values{if !rt_array_push(out,RuntimeValue::from_int(*value)){rt_array_free(out);return RuntimeValue::NIL;}}
    out
}
fn receipt()->RuntimeValue{let mut values=[0i64;32];values[0]=1;values[1]=256;values[2]=UNSUPPORTED;words(&values)}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_capabilities_value()->RuntimeValue{
    let mut values=[0i64;16];values[0]=1;values[1]=128;values[2]=UNSUPPORTED;words(&values)
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_deadline_value(_:i64)->RuntimeValue{words(&[1,32,0,0,UNSUPPORTED,0,0,0])}
#[no_mangle]
pub unsafe extern "C" fn rt_process_owned_interactive_v1_start_value(_: *const u8,_:u64,_:RuntimeValue,_:i64,_:i64,_:i64,_:i64,_:i64)->RuntimeValue{receipt()}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_write_some_value(_:i64,_:RuntimeValue,_:i64,_:i64,_:i64,_:i64,_:i64)->RuntimeValue{receipt()}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_poll_value(_:i64,_:i64,_:i64,_:i64,_:i64,_:i64)->RuntimeValue{
    let r=receipt();if r.is_nil(){return r;}let out=rt_byte_array_new_len(0);if out.is_nil(){rt_array_free(r);return out;}
    let err=rt_byte_array_new_len(0);if err.is_nil(){rt_array_free(out);rt_array_free(r);return err;}
    let tuple=rt_tuple_new(3);if tuple.is_nil(){rt_array_free(err);rt_array_free(out);rt_array_free(r);return tuple;}
    if !rt_tuple_set(tuple,0,out)||!rt_tuple_set(tuple,1,err)||!rt_tuple_set(tuple,2,r){
        rt_tuple_free(tuple);rt_array_free(err);rt_array_free(out);rt_array_free(r);return RuntimeValue::NIL;
    }tuple
}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_close_stdin_value(_:i64,_:i64,_:i64)->RuntimeValue{receipt()}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_cancel_value(_:i64,_:i64,_:i64)->RuntimeValue{receipt()}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_collect_value(_:i64,_:i64,_:i64,_:bool)->RuntimeValue{receipt()}
#[no_mangle]
pub extern "C" fn rt_process_owned_interactive_v1_release_value(_:i64)->RuntimeValue{receipt()}

#[cfg(test)]mod unavailable_tests{
 use super::*;use crate::value::{rt_array_get,rt_tuple_get,rt_tuple_len};
 #[test]fn interactive_32bit_is_explicitly_unavailable(){
  let c=rt_process_owned_interactive_v1_capabilities_value();assert_eq!(rt_array_get(c,2).as_int(),7);assert_eq!(rt_array_get(c,3).as_int(),0);rt_array_free(c);
  let p=rt_process_owned_interactive_v1_poll_value(123,1,999,0,64,64);assert_eq!(rt_tuple_len(p),3);
  let a=rt_tuple_get(p,0);let b=rt_tuple_get(p,1);let r=rt_tuple_get(p,2);assert_eq!(rt_array_get(r,2).as_int(),7);assert_eq!(rt_array_get(r,3).as_int(),0);
  rt_array_free(a);rt_array_free(b);rt_array_free(r);rt_tuple_free(p);
 }
}
