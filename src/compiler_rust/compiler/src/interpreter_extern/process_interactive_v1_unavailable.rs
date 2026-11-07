//! 32-bit explicit Unavailable, not a functional capability or positive gate.
use crate::error::CompileError;
use crate::value::Value;
fn count(args:&[Value],expected:usize)->Result<(),CompileError>{
    if args.len()==expected{Ok(())}else{Err(CompileError::runtime("interactive v1: wrong argument count"))}
}
fn receipt()->Value{let mut words=vec![Value::Int(0);32];words[0]=Value::Int(1);words[1]=Value::Int(256);words[2]=Value::Int(7);Value::array(words)}
pub fn capabilities(args:&[Value])->Result<Value,CompileError>{count(args,0)?;let mut words=vec![Value::Int(0);16];words[0]=Value::Int(1);words[1]=Value::Int(128);words[2]=Value::Int(7);Ok(Value::array(words))}
pub fn deadline(args:&[Value])->Result<Value,CompileError>{count(args,1)?;Ok(Value::array(vec![Value::Int(1),Value::Int(32),Value::Int(0),Value::Int(0),Value::Int(7),Value::Int(0),Value::Int(0),Value::Int(0)]))}
pub fn start(args:&[Value])->Result<Value,CompileError>{count(args,7)?;Ok(receipt())}
pub fn write_some(args:&[Value])->Result<Value,CompileError>{count(args,7)?;Ok(receipt())}
pub fn poll(args:&[Value])->Result<Value,CompileError>{count(args,6)?;Ok(Value::Tuple(vec![Value::byte_array(Vec::new()),Value::byte_array(Vec::new()),receipt()]))}
pub fn close_stdin(args:&[Value])->Result<Value,CompileError>{count(args,3)?;Ok(receipt())}
pub fn cancel(args:&[Value])->Result<Value,CompileError>{count(args,3)?;Ok(receipt())}
pub fn collect(args:&[Value])->Result<Value,CompileError>{count(args,4)?;Ok(receipt())}
pub fn release(args:&[Value])->Result<Value,CompileError>{count(args,1)?;Ok(receipt())}

#[cfg(test)]mod unavailable_tests{
 use super::*;
 #[test]fn interactive_32bit_is_explicitly_unavailable(){
  let c=capabilities(&[]).unwrap();let data=match c{Value::Array(data)=>data,_=>panic!("missing availability words")};
  assert!(matches!(data.get_value(2),Some(Value::Int(7))));assert!(matches!(data.get_value(3),Some(Value::Int(0))));
  let args=vec![Value::Int(123),Value::Int(1),Value::Int(999),Value::Int(0),Value::Int(64),Value::Int(64)];
  match poll(&args).unwrap(){Value::Tuple(fields)=>{assert_eq!(fields.len(),3);match &fields[2]{Value::Array(data)=>assert!(matches!(data.get_value(2),Some(Value::Int(7)))),_=>panic!("missing unavailable receipt")}},_=>panic!("wrong poll shape")}
 }
}
