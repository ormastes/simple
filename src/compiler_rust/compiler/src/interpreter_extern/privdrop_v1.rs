//! Interpreter lane for `rt_privcred_*_v1` / `rt_privspawn_*_v1`: delegates to
//! the one Rust implementation in `simple_runtime::value::sffi::privdrop_v1`,
//! so the interpreter and the compiled Rust lane cannot diverge.
//! A malformed argument yields the runtime's own INVALID code, never 0
//! (0 means success in this ABI).

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::value::sffi::privdrop_v1 as rt;

const INVALID: i64 = rt::err(rt::STEP_INVALID, 22);

fn int(args: &[Value], i: usize) -> Option<i64> {
    match args.get(i) {
        Some(Value::Int(n)) => Some(*n),
        _ => None,
    }
}

fn text(args: &[Value], i: usize) -> Option<String> {
    match args.get(i) {
        Some(Value::Str(s)) => Some(s.as_ref().clone()),
        _ => None,
    }
}

macro_rules! ok {
    ($e:expr) => {
        Ok(Value::Int($e))
    };
}

pub fn rt_privcred_new_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), int(a, 1)) {
        (Some(u), Some(g)) => rt::rt_privcred_new_v1(u, g),
        _ => INVALID,
    })
}

pub fn rt_privcred_from_user_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match text(a, 0) {
        Some(n) => unsafe { rt::rt_privcred_from_user_v1(n.as_ptr(), n.len() as u64) },
        None => INVALID,
    })
}

pub fn rt_privcred_add_group_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), int(a, 1)) {
        (Some(c), Some(g)) => unsafe { rt::rt_privcred_add_group_v1(c, g) },
        _ => INVALID,
    })
}

macro_rules! unary {
    ($name:ident) => {
        pub fn $name(a: &[Value]) -> Result<Value, CompileError> {
            ok!(match int(a, 0) {
                Some(h) => unsafe { rt::$name(h) },
                None => INVALID,
            })
        }
    };
}

unary!(rt_privcred_uid_v1);
unary!(rt_privcred_gid_v1);
unary!(rt_privcred_group_count_v1);
unary!(rt_privcred_drop_self_v1);
unary!(rt_privcred_free_v1);
unary!(rt_privspawn_new_session_v1);
unary!(rt_privspawn_run_v1);
unary!(rt_privspawn_free_v1);

pub fn rt_privspawn_wait_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match int(a, 0) {
        Some(p) => rt::rt_privspawn_wait_v1(p),
        None => INVALID,
    })
}

pub fn rt_privcred_group_at_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), int(a, 1)) {
        (Some(c), Some(i)) => unsafe { rt::rt_privcred_group_at_v1(c, i) },
        _ => INVALID,
    })
}

pub fn rt_privspawn_new_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match text(a, 0) {
        Some(p) => unsafe { rt::rt_privspawn_new_v1(p.as_ptr(), p.len() as u64) },
        None => INVALID,
    })
}

pub fn rt_privspawn_arg_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), text(a, 1)) {
        (Some(s), Some(t)) => unsafe { rt::rt_privspawn_arg_v1(s, t.as_ptr(), t.len() as u64) },
        _ => INVALID,
    })
}

pub fn rt_privspawn_env_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), text(a, 1)) {
        (Some(s), Some(t)) => unsafe { rt::rt_privspawn_env_v1(s, t.as_ptr(), t.len() as u64) },
        _ => INVALID,
    })
}

pub fn rt_privspawn_cred_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), int(a, 1)) {
        (Some(s), Some(c)) => unsafe { rt::rt_privspawn_cred_v1(s, c) },
        _ => INVALID,
    })
}

pub fn rt_privspawn_join_procs_v1(a: &[Value]) -> Result<Value, CompileError> {
    ok!(match (int(a, 0), int(a, 1), text(a, 2)) {
        (Some(s), Some(fd), Some(t)) => unsafe { rt::rt_privspawn_join_procs_v1(s, fd, t.as_ptr(), t.len() as u64) },
        _ => INVALID,
    })
}
