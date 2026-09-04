//! Execution proof for `simple_common::platform::path::to_native_arg`.
//!
//! Spawns the real `clang-cl` twice: once with the canonical internal
//! MinGW/MSYS path form (`/d/.../x.c`) and once with the same path put
//! through the single conversion home. Prints both exit codes and the size
//! of any object produced.
//!
//! Spawned from Rust via `CreateProcess`, so MSYS2's shell-level argument
//! mangling is not in play — this is the same path the compiler driver takes.
//!
//! Run with:
//!   cargo run -p simple-common --example clang_cl_path_proof -- <dir>
//!
//! Expected on Windows: unconverted rc=1, converted rc=0 with an object file.
//! On Unix the conversion is the identity and both runs are the same run;
//! the example reports that rather than pretending to prove anything.

use simple_common::platform::path::to_native_arg;
use std::process::Command;

fn run(cc: &str, src: &str, obj: &str) -> i32 {
    let out = Command::new(cc)
        .args(["/c", src, &format!("/Fo{obj}")])
        .output();
    match out {
        Ok(o) => {
            let rc = o.status.code().unwrap_or(-1);
            let err = String::from_utf8_lossy(&o.stderr);
            let first = err.lines().next().unwrap_or("").trim();
            println!("      rc={rc}  stderr[0]={first}");
            rc
        }
        Err(e) => {
            println!("      spawn failed: {e}");
            -1
        }
    }
}

fn obj_size(p: &str) -> String {
    match std::fs::metadata(p) {
        Ok(m) => format!("{} bytes", m.len()),
        Err(_) => "absent".to_string(),
    }
}

fn main() {
    let dir = std::env::args().nth(1).unwrap_or_else(|| "/d/tmp/pathproof".to_string());
    let cc = std::env::var("PROOF_CC").unwrap_or_else(|_| "clang-cl".to_string());

    // Canonical internal form: MinGW/MSYS style, forward slashes.
    let msys_src = format!("{dir}/x.c");
    let msys_obj_a = format!("{dir}/out_unconverted.obj");
    let msys_obj_b = format!("{dir}/out_converted.obj");

    let _ = std::fs::remove_file(&msys_obj_a);
    let _ = std::fs::remove_file(&msys_obj_b);

    println!("compiler        : {cc}");
    println!("canonical source: {msys_src}");
    println!();

    println!("[A] UNCONVERTED — canonical MSYS form handed straight to the tool");
    let rc_a = run(&cc, &msys_src, &msys_obj_a);
    println!("      object: {}", obj_size(&msys_obj_a));
    println!();

    let nat_src = to_native_arg(&msys_src).into_owned();
    let nat_obj = to_native_arg(&msys_obj_b).into_owned();
    println!("[B] CONVERTED via to_native_arg");
    println!("      {msys_src}  ->  {nat_src}");
    let rc_b = run(&cc, &nat_src, &nat_obj);
    // Stat the CONVERTED path: std::fs (Win32) cannot resolve the MSYS form
    // either, so statting `msys_obj_b` would report "absent" for a file that
    // exists. That is itself part of the hazard this conversion closes.
    println!("      object: {}", obj_size(&nat_obj));
    println!();

    if cfg!(windows) {
        println!("VERDICT: unconverted rc={rc_a}, converted rc={rc_b}");
        assert_ne!(rc_a, 0, "expected the unconverted MSYS form to be REJECTED");
        assert_eq!(rc_b, 0, "expected the converted native form to be ACCEPTED");
        assert!(
            std::fs::metadata(&nat_obj).map(|m| m.len() > 0).unwrap_or(false),
            "converted run must produce a non-empty object"
        );
        println!("PROOF OK: rc=1 before conversion, rc=0 + real object after.");
    } else {
        println!(
            "VERDICT: non-Windows host. to_native_arg is the identity here, so [A] and [B] \
             are the same invocation (rc={rc_a} / rc={rc_b}). Nothing is proven about \
             Windows conversion from this host."
        );
    }
}
