//! Runnable check for the `SIMPLE_LINKER` contract on the Rust seed's link
//! path (`pipeline/native_project/linker.rs`).
//!
//! WHY THIS EXISTS. The bootstrap CLI's `native-build` links through the seed
//! — `src/app/cli/bootstrap_main.spl:4` declares
//! `extern fn rt_native_build(args: [text]) -> i64` — so the Simple-side
//! linker wrapper is never entered (`SIMPLE_COMPILER_TRACE=1` emits zero
//! `[LINKER]` lines). The seed's link step read `SIMPLE_LINKER_DEBUG` but
//! never `SIMPLE_LINKER`, and passed no `-fuse-ld=` at all: strace showed a
//! bare `execve("/usr/local/bin/ld")`, which on this host is mold. mold
//! front-loads one contiguous 8 GiB virtual reservation, so under memory
//! contention the link died with
//! `mold: cannot reserve 8589934592 bytes of virtual memory`, the Stage-2
//! qualification gate reported `simple:entry-form:fail(build exited 1)`, and
//! the bootstrap died with it.
//!
//! `SIMPLE_LINKER=bogus-linker native-build ...` exited 0. That silent success
//! is the bug's signature, and assertion 1 below is exactly that signature
//! inverted.
//!
//! WHY AN INTEGRATION TEST AND NOT `#[cfg(test)] mod linker_tests`. The
//! natural home is that module, but the crate's `--lib` test target does not
//! compile at present, for three reasons that have nothing to do with the
//! linker: a duplicate `#[test]` name in `interpreter_extern/wsffi.rs:1072`,
//! `Value::as_array` missing at `interpreter_extern/mod.rs:3283`, and
//! `BTreeMap::intersection` at `native_project/tests.rs:4444`. A check that
//! cannot be run is not a check. An integration test builds the crate without
//! `cfg(test)`, so those modules are never compiled and this runs today.

use simple_compiler::pipeline::native_project::linker_alias;

/// ASSERTION 1: an unsupported `SIMPLE_LINKER` value must FAIL, loudly.
///
/// Also pins the whole alias table against `find_requested_linker` in
/// `src/compiler/70.backend/linker/mold.spl:96-119`. The two link paths must
/// accept exactly the same names, or a value that works through one silently
/// means something else through the other.
#[test]
fn unsupported_simple_linker_value_is_rejected_not_silently_ignored() {
    let err = linker_alias("bogus-linker").expect_err(
        "an unsupported SIMPLE_LINKER value must be an error; exiting 0 and \
         linking with the default linker is the bug this check exists for",
    );
    assert_eq!(err, "Unsupported SIMPLE_LINKER value: bogus-linker");

    assert_eq!(
        linker_alias("").expect_err("an empty value must not succeed"),
        "empty SIMPLE_LINKER override"
    );
    assert_eq!(
        linker_alias("   ").expect_err("a blank value must not succeed"),
        "empty SIMPLE_LINKER override"
    );
}

/// The accepted set, and nothing outside it.
///
/// `-fuse-ld=` takes a NAME, never a path, and GNU ld is spelled `bfd` — the
/// second element is the concrete program the C driver searches PATH for, so
/// probing that exact spelling is what makes "requested but not installed"
/// detectable. Probing bare `ld` would be actively wrong on a host where
/// `/usr/bin/ld` is a symlink to mold, which is this host.
#[test]
fn simple_linker_alias_table_mirrors_the_simple_side_wrapper() {
    for name in ["mold", "MOLD", " mold "] {
        assert_eq!(linker_alias(name).unwrap(), ("mold", "ld.mold"), "{name}");
    }
    for name in ["lld", "ld.lld", "lld-link", "LLD"] {
        assert_eq!(linker_alias(name).unwrap(), ("lld", "ld.lld"), "{name}");
    }
    for name in ["ld", "gnu", "bfd"] {
        assert_eq!(linker_alias(name).unwrap(), ("bfd", "ld.bfd"), "{name}");
    }
    // Not in the Simple-side table, so not accepted here either. An alias one
    // path honours and the other rejects is the disagreement this mirroring
    // exists to prevent.
    for name in ["gold", "ld.gold", "link.exe", "cc", "/usr/bin/ld.lld"] {
        assert!(linker_alias(name).is_err(), "{name} must not be accepted");
    }
}
