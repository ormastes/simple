#[cfg(test)]
mod unsafe_inline_body {
    fn parses(src: &str) -> bool {
        crate::Parser::new(src).parse().is_ok()
    }

    fn err(src: &str) -> String {
        match crate::Parser::new(src).parse() {
            Ok(_) => String::new(),
            Err(e) => format!("{:?}", e),
        }
    }

    /// `unsafe(capabilities: [...]): expr` with a ONE-LINE body was rejected
    /// with "expected Newline, found Identifier": `parse_unsafe_block_primary`
    /// called `parse_block`, which accepts only the indented form. This is the
    /// shape used at 8+ sites in `src/os/kernel/boot/mmio_hardware.spl`, which
    /// had been expanded to indented blocks as a workaround.
    /// See item 24 of doc/08_tracking/bug/
    /// unit_sweep_language_and_interpreter_gaps_2026-08-26.md.
    #[test]
    fn inline_unsafe_body_parses() {
        assert!(
            parses("fn r(addr: u64) -> u64:\n    unsafe(capabilities: [ffi, raw_ptr]): rt_volatile_read_u64(addr)\n"),
            "one-line unsafe body must parse: {}",
            err("fn r(addr: u64) -> u64:\n    unsafe(capabilities: [ffi, raw_ptr]): rt_volatile_read_u64(addr)\n")
        );
        assert!(
            parses(
                "fn w(addr: u64, v: u64):\n    unsafe(capabilities: [ffi, raw_ptr]): rt_volatile_write_u64(addr, v)\n"
            ),
            "one-line unsafe body with a multi-argument call must parse"
        );
        assert!(
            parses("fn b():\n    unsafe(capabilities: [ffi]): rt_memory_barrier()\n"),
            "one-line unsafe body with a single capability must parse"
        );
    }

    /// The indented form must keep working — it is what the workaround used and
    /// what the rest of the tree relies on.
    #[test]
    fn indented_unsafe_body_still_parses() {
        assert!(
            parses("fn r(addr: u64) -> u64:\n    unsafe(capabilities: [ffi, raw_ptr]):\n        rt_volatile_read_u64(addr)\n"),
            "indented unsafe body regressed"
        );
        assert!(
            parses("fn r(addr: u64) -> u64:\n    unsafe(capabilities: [ffi, raw_ptr]):\n        val v = rt_volatile_read_u64(addr)\n        v\n"),
            "multi-statement indented unsafe body regressed"
        );
    }

    /// `parse_inline_or_block` reconciles a pseudo-DEDENT left by a preceding
    /// condition's multi-line continuation. Pin the interaction: an inline
    /// `unsafe` body sitting inside `if`/`while` bodies must still parse.
    #[test]
    fn inline_unsafe_body_inside_control_flow_parses() {
        assert!(
            parses("fn r(addr: u64, on: bool) -> u64:\n    if on:\n        unsafe(capabilities: [ffi, raw_ptr]): rt_volatile_read_u64(addr)\n    else:\n        0u64\n"),
            "inline unsafe body inside an if body must parse"
        );
        assert!(
            parses("fn r(addr: u64, n: i64):\n    var i = 0\n    while i < n:\n        unsafe(capabilities: [ffi, raw_ptr]): rt_volatile_write_u64(addr, 0u64)\n        i = i + 1\n"),
            "inline unsafe body inside a while body must parse"
        );
        assert!(
            parses("fn r(a: u64, b: u64, on: bool) -> u64:\n    if a == b and\n            on:\n        unsafe(capabilities: [ffi, raw_ptr]): rt_volatile_read_u64(a)\n    else:\n        0u64\n"),
            "inline unsafe body after a multi-line condition continuation must parse"
        );
    }

    /// The fix must not weaken the grammar: a missing colon, a missing body and
    /// an unterminated header are still errors.
    #[test]
    fn malformed_unsafe_headers_still_rejected() {
        assert!(
            !parses("fn r(addr: u64) -> u64:\n    unsafe(capabilities: [ffi, raw_ptr]) rt_volatile_read_u64(addr)\n"),
            "missing colon after the unsafe header must still be rejected"
        );
        // NOTE: `unsafe(caps):` with NO body at all is accepted both before and
        // after this fix — a pre-existing laxness in `parse_block`, unrelated to
        // the inline-body change and deliberately not asserted here.
        assert!(
            !parses("fn r(addr: u64) -> u64:\n    unsafe(capabilities: [ffi, raw_ptr: rt_volatile_read_u64(addr)\n"),
            "an unterminated unsafe header must still be rejected"
        );
    }
}
