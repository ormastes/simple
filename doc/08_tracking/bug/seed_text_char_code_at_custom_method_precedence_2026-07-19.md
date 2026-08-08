# Seed text char_code_at custom-method precedence

Status: open bootstrap-only parity bug.

The Rust seed lowers a string receiver's `char_code_at` builtin before dynamic
or custom method dispatch. A user-defined `impl text` method with the same name
is therefore bypassed. Pure Simple performs resolved custom-owner dispatch
first and only uses the runtime builtin for the unresolved known-text case.

Reproduction: define an `impl text` `char_code_at(index)` that returns a fixed
sentinel, call it on a text value, and compare seed versus pure MIR/native
behavior. Acceptance: both paths invoke the custom method, while ordinary text
without that method still uses the raw-i64 runtime ABI and passes the existing
literal/tagged/Unicode/bounds/cast fixture.
