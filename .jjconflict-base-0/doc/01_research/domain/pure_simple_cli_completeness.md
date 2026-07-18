<!-- codex-research -->
# Pure-Simple CLI completeness: domain research

Rust documents `std::env::current_exe` as platform-dependent and fallible, so
it is unsuitable as a new cross-runtime string ABI shortcut when compatible
argv primitives already exist:
https://doc.rust-lang.org/std/env/fn.current_exe.html

Rust's reference guarantees `repr(transparent)` only for the wrapper's own ABI;
it does not make two different heap string layouts interchangeable:
https://doc.rust-lang.org/reference/type-layout.html#the-transparent-representation

Therefore executable identity stays on the established scalar argv ABI and
all text-returning runtime calls must use the compiled Simple string contract.
