# Cranelift indirect calls reject imported direct-function records

Status: isolated source fix and real native regression prepared; execution pending.

After the qualified-alias correction, Linux's three-module alias fixture
compiled and linked with all three modules present, then exited 139. The
retained executable calls the correct owner__normalize directly, but its
function-value call goes through a null pointer. Evidence is retained under
/root/linux-bootstrap-ext4/spawn-abi-9e89-run1/alias-native-probe, including
build.log, gdb.log and probe. The producer SHA-256 is
11bfc82adceebfad58a6d300c2279401919f882ea292e78fc31beab0d0639a90.

GlobalLoad emits an imported user function as a raw two-word record containing
the native entry and SDIRECTF marker. Cranelift's indirect call instead always
requests a registered closure entry and supplies a hidden environment plus
boxed RuntimeValue arguments. The core-C helper correctly returns zero for
the raw record. Merely widening that runtime helper would still call the
target with the wrong argument ABI.

The correction preserves registered closures and their boxed entries. A
separate guarded branch recognizes the existing direct-function record and
uses the uniform raw-I64 user signature from build_mir_signature: no hidden
environment, float bits transported as words, and an I64 result even for a
function without an explicit return. The record remains borrowed with its
existing allocator ownership. Tagged values and low or negative immediates
are rejected before any raw marker read; a marked record with a null entry
traps instead of calling address zero. As with other native function values,
a positive aligned raw callable must point to a valid compiler-owned record.

The original colliding_native_owner fixture must print 42 twice. The added
cranelift_callable_abi fixture exercises imported integer, f32, f64, bool,
signed narrow integer, zero-argument and void functions, function-value
parameter/return transport, and both capturing and noncapturing closures.
Expected stdout is six lines of 42, two lines of -42, three lines of 42, then 71.
The second -42 passes an actual narrow indirect result into another indirect
call, exercising signed widening rather than only a full-width literal.

This change does not widen the C closure registry or claim support for raw
runtime/SFFI function-value records with exceptional native signatures. Such
records do not carry signature metadata and need a distinct typed adapter.
Array/global callback transport and arbitrary invalid foreign pointers are
not claimed as covered by the focused fixture.
