# Native integer-sentinel mutex callers lack payload evidence

The canonical full CLI build using admitted compiler
`c978ab12656b7bf67d4bf9b6cc6450d08181c9140b19266863e93b3eba57e5f4`
reported E-MONO-032 for 37 calls to generic `mutex_lock<T>`. An integer mutex
handle does not retain its payload type, and these callers discard the returned
value, so argument or result context cannot identify `T`.

The affected owners initialize their mutexes with zero and unlock them with
zero. They now use the existing `mutex_lock_gate`, which explicitly acquires
the i64 payload. This changes only the imported name and call name: nine calls
in NVFS operation leases, sixteen in NVFS device identity, ten in native GPU
sessions, and two in font rendering. Critical sections, lazy initialization,
freestanding branches, failure handling, and unlocks are unchanged.

## Native evidence

The existing fixture `test/fixtures/compiler/native_mutex_integer_gate/main.spl`
was compiled and executed with the admitted compiler and its bound runtime.
It acquires an actual mutex, verifies its zero payload, unlocks it, then repeats
the acquisition and zero-value check. Build exit status and process exit status
were both zero. The executable SHA256 is
`0277f79b73cc6e271daa5db8b518613960e1266d8d90f9353cc67586499a3394`.

Retained evidence directory:
`D:/dev/simple-mono-caller-evidence-20261030/probe-mutex-01`.
The probe used source base `464f598bf0fd6fe37226da71f07191a06265c15c`, one
compiler worker, and a 4 GiB process-tree RSS cap. Its compiler and runtime
bindings, build log, phase records, executable, and process statuses are
retained there. The 37 caller edits were independently source-reviewed against
their initialization and unlock contracts.

This qualifies the shared gate's native behavior. It does not claim execution
of all 37 caller paths, a successful full CLI build, or a full compiler/library
suite pass. Other full CLI inference failures remain separate work.
