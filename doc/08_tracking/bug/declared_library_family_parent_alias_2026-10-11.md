# Declared library roots bind SHA3 imports to the parent crypto facade

The C33 normal runner build visits 223 HIR modules; its terminal ledger
records 222 successful modules and one failed module, HMAC. It reports
missing `std.crypto.sha3` exports `sha3_256_bytes`, `sha3_384_bytes` and
`sha3_512_bytes`, followed by unresolved calls. The failure gate blocks the
final compiler worker, MIR, objects and linking. Actual test cases: zero.

Source HEAD: `a9646f08c4b3f58712a0b8d6e752c211ebe061dd`.
Diagnostic producer SHA256:
`f993254fccf459616d227ffe8bb62ccd6dd18ca4992edf30e7d0c4f25fef14bd`.
No canonical Stage2 or tool admission is claimed.

Evidence is retained in the `simple-bootstrap-c06-20261011` worktree under
`build/native_probe/phase3-whole-20261011-c06/c33-producer-c33-runner/`.
The bounded, same-source/producer/cache GDB replay is `gdb-sha3-attempt1/`;
`indexed-provider-capture.json` contains the decoded surface and return
values. Source/runtime postguards passed. Normal build peak tree RSS was
2338108 KiB under the enforced 6835937 KiB cap. The first GDB disk preflight
failed before compilation and was retained; replay began after space was
restored. GDB itself exited normally, the actual compiler failed, and the
launcher returned 117 because no executable was produced.

The SHA3 source and encoded HIR contain all three functions. GDB at
`HirLowering.surface_declares_item_indexed` instead shows:

- selected physical index: 195;
- selected source: the frozen `src/lib/crypto.spl`;
- module/logical name: `lib.crypto`;
- indexed callable names: empty;
- all three requested SHA3 names return false; no crash signal.

The declared-root driver resolver tries `std.crypto.sha3` directly under
`src/lib`, then shortens it to `std.crypto` and selects `crypto.spl`. Unlike
the canonical native closure resolver, it omits the flattened library-family
lookup before shortening. Source loading then registers the parent file as
the exact `std.crypto.sha3` alias, which correctly takes precedence over
later HIR fallback lookup of `lib.common.crypto.sha3`.

Repair the source resolver, leaving cryptographic code and import checking
unchanged. All exact declared roots retain priority. Then search the first
declared library root using the canonical native closure's existing six-family
order, now shared by a common helper. Only after that pass may terminal item
fallback shorten the path. Found/Ambiguous/Missing remain distinct; ambiguity
terminates resolution. The older generic fallback's separate order is not
changed by this repair.

Regressions check the real selected SHA3 path and its indexed callable names,
a family module beside a parent facade, a later exact overlay ahead of family
fallback, legitimate item suffixes, and ambiguous numbered family owners.
They are written but unexecuted until a functioning pure-Simple runner is
available. A rebuilt producer and normal runner qualification remain required.
