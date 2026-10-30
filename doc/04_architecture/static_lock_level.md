# Static lock-level checking

Status: design for a bounded compiler foundation; REQ-MC-006 remains partial.

The selected requirement is the synchronization clause in
`doc/02_requirements/language/mission_critical_profile.md`, refined by item 10
of `doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`:
`@lock_level(n)` must reject acquisition below a held level unless a reviewed
exception authorizes it. Runtime TSan observations do not satisfy this static
requirement. The implementation targets `release_phase3` at `f5c0f468556`.

## Foundation boundary

The first supported annotation placement is a named synchronous function.
It declares a ranked acquisition scope: entering the function enters that
rank and returning leaves it. This is an explicit lock-effect contract. It
does not discover physical mutex acquisition or establish a guard lifetime.
Methods may be accepted only when their declaration identity is resolved;
ambiguous receiver dispatch is an unsupported boundary.

The checker validates calls within these scopes, including calls through
unannotated local wrappers. It rejects a callee rank below the active maximum.
Equal ranks follow the selected lower-after-higher rule and are not rejected
merely for equality. Consequently this contract does not prove the absence of
deadlocks between distinct equal-ranked locks. Recursive ranked call cycles
are rejected conservatively when their acquisition behavior cannot be proved.

Raw mutex APIs, dynamic dispatch, imported functions without trusted effects,
and escaping callbacks cannot silently become zero-effect operations. In a
checked scope they fail closed until a resolver or a supported acquisition
contract supplies the necessary proof. Unannotated code is not certified by
the presence of this checker elsewhere in the module.

## Compiler ownership

Existing generic attribute syntax owns parsing. The parser retains exact
annotation arguments and declaration identity; the checker owns validation
and call-effect analysis. No new token or grammar form is introduced. Do not
reuse permissive decorator digit extraction: malformed values must fail.

Use one arena-AST checker shared by the native FlatAstBridge and interpreter.
Run it after parsing and before execution or lowering. Cached AST restoration
must provide the same annotation facts and invoke the same check. Persisted
metadata requires cache versioning; otherwise annotated sources must bypass
that cache. A cache hit never serves as proof that an old compiler performed
the current check. Parser resets and transient-owner promotion must include
any new annotation state.

The checker identifies declarations structurally, not by method basename.
Binding shadowing, aliases and unsupported indirect calls must not select a
convenient unrelated annotated function. Traversal must terminate on cycles
and must bound work or memoize effects rather than recursively expanding an
exponential number of paths. A budget exhaustion is a diagnostic, not PASS.

## Physical-acquisition implementation contract

The current canonical Mutex API offers synchronous `with_lock` callbacks;
manual `lock`/`try_lock` returns a protected value rather than an RAII guard.
The second implementation step in this task annotates immutable module-level
Mutex resources using existing declaration attributes and resolves
`Mutex.with_lock`, `mutex_with_lock`, and `mutex_with_lock_keeping` from the
canonical library owner. The async-tier compatibility re-export remains a
synchronous API. Symbol identity and the resource's constructor/type must be
proved; matching a method or function basename is insufficient.

Evaluate the receiver and ordinary arguments in the current context. Enter the
resource rank only for the inline callback body; restore the previous held set
on exit. Reject descending rank and same-resource recursive acquisition.
Distinct equal-ranked resources retain the selected equality policy. Reject
unresolved/imported resources, mutable or escaping aliases, callback references,
and suspension until their effects are represented. Sequential callbacks must
not retain the preceding callback's rank.

Manual `lock`/`try_lock`/`unlock` requires path-sensitive successful-acquire and
release state, branch joins and loop handling. In this task it is an explicit
unsupported diagnostic within the claimed checked boundary, not an unchecked
success. Imported effect metadata and reviewed exception manifests likewise
fail closed until implemented. These restrictions are actionable: use a proved
immutable resource with an inline synchronous `with_lock` callback.

REQ-MC-006 cannot be marked complete from function-scope tests. Acceptance
requires actual acquisition/release/lifetime coverage or a documented rejection
of every unsupported case in the claimed checked-program boundary.
