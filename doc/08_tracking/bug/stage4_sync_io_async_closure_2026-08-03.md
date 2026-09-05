# Native Stage 4 sync I/O facade pulled the unsupported async Future graph

Status: repair pending exact x86 Phase 4 verification

The full CLI reaches `std.io` for synchronous file, environment, process, and
time helpers. The `nogc_sync_mut/io.spl` facade also imported and re-exported
the entire async I/O family unconditionally. Phase 1 scanned those raw imports,
so native entry-closure discovery loaded `Future<T>` even though no CLI path
used async I/O. Native HIR correctly rejects generic classes and generic-owner
methods until monomorphization exists.

Two closure defects combined here. The driver resolved unqualified `std.*`
modules by searching the no-GC async family before the documented no-GC sync
default, so `std.io` selected the async facade. It also scanned conditionally
disabled imports as raw text. The repair restores no-GC sync precedence, makes
entry-closure import extraction run the canonical conditional preprocessor,
and marks the seven async-only sync-facade edges as interpreter-only. Direct
native `Future<T>` use remains a negative contract; this fix does not weaken
generic HIR gates or claim native async support.

Regression evidence consists of a cfg-aware closure-scanner unit, a small
native sync-I/O facade fixture, the exact full x86 Stage 4 build, and the final
candidate essential-tools smoke.
