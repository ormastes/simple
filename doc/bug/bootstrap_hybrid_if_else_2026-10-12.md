# Unsupported hybrid multiline if-expression blocks Phase2

Status: source formatting repair authored; execution pending. Compact hybrid grammar remains unsupported.

Frozen source `62d306cf0eee92107abf1649e496979f71625748` failed actual Phase2 discovery at `src/compiler/80.driver/cache/driver_hir_archive_journal_v1.spl:145:83`: unexpected token, expected expression, found Else. The same form also occurs in `hir_mono_archive_consumer_v1.spl:232`.

Minimal unsupported form (preserved as a grammar reproducer, not normalized away):

```simple
val result = if ready:
    Ok(1) else: Err("not ready")
```

Both Rust parse_if_expr and Simple parse_block require Dedent before the multiline arm's Else. The documented supported forms are wholly inline or aligned multiline. Supporting this compact hybrid is an open language/parser request; this repair does not implement it.

The two production declarations now use aligned multiline Else, retaining identical conditions, selected expressions, and all surrounding ownership/lease operations. No runtime or Rust changes are needed for this source repair.

`test/fixtures/compiler/bootstrap_multiline_result_if.spl` covers six real Result outcomes with twelve checks: empty binding, empty digest, retained tuple fields, absent input with lazy refusal (true-arm unwrap must not execute), successful selected load, and selected-load error propagation. Expected exit0 and exact marker `BOOTSTRAP_MULTILINE_RESULT_IF_PASS cases=6 checks=12`. These are syntax/value regressions, not whole archive/lease qualification. AUTHORED_UNEXECUTED.

A finite frozen compiler scan covered 2333 files and identified these two exact hybrids; this was not a whole-source parser PASS. No supported seed parser-only CLI was found. Seed `check` dispatches the pure-Simple tool and is not a reliable Rust-parser census; any seed diagnostic is bootstrap-only, never replacement project tooling.
