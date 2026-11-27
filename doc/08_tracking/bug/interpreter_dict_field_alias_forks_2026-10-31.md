# Interpreter dict stored in two places forks on first write (2026-10-31)

Status: OPEN for the interpreter; worked around for `SymbolTable` only.

## Defect
Interpreter dicts are `Arc<HashMap>` with copy-on-write. A dict stored in two
fields is one object on the compiled lanes and two after the first write here:

```
var r: Dict<text,i64> = {}
var s: Dict<i64,Sc> = {}
s[0] = Sc(symbols: r)
var t = T(root: r, scopes: s)
t.put()                        # self.scopes[0].symbols["a"] = 1
# interpreter: t.root.len() == 0, t.scopes[0].symbols.len() == 1
```

`SymbolTable.new` relies on that aliasing (`root_scope_symbols` and
`scopes[0].symbols`), so `verification_source_environment_v1`
(`src/compiler/50.mir/verification_source_environment_v1.spl:44`) failed with
"source root lexical mirror is inconsistent" on the seed.

A real fix needs handle semantics for interpreter dicts, which is not a narrow
change. `SymbolTable.bind_in_current_scope` writes both dicts instead, a repeated
store where they are shared. Other aliased dicts remain affected.

## Still red after this: lean_enum_elimination specs
`test/03_system/compiler/lean_enum_elimination_spec.spl` and its
`compiler_lean_enum_elimination_spec` twin measured 35 failed of 35 before and
34 failed of 35 after. Next layer:
"EE-E-METADATA: source lowering failed: non-exhaustive enum match on 'Flag'".

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:5175-5211`
reports that through `self.error` for every match with no default arm, even when
the arms cover every variant ("Arms are textually exhaustive"), and the spec
helper treats any lowering error as failure. The report is unconditional in the
source, so no seed defect is implicated at this check, but no lane has been shown
to pass these specs: `test_db.sdn` lists them without a usable outcome. So the
"blocked only by Dict keys" triage is not confirmed. Whether exhaustive matches
should report, or the helper should ignore this class, is an owner decision. Other messages seen in the same run:
`serialize_mir_module` not found, "nullary variant carries a payload",
"lean-nominal-body: requires a known nonvariadic signature". None are triaged.
