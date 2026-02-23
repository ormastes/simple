# Runtime Parser Bugs - Fix Implementation

**Date:** 2026-02-11
**Status:** Fix implemented, requires runtime rebuild

## BUG-RT-001: Slice Syntax [:variable] Fix

### Problem
`s[:variable]` was failing with error: `cannot index string with type 'symbol'`

The issue was that `EXPR_SLICE` was not handled in the interpreter's expression evaluator.

### Fix Implemented

**File:** `src/compiler_core/interpreter/eval.spl`

1. **Added EXPR_SLICE dispatch** (line ~131):
```simple
if tag == EXPR_SLICE: return eval_slice_expr(eid)
```

2. **Implemented eval_slice_expr function** (after eval_index_expr):
```simple
fn eval_slice_expr(eid: i64) -> i64:
    """Evaluate slice expression: base[start:end]

    Handles string and array slicing with support for:
    - [:end] - slice from start (start=0)
    - [start:] - slice to end (end=-1 means len)
    - [start:end] - explicit range
    """
    val e_node = expr_get(eid)
    val base_eid = e_node.left
    val start_eid = e_node.right
    val end_eid = e_node.extra

    val base_val = eval_expr(base_eid)
    if eval_had_error: return -1
    val start_val = eval_expr(start_eid)
    if eval_had_error: return -1
    val end_val = eval_expr(end_eid)
    if eval_had_error: return -1

    if val_is_text(base_val):
        val s = val_get_text(base_val)
        val slen = s.len()

        var start_idx = 0
        if val_is_int(start_val):
            start_idx = val_get_int(start_val)
            if start_idx < 0: start_idx = 0

        var end_idx = slen
        if val_is_int(end_val):
            end_idx = val_get_int(end_val)
            if end_idx < 0: end_idx = slen
            if end_idx > slen: end_idx = slen

        if start_idx >= slen: return val_make_text("")
        if end_idx <= start_idx: return val_make_text("")

        return val_make_text(s[start_idx:end_idx])

    if val_is_array(base_val):
        val elements = val_get_array(base_val)
        val alen = elements.len()

        var start_idx = 0
        if val_is_int(start_val):
            start_idx = val_get_int(start_val)
            if start_idx < 0: start_idx = 0

        var end_idx = alen
        if val_is_int(end_val):
            end_idx = val_get_int(end_val)
            if end_idx < 0: end_idx = alen
            if end_idx > alen: end_idx = alen

        var result: [i64] = []
        if start_idx < alen and end_idx > start_idx:
            for i in start_idx..end_idx:
                result.push(elements[i])

        return val_make_array(result)

    eval_set_error("cannot slice " + val_kind_name(val_get_kind(base_val)))
    -1
```

### Status

- ✅ Code changes implemented in `src/compiler_core/interpreter/eval.spl`
- ✅ Build succeeds with changes
- ⏸️ **Requires runtime rebuild** to take effect
- The current `bin/simple` is a pre-built Rust binary
- Changes to Simple interpreter code require rebuilding the runtime

### Testing

Once runtime is rebuilt, test with:
```bash
bin/simple -c 'val s = "hello world"; val end = 5; val result = s[:end]; print result'
# Expected output: "hello"

bin/simple -c 'val arr = [1,2,3,4,5]; val end = 3; val result = arr[:end]; print result'
# Expected output: [1, 2, 3]
```

### Next Steps

1. Rebuild runtime with: `scripts/build-bootstrap.sh` or equivalent
2. Run tests: `bin/simple test test/unit/std/runtime_parser_bugs_spec.spl`
3. Verify fix resolves BUG-RT-001

## Other Runtime Bugs

The following bugs also exist and have workarounds documented in `test/unit/std/runtime_parser_bugs_spec.spl`:

- **BUG-RT-002**: Dict.get() returns raw value not Option<T>
- **BUG-RT-003**: 'feature' is reserved word
- **BUG-RT-004**: 'class' is reserved word
- **BUG-RT-005**: static val not supported
- **BUG-RT-006**: val field defaults not supported
- **BUG-RT-007**: empty class body fails
- **BUG-RT-008**: named params in fn types fail
- **BUG-RT-009**: cannot call fn fields directly

These are bootstrap runtime limitations that require C/Rust-level fixes or parser changes.
