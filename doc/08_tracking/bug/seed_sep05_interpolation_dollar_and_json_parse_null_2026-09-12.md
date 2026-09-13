# Sep-5 seed: `"${x}"` emits a stray `$`, and `json_parse` returns null for an object

Status: OPEN. Found 2026-09-12 while building the RenderDoc capture diff
(`src/app/ui/renderdoc_diff/`). Two independent defects in the same binary; both were
worked around rather than left silent, per CLAUDE.md's rule against normalizing a
workaround without recording the defect.

Binary: `/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple`,
`-r-x------ 130402384 Sep 5 20:01`. Host macOS (darwin 25.5.0, aarch64). This is the
only Simple binary present on this machine, so neither defect could be checked against
a second build; both need re-verification on a rebuilt seed before anyone concludes
they are still live.

## 1. String interpolation prepends a literal `$`

```
fn main():
    val n = 5
    print("interp=${n}")          # prints  interp=$5      expected  interp=5
    print("n=" + n.to_text())     # prints  n=5            correct
```

Every interpolated value is rendered with a leading `$`. Concatenation is unaffected.
This is not cosmetic for anything that produces machine-read output: a verdict line or a
`key=value` status built with interpolation carries junk a caller's `cut -d= -f2` picks
up.

Workaround in use: every output string in `src/app/ui/renderdoc_diff/` is built with `+`
concatenation, never interpolation. Recorded in
`doc/07_guide/app/ui/renderdoc_web_diff.md`.

## 2. `std.json.json_parse` returns null for a plain object

```
use std.json.{json_parse, json_get_type, json_object_get}

fn main():
    val root = json_parse("{\"schema\":\"v1\",\"events\":[{\"eventId\":3}]}")
    print("type=" + json_get_type(root))    # prints  type=$null
```

`json_get_type` reports `null` and every `json_object_get` on the result is `None`, so
the whole `common/json` reader surface is unusable on this binary. The import itself
resolves (running the script from OUTSIDE the repo instead fails earlier, with
`stdlib import 'std.json' resolves from the project stdlib roots only` — a different and
correct message; the probe above was run from the repo root).

Workaround in use: `src/app/ui/renderdoc_diff/jsonflat.spl`, a recursion-free scanner
that flattens the document to `(path, value)` pairs. It is ~130 lines and is covered by
the lane's spec, so it is not dead weight — but it exists only because the stdlib reader
does not work here, and should be reconsidered once the seed is rebuilt.

## Unblock

Rebuild the seed and re-run both probes. If either reproduces, the defect is in current
source and needs a real fix; if neither does, close this and delete the workaround note
in the guide (the flat reader can stay or go on its own merits).
