# `[text].sort()` is a no-op — neither sorts in place nor returns a sorted value

- **Filed:** 2026-09-12
- Status: OPEN (2026-09-12)
- **Found by:** L5-D (generated/deployed binary closure wave), while deciding
  whether `simple check <dir>`'s emitted file ORDER could be pinned in a spec.
- **Binary:** deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`,
  and the wave binary
  `/home/yoon/dev/simple-wave/src/compiler_rust/target/release/simple`
  (sha256 `ef528c60…`) — both behave identically. Tree `c7c5bef3ca3`.

## Symptom

`sort()` on a `[text]` array does nothing at all. It does not sort in place, and
its value is the unsorted array. No error, no warning, no diagnostic.

## Reproducer

```sh
cat > /tmp/sortchk.spl <<'EOF'
fn main():
    var xs: [text] = ["c", "a", "b"]
    xs.sort()
    print "in_place={xs}"
    val ys = ["c", "a", "b"].sort()
    print "returned={ys}"
EOF
bin/release/aarch64-unknown-linux-gnu/simple run /tmp/sortchk.spl
```

Observed:

```
in_place=[c, a, b]
returned=[c, a, b]
```

Expected: `[a, b, c]` for at least one of the two forms — whichever the language
defines `sort()` to be. Today neither holds, so any caller that writes
`xs.sort()` and then reads `xs` silently gets unsorted data.

## Live caller shipping today

`src/app/io/source_discovery.spl:17`:

```
        if path.ends_with(".spl"):
            files.push(path)
    files.sort()
    files
```

That is the discovery used by `app.check.targets.expand_check_targets`, i.e. the
public `simple check <dir>` entry. Because the `sort()` does nothing, the order
`simple check <dir>` reports and processes is raw `rt_dir_walk` (readdir) order.
Two consequences, both observed:

- the order is filesystem-dependent, not lexicographic. On the mixed-depth
  fixture `test/fixtures/app/check/membership/` the emitted order is
  `a_top.spl, z_top.spl, m_zebra/inner.spl, nested/mid.spl,
  nested/deep/leaf.spl` — `z_top` second, ahead of two directories that sort
  before it;
- the order differs between a relative and an absolute spelling of the SAME
  directory, because `discover_spl_files` walks `rt_path_absolute(root)` while a
  caller walking the relative path gets a different readdir sequence. Measured:
  a spec that pinned the expansion element-wise against `rt_dir_walk(<relative
  dir>)` failed with `expected …/z_top.spl to equal …/nested/deep/leaf.spl`.

Nothing is *wrong* with what `check` checks — membership and count are correct —
but any downstream consumer that assumes sorted output is wrong today, and a
regression in that order cannot be pinned by a portable spec.

## Consequence for the check membership pin

`test/01_unit/app/check/check_directory_membership_pin_spec.spl` (added by L5-D)
deliberately does **not** pin within-directory order, and says why in its
header. Once `sort()` works, that spec should be tightened to pin lexicographic
order, and this record is the trigger for doing so.

## Not yet determined

- Whether `sort()` is equally dead for `[i64]` / other element types, or whether
  this is specific to `text` comparison. Only `[text]` was measured.
- Whether the intended contract is in-place or by-value. Both are broken now, so
  the reproducer above asserts neither; whoever fixes this picks the contract and
  should state it in `doc/07_guide/quick_reference/syntax_quick_reference.md`.
- Whether a `sort_by`/comparator form exists and works. Not probed.
