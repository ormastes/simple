# Forbidden Verbs Specification

> <details>

<!-- sdn-diagram:id=forbidden_verbs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=forbidden_verbs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

forbidden_verbs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=forbidden_verbs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Forbidden Verbs Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sj/forbidden_verbs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Forbidden Verbs - Interactive Rebase

#### forbids git rebase -i

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "rebase", "-i"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("FORBIDDEN")
expect(result.message).to_contain("rebase -i")
```

</details>

#### allows git rebase without -i

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "rebase", "main"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Force Push

#### forbids git push --force

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "push", "--force"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("force-push")
```

</details>

#### forbids git push -f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "push", "-f"])
expect(result.allowed).to_equal(false)
```

</details>

#### allows git push with --bookmark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "push", "--bookmark", "main"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Bare Push

#### forbids bare git push

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "push"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("ambiguous")
```

</details>

#### allows git push with --via-worktree

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "push", "--via-worktree"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Bare Checkout

#### forbids bare git checkout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "checkout"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("not meaningful")
```

</details>

#### allows git checkout with rev

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "checkout", "main"])
expect(result.allowed).to_equal(true)
```

</details>

### Forbidden Verbs - Filter-Branch

#### forbids git filter-branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "filter-branch"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("filter-branch")
```

</details>

### Forbidden Verbs - Stash

#### forbids git stash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git", "stash"])
expect(result.allowed).to_equal(false)
expect(result.message).to_contain("jj new")
```

</details>

### Forbidden Verbs - Passthrough

#### allows non-git commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["describe", "-m", "test"])
expect(result.allowed).to_equal(true)
```

</details>

#### allows empty argv

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden([])
expect(result.allowed).to_equal(true)
```

</details>

#### allows single git with no verb

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_forbidden(["git"])
expect(result.allowed).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
