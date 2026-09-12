# Test-tree divergence: scoped-delta step-over record for the web-layout round-3 range

Required by `.claude/rules/vcs.md` § test-tree divergence guard: *"Landing on a
delta-PASS additionally REQUIRES recording the pre-existing offender list … in
the commit message or a `doc/08_tracking/bug/` record — an unrecorded step-over
is a violation even when the delta is clean."* This is that record.

## Range and verdict

```
sh scripts/check/check-test-tree-divergence-delta.shs \
   cca466602e5e29d84a83ab2edc3d0f2c5963d4b9 \
   35a350d3dedf9005371e0a2057f323e56651927f
```

- BASE: `cca466602e5` (`origin/main`, PR #589)
- NEW: `35a350d3ded` (web-layout round 3)
- Runtime: ~14 min. Verdict, last line of stdout, **exit 0**:

```
check-test-tree-divergence-delta: pre-existing red is identical at BASE and NEW;
  this range introduces nothing
check-test-tree-divergence-delta: PASS — 3209 pre-existing offender(s),
  0 introduced by this range
```

The base verdict the delta helper stepped over, verbatim:

```
check-test-tree-divergence: FAIL — 3943 diverged vs 965 baselined
  (3081 new, 103 fixed-but-still-baselined); 26 mirror-only
  (25 unallowlisted, 0 stale-allowlist); half-landed: skipped (no --base)
```

## The pre-existing offender list

3,943 lines, SHA-256
`078e4b91199ac97d46f66cbf99996e12cb78f56311cae7078372e483c3c4daf8`, split
`unit:` 3,570 / `integration:` 373. It is byte-identical at BASE and at NEW —
which is the whole basis for landing over it. First entries:

```
integration:app/add_remove_log_modes_spec.spl
integration:app/app_mcp_intensive_spec.spl
integration:app/brief_log_modes_spec.spl
integration:app/bug_add_resolve_log_modes_spec.spl
integration:app/bug_gen_log_modes_spec.spl
```

33 of the 3,943 are under `browser_engine/`, the tree this change touches:

```
unit:browser_engine/anonymous_block_spec.spl
unit:browser_engine/html5lib_tokenizer_spec.spl
unit:browser_engine/html_tokenizer_spec.spl
unit:browser_engine/html_tree_builder_spec.spl
unit:browser_engine/js_integration_spec.spl
unit:browser_engine/layout_paint_contract_pin_spec.spl
   (…27 more)
```

**None of them is a file this range adds or edits.** The three specs landed here
—`grid_repeat_minmax_track_list_spec.spl`,
`flex_wrap_grow_distribution_spec.spl`,
`inline_content_area_half_leading_spec.spl` — appear **zero** times in the
offender list.

## Why the three new specs live only in `test/01_unit/browser_engine/`

`test/unit/browser_engine/` holds 17 specs; `test/01_unit/browser_engine/` holds
53. Adding to the numbered tree only is the established pattern in this
directory, and is what F20's two specs
(`flex_wrap_auto_width_item_spec.spl`, `form_control_ua_font_spec.spl`) did when
they landed hours earlier in the same lane. The delta guard confirms this
introduces no new divergence and no new mirror-only offender attributable to
this range.

This record does NOT claim the 3,943-offender backlog is acceptable. It is a
standing red owned by whoever owns the duplicate test trees; it is recorded here
only so that this range's step-over is auditable rather than silent.
