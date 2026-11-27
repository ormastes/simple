# Knowledge Registry Schema

`knowledge_registry.sdn` is the canonical, versioned routing inventory. A feature
route has one exact `feature_id`, group base, and optional expert overlay. A
layer route has a normalized repository-relative source prefix, layer base,
optional expert overlay, and architecture profile.

Selection is fail-closed: exact feature match, then longest path-prefix match
for every planned or changed source path. Equal-length competing layer groups,
missing routes, duplicate feature IDs, and empty path sets are errors. Results
are deduplicated and lexically ordered before the receipt is written.

`src/os/kernel/**` and `src/os/drivers/**` always require `mdsoc_only`. This is a
hard selector invariant; feature metadata cannot enable ECS or MDSOC+ there.
Receipts record registry version, feature, selected knowledge paths, each source
path and matched prefix, and architecture profile.

## `task_skills` table (registry version 2)

The same file carries the goal-start task-skill inventory as a top-level
`task_skills:` section after `layer_routes:`. Version 2 only adds this section;
`feature_routes` and `layer_routes` are unchanged, so existing route consumers
keep working. Each row is a `- skill_id: ...` block with exactly these keys:

| key | meaning |
| --- | --- |
| `skill_id` | unique id (also the dependency and alias namespace) |
| `task_class` | one of `setup dev debug research design impl refactor verify release other`; at most one primary skill per class |
| `version` | skill row version |
| `canonical_path` | provider-neutral skill doc; must exist |
| `claude` `codex` `gemini` `kimi` | repository-relative adapter path, or `disabled` |
| `aliases` | comma-separated alternate names, or `none`; must not repeat or shadow another id |
| `depends_on` | comma-separated skill ids, or `none`; must exist and be acyclic |
| `fallback` | always `ask` (an unknown provider activates nothing and asks) |

Rows exist only for skills whose files exist; a task class with no row (today
`setup`, `other`) selects as `skill-missing`, and `kimi` is `disabled` for every
row because no Kimi skill directory exists yet. The pure selector
`src/lib/common/llm/task_skill_selector.spl` validates the whole table fail
closed (malformed row, duplicate id, ambiguous alias or task class, missing or
cyclic dependency) before resolving a class for a provider, and emits a
`GoalSkillSelectionV1` receipt carrying the registry version and SHA-256 digest.
