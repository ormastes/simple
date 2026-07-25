# Claude Full Hidden Stub Registry

> Projects every claude_full parts-bin hidden-disabled stub descriptor into one neutral
> registry and compares it with normalized source discovery.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Hidden Stub Registry

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tools / LLM / Claude Full / Commands |
| Status | Active; execution requires a qualified self-hosted Simple runtime |
| Requirements | REQ-LLM-CARET-HIDDEN-008 (supporting parts-bin metadata) |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl` |
| Updated | 2026-07-24 |
| Generator | Manual synchronization; docgen execution remains a qualification gate |

## Scope

The parts-bin aggregate imports the 14 import-safe leaf descriptor owners,
choosing underscore forms for hyphenated identities, and projects their
heterogeneous command values into
`ClaudeHiddenStubCommandRecord`. The executable scenario independently walks
the command source indexes, identifies `name: "stub"` descriptors, normalizes
hyphen/underscore twins, and compares the discovered and registered identities
in both directions.

The fixed count of 14 is supporting evidence only. A new source stub without a
registry record, an orphan record, a duplicate registered identity, a missing
underscore import owner, or a descriptor whose hidden/enabled metadata drifts
causes a real assertion failure. Six physical hyphen/underscore twin pairs
collapse to one logical identity each.

This parts-bin metadata contract does not prove shipped Caret command
admission, every distributed hidden feature, current upstream Claude parity,
or executable PASS before the SSpec and doc generator run on a qualified
self-hosted runtime.

## Scenario

### REQ-LLM-CARET-HIDDEN-008: hidden disabled stub inventory

#### should derive every hidden disabled stub from claude_full leaf descriptors and match normalized source discovery

- Load the parts-bin hidden-stub registry.
  - Expected: the parts-bin aggregate is nonempty and contains 14 unique
    canonical identities.
- Check every hidden stub is disabled.
  - Expected: each record is derived as `command_name=stub`, `hidden=true`,
    and `enabled=false`.
  - Expected: every normalized source identity has exactly one registry
    identity and an import-safe owner.
  - Expected: every registry identity exists in normalized source discovery.

<details>
<summary>Executable SSpec</summary>

```simple
step("Load the parts-bin hidden-stub registry")
val records = setup_hidden_stub_registry_fixture()

step("Check every hidden stub is disabled")
expect(check_hidden_stub_registry_contract(records)).to_equal("complete")
```

</details>

<details>
<summary>Supporting SSpec helpers</summary>

```simple
val HIDDEN_STUB_ROOT = "src/app/llm_caret/claude_full/commands/"
val HIDDEN_STUB_SUFFIX = "/index.spl"

class HiddenStubSourceDiscovery:
    physical_paths: [text]
    canonical_ids: [text]

fn _hidden_stub_contains_text(values: [text], wanted: text) -> bool:
    for value in values:
        if value == wanted:
            return true
    false

fn _hidden_stub_normalize_id(source_id: text) -> text:
    source_id.replace("_", "-")

fn _hidden_stub_compact_source(source: text) -> text:
    var compact = source.replace(" ", "")
    compact = compact.replace("\t", "")
    compact = compact.replace("\r", "")
    compact.replace("\n", "")

fn _discover_hidden_stub_sources() -> HiddenStubSourceDiscovery:
    var physical_paths: [text] = []
    var canonical_ids: [text] = []
    for path in dir_walk(HIDDEN_STUB_ROOT):
        if path.starts_with(HIDDEN_STUB_ROOT) and path.ends_with(HIDDEN_STUB_SUFFIX):
            val compact_source = _hidden_stub_compact_source(file_read_text(path))
            if compact_source.contains("name:\"stub\""):
                val relative_end = path.len() - HIDDEN_STUB_SUFFIX.len()
                val raw_id = path.substring(HIDDEN_STUB_ROOT.len(), relative_end)
                if not raw_id.contains("/"):
                    val canonical_id = _hidden_stub_normalize_id(raw_id)
                    val import_id = canonical_id.replace("-", "_")
                    expect(raw_id == canonical_id or raw_id == import_id).to_equal(true)
                    expect(_hidden_stub_contains_text(physical_paths, path)).to_equal(false)
                    physical_paths.push(path)
                    if not _hidden_stub_contains_text(canonical_ids, canonical_id):
                        canonical_ids.push(canonical_id)
    HiddenStubSourceDiscovery(
        physical_paths: physical_paths,
        canonical_ids: canonical_ids
    )

fn setup_hidden_stub_registry_fixture() -> [ClaudeHiddenStubCommandRecord]:
    val records = hiddenDisabledStubCommandRegistry()
    expect(records.len()).to_be_greater_than(0)
    records

fn check_hidden_stub_registry_contract(records: [ClaudeHiddenStubCommandRecord]) -> text:
    val discovery = _discover_hidden_stub_sources()
    var registered_ids: [text] = []

    expect(records.len()).to_equal(14)
    expect(discovery.canonical_ids.len()).to_equal(records.len())
    expect(discovery.physical_paths.len()).to_be_greater_than(0)

    for record in records:
        expect(record.source_id).to_equal(_hidden_stub_normalize_id(record.source_id))
        expect(_hidden_stub_contains_text(registered_ids, record.source_id)).to_equal(false)
        registered_ids.push(record.source_id)

        val import_owner = HIDDEN_STUB_ROOT + record.source_id.replace("-", "_") + HIDDEN_STUB_SUFFIX
        expect(record.source_file).to_equal(import_owner)
        expect(_hidden_stub_contains_text(discovery.physical_paths, record.source_file)).to_equal(true)
        expect(file_read_text(record.source_file)).to_contain("name: \"stub\"")
        expect(record.command_name).to_equal("stub")
        expect(record.hidden).to_equal(true)
        expect(record.enabled).to_equal(false)
        expect(_hidden_stub_contains_text(discovery.canonical_ids, record.source_id)).to_equal(true)

    for discovered_id in discovery.canonical_ids:
        expect(_hidden_stub_contains_text(registered_ids, discovered_id)).to_equal(true)
        val import_owner = HIDDEN_STUB_ROOT + discovered_id.replace("-", "_") + HIDDEN_STUB_SUFFIX
        expect(_hidden_stub_contains_text(discovery.physical_paths, import_owner)).to_equal(true)

    "complete"
```

</details>

</details>
