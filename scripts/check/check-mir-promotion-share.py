#!/usr/bin/env python3
"""Check MIR promotion window ordering and both cleanup paths without a build."""
from pathlib import Path
import re


def check(source):
    start = source.index("    me lower_module_transient_scoped")
    body = source[start:]
    end = re.search(r"\n    me ", body[1:])
    if end:
        body = body[:end.start() + 1]
    body = re.sub(r"(?m)^\s*#.*$", "", body)
    tokens = [
        "scope_decisions = scope_decisions | 2",
        "val _owner_share_opened = transient_heap_promote_share_begin_v1()",
        "if not transient_heap_promote_v1(lowered):",
        "val _module_share_closed = transient_heap_promote_share_end_v1()",
        "val _ended_module = mir_abort_reverse_reference_scope_v1(reverse_token)",
        'return Err("MIR module ownership promotion failed for {module.name}")',
        'mir_section_profile_mark("s2_promote_mir", module.name)',
        "val owner_promoted = self.promote_transient_owner()",
        "val _owner_share_closed = transient_heap_promote_share_end_v1()",
        "if not owner_promoted:",
        "val _ended_owner = mir_abort_reverse_reference_scope_v1(reverse_token)",
        'mir_section_profile_mark("s3_promote_owner", module.name)',
    ]
    positions = [body.index(token) for token in tokens]
    assert positions == sorted(positions), "promotion/cleanup/profile ordering changed"
    assert body.count("transient_heap_promote_share_begin_v1()") == 1
    assert body.count("transient_heap_promote_share_end_v1()") == 2
    failure = body[positions[2]:positions[5]]
    assert re.search(r"(?m)^            val _module_share_closed =", failure), "failure close must be in failure arm"
    assert re.search(r"(?m)^        val _owner_share_closed =", body), "success close must be unconditional"


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    source = (root / "src/compiler/50.mir/_MirLowering/module_lowering.spl").read_text()
    check(source)
    mutations = [
        source.replace("val _module_share_closed = transient_heap_promote_share_end_v1()", "val _module_share_closed = false", 1),
        source.replace("val _owner_share_closed = transient_heap_promote_share_end_v1()", "val _owner_share_closed = false", 1),
        source.replace("        val _owner_share_opened = transient_heap_promote_share_begin_v1()\n", "", 1),
        source.replace("            val _module_share_closed", "        val _module_share_closed", 1),
    ]
    for mutation in mutations:
        try:
            check(mutation)
        except (ValueError, AssertionError):
            continue
        raise AssertionError("unsafe mutation accepted")
    print("PASS: MIR shared module/owner promotion and 4 rejected cleanup mutations")
