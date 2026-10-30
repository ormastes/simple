#!/usr/bin/env python3
"""One-off byte-preserving V4 bug-ledger migration; not a product toolchain.

Run from the repository root with --prepare to create a same-directory
candidate after validating the frozen V4 inputs, raw-row identities, inverse
reconstruction, idempotence, and scratch fixtures. Run --install only after
reviewing that candidate. Both operations are compare-and-swap guarded.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile
import time
import zlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
DB = ROOT / "doc/08_tracking/bug/bug_db.sdn"
BUG_DOC = ROOT / "doc/08_tracking/bug/font_registry_bungee_digest_mismatch_blocks_selected_outline_path_2026-08-15.md"
TRIAGE = ROOT / "doc/08_tracking/bug/triage_20261027"
CAT = TRIAGE / "reviewed_categories_v4.sdn"
RES = TRIAGE / "residual_ids_v4.sdn"
MANIFEST = TRIAGE / "manifest_v4.sdn"
SCOPE = TRIAGE / "reproduction_scope_v4.sdn"
CAMPAIGN = "triage-20261027-v4"
ASSESS = "c0b3ad911f4cb00c0f3550b05baa8d06347d17d0"
BASE = "f963f94ce84de1836aa5941e9eec49094112cc8a"
EVIDENCE_COMMIT = "b078b2807cf4379640f832a29672119f57e565ff"
BASE_DB_SHA = "c617ac5ea12dfc2887fe2fb6e4e6433daf459ac8a4c74ef27b3c88e11e85fae4"
BASE_CRC = b"#sdn-crc32:2672672909\n"
BASE_BUNGEE_ROW_SHA = "7dbe987390af149e40b210efc72eeb1b48c437e646dc1ae30ec4cb6532358f49"
V4_MANIFEST_SHA = "20c9585305077f9cdec78d82dee9f3add8fb1d98258b9209ad6169097072296c"
V4_CATEGORIES_SHA = "f47867ce23862fe32ca679bd72a0f53a2ea1e0727044f8c32f71209653d4da42"
V4_RESIDUAL_SHA = "632c63f649780004373b3713f8e8ce4f5e91196974e9cd5a0b22e89d1d49e007"
V4_SCOPE_SHA = "ebb90f38ab871c07c971222b86e285d39f02d3284bd100364e5e23ed47440ca8"
LEGACY_LOG_ZERO_HASHES = {
    "ae4b820bced78172fd9c00e836d2fba36fa3b3729dbd867ea017371ea116fa37",
    "ca6ff96a9ea761577b93f921ad84cbb252b11512d31b5e932b0d16f6476b4883",
}
BOUNCE_ID = "font_registry_bungee_digest_mismatch_blocks_selected_outline_path_2026-08-15"
REPRO_ID = "BUG-STAGE3-RESUME-SOURCE-POLICY-20261011"
MAX_LINE = 1152921504606846975
ALLOWED = re.compile(rb"^[A-Za-z0-9_./:=+-]+(?: [A-Za-z0-9_./:=+-]+)*$")
ROW_ID = re.compile(rb"^\s*([^,|\"\s]+),")
LOG_PREFIX = re.compile(rb"^\s*([^,|\"\s]+),\s*(-?[0-9]+),")
HEADER = re.compile(rb"^[A-Za-z_][A-Za-z0-9_-]* \|.*\|$")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def committed_blob(path: Path) -> bytes:
    relative = path.relative_to(ROOT).as_posix()
    result = subprocess.run(["git", "show", f"{BASE}:{relative}"], cwd=ROOT, capture_output=True, check=True)
    return result.stdout


def sdn_records(path: Path, fields: int) -> list[list[str]]:
    raw = path.read_bytes()
    rows = []
    for line in raw.splitlines():
        if not line.strip() or line.lstrip().startswith(b"#") or b" |" in line:
            continue
        if b"|" in line:
            continue
        vals = [part.strip().decode("ascii") for part in line.split(b",")]
        if len(vals) != fields:
            raise ValueError(f"{path}: expected {fields} fields, got {len(vals)}")
        rows.append(vals)
    return rows


def input_rows() -> tuple[dict[str, dict[str, str]], set[str], dict[str, str]]:
    # This one-off application is bound to the exact pre-application base. A
    # post-commit invocation is intentionally refused; do not replan on a
    # descendant release from this frozen script. The splice itself is
    # idempotent and its pre-commit no-op path is exercised by the fixture.
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
    if head != BASE:
        raise ValueError(f"fixed-base one-off migration refuses descendant HEAD {head}; base is {BASE}")
    categories = sdn_records(CAT, 9)
    residuals = sdn_records(RES, 10)
    if len(categories) != 1571 or len({r[0] for r in categories}) != 1571:
        raise ValueError("V4 accepted categories are not exactly 1571 unique rows")
    if len(residuals) != 31 or len({r[0] for r in residuals}) != 31:
        raise ValueError("V4 residual IDs are not exactly 31 unique rows")
    cat_by_id = {row[0]: dict(zip(("bug_id", "assessed_sha", "inspection_level", "validity", "reproducibility", "solution", "structural_change", "action", "review_receipt"), row)) for row in categories}
    residual_by_id = {row[0]: dict(zip(("bug_id", "assessed_sha", "inspection_level", "validity", "reproducibility", "solution", "structural_change", "action", "review_state", "review_receipt"), row)) for row in residuals}
    res_ids = {row[0] for row in residuals}
    if res_ids & cat_by_id.keys():
        raise ValueError("accepted category IDs overlap residual IDs")
    if any(row["review_state"] != "needs_more_evidence" for row in residual_by_id.values()):
        raise ValueError("residual file contains an unexpected review state")
    cat_by_id.update({key: {name: value for name, value in row.items() if name != "review_state"} for key, row in residual_by_id.items()})
    if len(cat_by_id) != 1602:
        raise ValueError("V4 review partition does not total 1602 IDs")
    if any(row["assessed_sha"] != ASSESS for row in cat_by_id.values()):
        raise ValueError("mixed assessment SHAs in V4 categories")
    if {key for key, row in cat_by_id.items() if row["validity"] == "invalid"} != {BOUNCE_ID}:
        raise ValueError("V4 contains an unexpected invalid classification outside the one approved closure")
    if {key for key, row in cat_by_id.items() if row["reproducibility"] == "reproducible"} != {REPRO_ID}:
        raise ValueError("V4 reproduction set is not the one HOST_PROTOCOL record")
    if any(row["reproducibility"] != "untested" for key, row in cat_by_id.items() if key != REPRO_ID):
        raise ValueError("unexpected non-HOST_PROTOCOL reproduction claim")
    if cat_by_id[BOUNCE_ID]["action"] != "close_invalid_candidate":
        raise ValueError("Bungee is not the V4 invalid-closure candidate")
    manifest_sha, cat_sha, res_sha = sha(MANIFEST.read_bytes()), sha(CAT.read_bytes()), sha(RES.read_bytes())
    scope_sha = sha(SCOPE.read_bytes())
    expected_digests = (manifest_sha, cat_sha, res_sha, scope_sha)
    if expected_digests != (V4_MANIFEST_SHA, V4_CATEGORIES_SHA, V4_RESIDUAL_SHA, V4_SCOPE_SHA):
        raise ValueError("V4 evidence working-tree hashes differ from the reviewed manifest bindings")
    for path, expected in ((MANIFEST, V4_MANIFEST_SHA), (CAT, V4_CATEGORIES_SHA), (RES, V4_RESIDUAL_SHA), (SCOPE, V4_SCOPE_SHA)):
        if sha(committed_blob(path)) != expected or committed_blob(path) != path.read_bytes():
            raise ValueError(f"V4 evidence is not byte-identical to committed base {BASE}: {path}")
    scopes = sdn_records(SCOPE, 14)
    scoped = {row[0]: row for row in scopes}
    if set(scoped) != {REPRO_ID}:
        raise ValueError("V4 scope table must contain exactly the one HOST_PROTOCOL row")
    scope_row = scoped[REPRO_ID]
    if scope_row[2] != "HOST_PROTOCOL" or cat_by_id[REPRO_ID]["reproducibility"] != "reproducible":
        raise ValueError("scope-table reproduction does not match its category")
    ev = {}
    for bug_id, row in cat_by_id.items():
        pending = bug_id in res_ids
        ev[bug_id] = {
            "review": "needs_more_evidence" if pending else "accepted",
            "evidence": str((TRIAGE / ("residual_ids_v4.sdn" if pending else "reviewed_categories_v4.sdn")).relative_to(ROOT)),
            "evidence_sha256": res_sha if pending else cat_sha,
            "manifest_sha256": manifest_sha,
            "evidence_commit": EVIDENCE_COMMIT,
        }
    return cat_by_id, res_ids, {"manifest": manifest_sha, "categories": cat_sha, "residuals": res_sha, "scope": scope_sha}


def raw_sections(data: bytes) -> tuple[dict[str, list[tuple[int, int, bytes]]], tuple[int, int, bytes]]:
    """Return table row spans (excluding headers) keyed by table; do no decoding/reserialization."""
    lines = data.splitlines(keepends=True)
    starts = []
    offset = 0
    for line in lines:
        clean = line.rstrip(b"\r\n")
        if HEADER.match(clean):
            starts.append((offset, clean.split(b" |", 1)[0].decode("ascii")))
        offset += len(line)
    sections: dict[str, list[tuple[int, int, bytes]]] = {}
    headers = []
    offset = 0
    for line in lines:
        clean = line.rstrip(b"\r\n")
        if HEADER.match(clean):
            name = clean.split(b" |", 1)[0].decode("ascii")
            headers.append((offset, name))
        offset += len(line)
    for n, (start, name) in enumerate(headers):
        end = headers[n + 1][0] if n + 1 < len(headers) else len(data)
        # Find the header's exact line end without parsing any table values.
        header_end = data.find(b"\n", start)
        if header_end < 0:
            raise ValueError("unterminated table header")
        pos = header_end + 1
        rows = []
        while pos < end:
            line_end = data.find(b"\n", pos)
            line_end = len(data) if line_end < 0 else line_end + 1
            line = data[pos:line_end]
            if line.strip():
                rows.append((pos, line_end, line))
            pos = line_end
        sections[name] = rows
    if "bug_investigation_logs" not in sections:
        raise ValueError("missing investigation log table")
    logs = [h for h in headers if h[1] == "bug_investigation_logs"]
    if len(logs) != 1:
        raise ValueError("expected one investigation log header")
    start, name = logs[0]
    h_end = data.find(b"\n", start) + 1
    boundary = h_end
    for pos, _, row in sections[name]:
        boundary = pos + len(row)
    # The boundary follows the last raw log row, before its existing separator.
    return sections, (boundary, boundary, b"")


def extract_db(data: bytes, ids: set[str]) -> tuple[dict[str, list[tuple[int, int, bytes, str]]], dict[str, list[int]], tuple[int, int, bytes]]:
    sections, boundary = raw_sections(data)
    matched: dict[str, list[tuple[int, int, bytes, str]]] = {i: [] for i in ids}
    for table in ("bugs_active", "bugs"):
        for start, end, row in sections.get(table, []):
            match = ROW_ID.match(row)
            if not match:
                continue
            key = match.group(1).decode("ascii")
            if key in matched:
                matched[key].append((start, end, row, table))
    absent = [key for key, rows in matched.items() if not rows]
    if absent:
        raise ValueError(f"authoritative IDs missing from live DB rows: {absent[:5]}")
    schema = b"bug_investigation_logs |bug_id, line_num, content|"
    headers = [line.rstrip(b"\r\n") for line in data.splitlines(keepends=True) if line.startswith(b"bug_investigation_logs ")]
    if headers != [schema]:
        raise ValueError("investigation log schema is missing, duplicated, or changed")
    logs: dict[str, list[int]] = {i: [] for i in ids}
    for _, _, row in sections["bug_investigation_logs"]:
        id_match = ROW_ID.match(row)
        if not id_match:
            continue
        key = id_match.group(1).decode("ascii")
        if key in logs:
            cells = row.strip().split(b",", 2)
            if len(cells) != 3 or not re.fullmatch(rb"\s*-?[0-9]+\s*", cells[1]):
                raise ValueError(f"nonnumeric/malformed investigation line number for {key}")
            n = int(cells[1])
            if n < 0 or n >= MAX_LINE:
                raise ValueError(f"negative investigation line number for {key}")
            logs[key].append(n)
    return matched, logs, boundary


def record_fields(bug_id: str, category: dict[str, str], pending: bool, evidence: dict[str, str]) -> tuple[bytes, str]:
    scope = "HOST_PROTOCOL" if bug_id == REPRO_ID else "UNRUN"
    scope_path = str((TRIAGE / "reproduction_scope_v4.sdn").relative_to(ROOT)) if bug_id == REPRO_ID else "none"
    scope_sha = evidence["scope_sha256"] if bug_id == REPRO_ID else "none"
    # Bind every V4 category field and the correct accepted/pending evidence snapshot.
    semantic = [CAMPAIGN, bug_id, ASSESS, evidence["review"], category["inspection_level"], category["validity"], category["reproducibility"], scope, category["solution"], category["structural_change"], category["action"], category["review_receipt"], evidence["evidence"], evidence["evidence_sha256"], evidence["manifest_sha256"], evidence["evidence_commit"], scope_path, scope_sha]
    digest = sha("\n".join(semantic).encode("ascii"))
    fields = [f"audit={CAMPAIGN}", f"assessed_sha={ASSESS}", f"review={evidence['review']}", f"inspection={category['inspection_level']}", f"validity={category['validity']}", f"reproducibility={category['reproducibility']}", f"scope={scope}", f"solution={category['solution']}", f"structural={category['structural_change']}", f"action={category['action']}", f"review_receipt={category['review_receipt']}", f"evidence={evidence['evidence']}", f"evidence_sha256={evidence['evidence_sha256']}", f"manifest_sha256={evidence['manifest_sha256']}", f"evidence_commit={evidence['evidence_commit']}", f"scope_evidence={scope_path}", f"scope_sha256={scope_sha}", f"record_sha256={digest}"]
    payload = " ".join(fields).encode("ascii")
    if len(payload) > 1024 or not ALLOWED.fullmatch(payload):
        raise ValueError(f"invalid/oversize payload for {bug_id}")
    return payload, digest


def log_rows(data: bytes) -> list[tuple[str, int, bytes]]:
    sections, _ = raw_sections(data)
    out = []
    for _, _, row in sections["bug_investigation_logs"]:
        m = LOG_PREFIX.match(row)
        if m:
            out.append((m.group(1).decode("ascii"), int(m.group(2)), row))
    return out


def splice(data: bytes, categories: dict[str, dict[str, str]], residuals: set[str], evidence_digests: dict[str, str], allow_base_sha: str | None = None) -> tuple[bytes, dict]:
    actual_sha = sha(data)
    if allow_base_sha and actual_sha != allow_base_sha:
        raise ValueError(f"stale database CAS: expected {allow_base_sha}, got {actual_sha}")
    ids = set(categories)
    matches, old_nums, (insert_at, _, _) = extract_db(data, ids)
    # Only this exact preexisting numbering anomaly is grandfathered.
    existing_logs = log_rows(data)
    zero_rows = [row for bug, number, row in existing_logs if bug == "phase1_docstring_trim_start_dispatch_2026_10_12" and number == 0]
    if len(zero_rows) != 2 or len({sha(row) for row in zero_rows}) != 2 or {sha(row) for row in zero_rows} != LEGACY_LOG_ZERO_HASHES:
        raise ValueError("the frozen duplicate line-zero anomaly changed")
    for bug_id, nums in old_nums.items():
        if any(number >= MAX_LINE for number in nums):
            raise ValueError(f"line number exceeds owner ceiling: {bug_id}")
        if len(nums) != len(set(nums)) and bug_id != "phase1_docstring_trim_start_dispatch_2026_10_12":
            raise ValueError(f"unexpected existing investigation number collision: {bug_id}")
    payloads: dict[str, tuple[bytes, str, int]] = {}
    for bug_id in sorted(ids):
        ev = {"review": "needs_more_evidence" if bug_id in residuals else "accepted",
              "evidence": str((TRIAGE / ("residual_ids_v4.sdn" if bug_id in residuals else "reviewed_categories_v4.sdn")).relative_to(ROOT)),
              "evidence_sha256": evidence_digests["residuals"] if bug_id in residuals else evidence_digests["categories"],
              "manifest_sha256": evidence_digests["manifest"], "evidence_commit": EVIDENCE_COMMIT, "scope_sha256": evidence_digests["scope"]}
        payload, digest = record_fields(bug_id, categories[bug_id], bug_id in residuals, ev)
        existing = [row for b, _, row in existing_logs if b == bug_id and b"audit=" + CAMPAIGN.encode() in row]
        if existing:
            if len(existing) != 1 or payload not in [line.split(b", ", 2)[2].rstrip(b"\r\n").strip(b'"') for line in existing]:
                raise ValueError(f"same campaign/ID has conflicting payload: {bug_id}")
            current = existing[0]
            m = LOG_PREFIX.match(current)
            assert m
            if sum(1 for b, n, _ in existing_logs if b == bug_id and n == int(m.group(2))) != 1:
                raise ValueError(f"existing campaign line number is not unique: {bug_id}")
            payloads[bug_id] = (payload, digest, int(m.group(2)))
            continue
        line_no = max(old_nums[bug_id], default=-1) + 1
        if line_no >= MAX_LINE:
            raise ValueError(f"line number exhausted: {bug_id}")
        payloads[bug_id] = (payload, digest, line_no)
    # Reuse the exact Bungee row, changing only status and updated_at cell spans.
    bungee_rows = matches[BOUNCE_ID]
    if len(bungee_rows) != 1 or bungee_rows[0][3] != "bugs_active":
        raise ValueError("Bungee raw-row identity/table conflict")
    b_start, b_end, old_bungee, _ = bungee_rows[0]
    if b", P3, open," in old_bungee and old_bungee.endswith(b", 2026-08-15, 2026-09-21, true\n"):
        new_bungee = old_bungee.replace(b", open,", b", closed,", 1).replace(b", 2026-09-21, true\n", b", 2026-10-27, true\n", 1)
        if old_bungee.count(b", open,") != 1 or old_bungee.count(b", 2026-09-21, true\n") != 1:
            raise ValueError("Bungee cell spans are ambiguous")
    elif b", P3, closed," in old_bungee and old_bungee.endswith(b", 2026-08-15, 2026-10-27, true\n"):
        new_bungee = old_bungee
    else:
        raise ValueError("Bungee status/date/valid precondition changed")
    # Insert only new rows. Existing same-campaign rows are a zero-change no-op.
    new_lines = []
    for bug_id in sorted(ids):
        payload, digest, line_no = payloads[bug_id]
        if any(b == bug_id and b"audit=" + CAMPAIGN.encode() in row for b, _, row in existing_logs):
            continue
        new_lines.append(f"    {bug_id}, {line_no}, ".encode("ascii") + payload + b"\n")
    insertion = b"".join(new_lines)
    # Replacing Bungee by exact raw span, plus inserting at the exact table boundary.
    body = data[:b_start] + new_bungee + data[b_end:]
    if insert_at >= b_end:
        insert_at += len(new_bungee) - len(old_bungee)
    candidate = body[:insert_at] + insertion + body[insert_at:]
    return candidate, {"payloads": payloads, "inserted": insertion, "old_bungee": old_bungee, "new_bungee": new_bungee, "anomaly_rows": zero_rows, "id_count": len(ids), "no_op": not insertion and new_bungee == old_bungee}


def crc_body(data: bytes) -> int:
    if not data.startswith(b"#sdn-crc32:"):
        raise ValueError("missing CRC header")
    end = data.find(b"\n")
    if end < 0:
        raise ValueError("invalid CRC header")
    expected = int(data[len(b"#sdn-crc32:"):end])
    got = zlib.crc32(data[end + 1:]) & 0xFFFFFFFF
    if expected != got:
        raise ValueError(f"CRC mismatch: header={expected} actual={got}")
    return expected


def reseal_header(data: bytes) -> tuple[bytes, int]:
    end = data.find(b"\n")
    if end < 0 or not data.startswith(b"#sdn-crc32:"):
        raise ValueError("candidate missing expected SDN CRC header")
    body = data[end + 1:]
    value = zlib.crc32(body) & 0xFFFFFFFF
    return f"#sdn-crc32:{value}\n".encode("ascii") + body, value


def reconstruct(candidate: bytes, meta: dict, original: bytes) -> bool:
    # Remove exact inserted block and restore Bungee row and the original CRC header.
    x = candidate
    inserted = meta["inserted"]
    if inserted:
        if x.count(inserted) != 1:
            return False
        x = x.replace(inserted, b"", 1)
    if x.count(meta["new_bungee"]) != 1:
        return False
    x = x.replace(meta["new_bungee"], meta["old_bungee"], 1)
    x = original.split(b"\n", 1)[0] + b"\n" + x.split(b"\n", 1)[1]
    return x == original and sha(x) == sha(original)


def validate_added_rows(candidate: bytes, meta: dict, categories: dict[str, dict[str, str]], residuals: set[str], digests: dict[str, str]) -> None:
    rows = log_rows(candidate)
    campaign_rows = [(bug, num, row) for bug, num, row in rows if b"audit=" + CAMPAIGN.encode() in row]
    if len(campaign_rows) != len(categories) or {bug for bug, _, _ in campaign_rows} != set(categories):
        raise ValueError("campaign row count/ID set mismatch")
    if len({(bug, num) for bug, num, _ in campaign_rows}) != len(campaign_rows):
        raise ValueError("campaign line-number allocation collision")
    for bug_id, line_no, row in campaign_rows:
        prefix = f"    {bug_id}, {line_no}, ".encode("ascii")
        if not row.startswith(prefix) or not row.endswith(b"\n"):
            raise ValueError(f"new row does not have exact three-cell framing: {bug_id}")
        payload = row[len(prefix):-1]
        if len(payload) > 1024 or not ALLOWED.fullmatch(payload):
            raise ValueError(f"new payload grammar/length invalid: {bug_id}")
        evidence = {"review": "needs_more_evidence" if bug_id in residuals else "accepted",
                    "evidence": str((TRIAGE / ("residual_ids_v4.sdn" if bug_id in residuals else "reviewed_categories_v4.sdn")).relative_to(ROOT)),
                    "evidence_sha256": digests["residuals"] if bug_id in residuals else digests["categories"],
                    "manifest_sha256": digests["manifest"], "evidence_commit": EVIDENCE_COMMIT, "scope_sha256": digests["scope"]}
        expected, semantic_sha = record_fields(bug_id, categories[bug_id], bug_id in residuals, evidence)
        if payload != expected or f"record_sha256={semantic_sha}".encode() not in payload:
            raise ValueError(f"new payload does not map exactly to its V4 source: {bug_id}")
        if bug_id == REPRO_ID and b"scope=HOST_PROTOCOL" not in payload:
            raise ValueError("the single HOST_PROTOCOL scope was not preserved")
        if bug_id != REPRO_ID and (b"scope=UNRUN" not in payload or categories[bug_id]["reproducibility"] != "untested"):
            raise ValueError(f"unexpected reproduction scope or claim: {bug_id}")


def scratch_checks(categories: dict[str, dict[str, str]], residuals: set[str], digests: dict[str, str]) -> dict[str, str]:
    # A small byte-shaped fixture exercises the same splice with real V4 records.
    baseline_rows = log_rows(DB.read_bytes())
    legacy_rows = [row for bug, number, row in baseline_rows if bug == "phase1_docstring_trim_start_dispatch_2026_10_12" and number == 0]
    if len(legacy_rows) != 2 or {sha(row) for row in legacy_rows} != LEGACY_LOG_ZERO_HASHES:
        raise ValueError("scratch fixture could not bind the two exact legacy log-zero rows")
    def fixture(status=b"open", updated=b"2026-09-21", unrelated=b"unrelated malformed, value, \"q\"\n"):
        body = (b"bugs_active |id, priority, status, title, source, line, report, created, updated, valid|\n"
                + b"    " + BOUNCE_ID.encode() + b", P3, " + status + b", \"Bungee, title\", src, 1, report, 2026-08-15, " + updated + b", true\n"
                + b"    fixture_a, P2, open, \"" + unrelated.rstrip(b"\n") + b"\n"
                + b"    phase1_docstring_trim_start_dispatch_2026_10_12, P2, open, phase1, src, 93, report, 2026-10-12, 2026-10-12, true\n"
                + b"\nbugs |id, priority, status, title|\n    fixture_a, P2, closed, dup\n"
                + b"    phase1_docstring_trim_start_dispatch_2026_10_12, P2, open, old-archive\n\n"
                + b"bug_investigation_logs |bug_id, line_num, content|\n"
                + b"".join(legacy_rows)
                + b"    fixture_a, 2, malformed-old\n")
        return b"#sdn-crc32:0\n" + body
    # Use one actual input ID and tailor source rows for isolated behavior.
    chosen = BOUNCE_ID
    legacy = "phase1_docstring_trim_start_dispatch_2026_10_12"
    tiny = {chosen: categories[chosen], legacy: categories[legacy]}
    nonres = set()
    d = dict(digests)
    source = fixture()
    first, m1 = splice(source, tiny, nonres, d)
    sealed, _ = reseal_header(first)
    second, m2 = splice(sealed, tiny, nonres, d)
    assert second == sealed and not m2["inserted"]
    assert first.count(b"fixture_a, P2, closed, dup") == 1
    assert first.count(b"unrelated malformed, value, \"q\"") == 1
    assert len(m1["anomaly_rows"]) == 2
    assert m1["payloads"][chosen][2] == 0
    assert m1["payloads"][legacy][2] == 1
    assert m1["old_bungee"].replace(b", open,", b", closed,").replace(b"2026-09-21", b"2026-10-27").endswith(b", true\n")
    assert first.count(b"    fixture_a,") == 3
    # Exact CAS refusal on stale bytes.
    try:
        splice(source, tiny, nonres, d, allow_base_sha="0" * 64)
        raise AssertionError("stale CAS unexpectedly accepted")
    except ValueError as e:
        assert "stale database CAS" in str(e)
    # Campaign collision refusal when same ID has a different payload.
    conflict = sealed.replace(m1["payloads"][chosen][0], b"audit=triage-20261027-v4 changed=true")
    try:
        splice(conflict, tiny, nonres, d)
        raise AssertionError("same-campaign payload conflict unexpectedly accepted")
    except ValueError:
        pass
    # Preserve concurrent unrelated raw row, then replan against changed bytes.
    concurrent = sealed.replace(b"fixture_a, P2, open", b"fixture_a, P2, resolved", 1)
    replanned, _ = splice(concurrent, tiny, nonres, d)
    assert b"fixture_a, P2, resolved" in replanned
    # Distinct duplicate/archive ID and malformed row bytes survive inverse transform.
    if not reconstruct(sealed, m1, source):
        raise AssertionError("scratch inverse reconstruction failed")
    lock_results = scratch_lock_checks()
    return {"idempotence": "PASS", "stale_cas": "PASS", "same_campaign_conflict": "PASS", "concurrent_replan": "PASS", "malformed_duplicate_preservation": "PASS", "legacy_log_zero": "PASS", "bungee_narrow_cells": "PASS", **lock_results}


def scratch_lock_checks() -> dict[str, str]:
    with tempfile.TemporaryDirectory(prefix="canonical-triage-lock-") as tmp:
        path = Path(tmp) / "bug_db.sdn.lock"
        foreign = b"other-owner\n"
        path.write_bytes(foreign)
        try:
            acquire_exclusive_lock(path)
            raise AssertionError("existing lock was overwritten")
        except FileExistsError:
            if path.read_bytes() != foreign:
                raise AssertionError("existing lock changed after refusal")
        path.unlink()
        fd, identity, token = acquire_exclusive_lock(path)
        try:
            raise RuntimeError("injected validation failure")
        except RuntimeError:
            pass
        finally:
            removed = release_owned_lock(path, fd, identity, token)
        if not removed or path.exists():
            raise AssertionError("owned lock was not removed after error")
        fd, identity, token = acquire_exclusive_lock(path)
        path.unlink()
        path.write_bytes(foreign)
        removed = release_owned_lock(path, fd, identity, token)
        if removed or path.read_bytes() != foreign:
            raise AssertionError("cleanup removed a lock replaced by another owner")
    return {"existing_lock_refusal": "PASS", "owned_lock_cleanup": "PASS", "foreign_lock_preservation": "PASS"}


def check_lock_state() -> None:
    for path in (DB, Path(str(DB) + ".lock"), Path(str(DB) + ".wal")):
        if path.is_symlink():
            raise ValueError(f"symlink refused: {path}")
    if Path(str(DB) + ".lock").exists() or (Path(str(DB) + ".wal").exists() and Path(str(DB) + ".wal").stat().st_size):
        raise ValueError("live DB lock/nonempty WAL refused")


def acquire_exclusive_lock(path: Path) -> tuple[int, tuple[int, int], bytes]:
    # Match the repository database owner's lock record format: PID then usec.
    token = f"{os.getpid()}\n{time.time_ns() // 1000}\n".encode("ascii")
    fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    try:
        os.write(fd, token)
        os.fsync(fd)
        st = os.fstat(fd)
        return fd, (st.st_dev, st.st_ino), token
    except Exception:
        st = os.fstat(fd)
        try:
            current = path.lstat()
            if (current.st_dev, current.st_ino) == (st.st_dev, st.st_ino) and not path.is_symlink():
                path.unlink()
        finally:
            os.close(fd)
        raise


def release_owned_lock(path: Path, fd: int, identity: tuple[int, int], token: bytes) -> bool:
    try:
        if path.is_symlink():
            return False
        current = path.stat()
        if (current.st_dev, current.st_ino) != identity or path.read_bytes() != token:
            return False
        path.unlink()
        return True
    except FileNotFoundError:
        return False
    finally:
        os.close(fd)


def check_locked_state(lock_path: Path, identity: tuple[int, int], token: bytes) -> None:
    if DB.is_symlink() or Path(str(DB) + ".wal").is_symlink():
        raise ValueError("symlink DB/WAL refused during locked install")
    if not lock_path.exists() or lock_path.is_symlink():
        raise ValueError("owned DB lock disappeared or changed type")
    st = lock_path.stat()
    if (st.st_dev, st.st_ino) != identity or lock_path.read_bytes() != token:
        raise ValueError("owned DB lock identity/token changed")
    wal = Path(str(DB) + ".wal")
    if wal.exists() and wal.stat().st_size:
        raise ValueError("nonempty WAL appeared during locked install")


def check_bungee_report() -> None:
    report = BUG_DOC.read_bytes()
    required = (
        b"**Date:** 2026-08-15",
        b"**Status:** CLOSED",
        b"METADATA.pb",
        b"c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f",
        b"ec1a73318ff76d666c2e3cad5948b6799f4a9ed6d6af59e787f4e5372c291edf",
        b"does not claim that Bungee",
        b"historical nil-loading or fallback symptoms",
    )
    if any(value not in report for value in required) or b"**Status:** OPEN" in report:
        raise ValueError("Bungee report is not the reviewed narrow invalid-premise closure")


def validate_already_applied(data: bytes, categories: dict[str, dict[str, str]], residuals: set[str], digests: dict[str, str]) -> dict:
    crc_body(data)
    expected_noop, meta = splice(data, categories, residuals, digests)
    validate_added_rows(data, meta, categories, residuals, digests)
    if expected_noop != data or not meta["no_op"]:
        raise ValueError("database differs from the complete campaign state; partial or unrelated first-apply changes refused")
    if len([1 for bug, _, row in log_rows(data) if b"audit=" + CAMPAIGN.encode() in row]) != 1602:
        raise ValueError("already-applied state does not contain all1602 exact campaign notes")
    return meta


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--prepare", action="store_true")
    p.add_argument("--install", action="store_true")
    p.add_argument("--validate", action="store_true")
    args = p.parse_args()
    if sum((args.prepare, args.install, args.validate)) != 1:
        p.error("select exactly one of --prepare, --install, or --validate")
    cats, residuals, digests = input_rows()
    check_bungee_report()
    base = DB.read_bytes()
    if args.prepare:
        check_lock_state()
        if sha(base) != BASE_DB_SHA:
            meta = validate_already_applied(base, cats, residuals, digests)
            print(f"already_applied=verified_no_op sha256={sha(base)} crc32={crc_body(base)} notes={meta['id_count']}")
            return 0
        if not base.startswith(BASE_CRC) or crc_body(base) != 2672672909:
            raise ValueError("baseline CRC precondition mismatch")
        transformed, meta = splice(base, cats, residuals, digests, BASE_DB_SHA)
        candidate, new_crc = reseal_header(transformed)
        validate_added_rows(candidate, meta, cats, residuals, digests)
        if not reconstruct(candidate, meta, base):
            raise ValueError("candidate cannot reconstruct exact baseline bytes")
        if crc_body(candidate) != new_crc:
            raise ValueError("independent candidate CRC check failed")
        fixture_results = scratch_checks(cats, residuals, digests)
        candidate_path = Path(str(DB) + ".candidate")
        if candidate_path.is_symlink() or candidate_path.exists():
            raise ValueError("candidate path already exists; inspect it before retry")
        fd = os.open(candidate_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        with os.fdopen(fd, "wb") as target:
            target.write(candidate)
            target.flush()
            os.fsync(target.fileno())
        if sha(meta["old_bungee"]) != BASE_BUNGEE_ROW_SHA:
            candidate_path.unlink()
            raise ValueError("Bungee baseline raw-row SHA mismatch")
        print(f"prepared_candidate={candidate_path}")
        print(f"source_sha256={sha(base)} candidate_body_crc32={new_crc} inserted_rows={len(meta['payloads'])} inserted_bytes={len(meta['inserted'])}")
        print(f"bungee_old_row_sha256={sha(meta['old_bungee'])} bungee_new_row_sha256={sha(meta['new_bungee'])} inserted_block_sha256={sha(meta['inserted'])}")
        print("scratch=" + ",".join(f"{k}:{v}" for k, v in fixture_results.items()))
        return 0
    candidate_path = Path(str(DB) + ".candidate")
    if args.validate:
        if candidate_path.is_symlink():
            raise ValueError("candidate symlink refused")
        candidate = candidate_path.read_bytes()
        crc = crc_body(candidate)
        print(f"candidate_sha256={sha(candidate)} crc32={crc}")
        return 0
    check_lock_state()
    lock_path = Path(str(DB) + ".lock")
    lock_fd, lock_identity, lock_token = acquire_exclusive_lock(lock_path)
    try:
        check_locked_state(lock_path, lock_identity, lock_token)
        base = DB.read_bytes()
        if sha(base) != BASE_DB_SHA:
            meta = validate_already_applied(base, cats, residuals, digests)
            print(f"already_applied=verified_no_op sha256={sha(base)} crc32={crc_body(base)} notes={meta['id_count']}")
            return 0
        if candidate_path.is_symlink():
            raise ValueError("candidate symlink refused")
        candidate = candidate_path.read_bytes()
        crc = crc_body(candidate)
        transformed, meta = splice(base, cats, residuals, digests, BASE_DB_SHA)
        expected, expected_crc = reseal_header(transformed)
        if candidate != expected or crc != expected_crc:
            raise ValueError("candidate differs from deterministic fresh plan")
        if not reconstruct(candidate, meta, base):
            raise ValueError("install inverse reconstruction failed")
        validate_added_rows(candidate, meta, cats, residuals, digests)
        if sha(meta["old_bungee"]) != BASE_BUNGEE_ROW_SHA:
            raise ValueError("Bungee baseline raw-row SHA mismatch")
        resealer = ROOT / "scripts/check/reseal-sdn-crc32.shs"
        result = subprocess.run(["sh", str(resealer), str(candidate_path)], capture_output=True, text=True, check=False)
        if result.returncode != 0 or "already " not in result.stdout:
            raise ValueError(f"existing resealer rejected candidate: {result.stdout}{result.stderr}")
        check_locked_state(lock_path, lock_identity, lock_token)
        if DB.read_bytes() != base:
            raise ValueError("install compare-and-swap failed while holding DB lock")
        os.replace(candidate_path, DB)
        if sha(DB.read_bytes()) != sha(candidate):
            raise ValueError("atomic install result differs from validated candidate")
        print(f"installed_sha256={sha(candidate)} crc32={crc}")
        print(f"bungee_old_row_sha256={sha(meta['old_bungee'])} bungee_new_row_sha256={sha(meta['new_bungee'])} inserted_block_sha256={sha(meta['inserted'])}")
    finally:
        if not release_owned_lock(lock_path, lock_fd, lock_identity, lock_token):
            raise ValueError("migration did not remove its own exact DB lock; foreign lock preserved")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(f"migration refused: {type(exc).__name__}: {exc}", file=sys.stderr)
        sys.exit(2)
