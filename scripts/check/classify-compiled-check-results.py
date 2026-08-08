#!/usr/bin/env python3
"""Classify durable results from compiled-check-tree.py into owner routes."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def primary_diagnostic(text: str) -> tuple[int, int, str]:
    match = re.search(
        r"\[parser_error\](?:\s+path\s+.*?)?\s+line\s+(\d+):(\d+):\s*(.+)",
        text,
    )
    if not match:
        return 0, 0, ""
    return int(match.group(1)), int(match.group(2)), match.group(3).strip()


def invalid_source_reason(message: str, source: str, path: str) -> tuple[str, str] | None:
    lower_message = message.lower()
    if "refutable pattern" in lower_message or "var without initializer" in lower_message:
        return "source_contract_violation", "diagnostic states an enforced source contract"
    if "@packed struct fields" in lower_message or "integer literal out of range" in lower_message:
        return "source_contract_violation", "diagnostic states an enforced representation/literal contract"
    if "use # for comments" in lower_message or "unterminated string" in lower_message:
        return "source_lexical_error", "source contains a rejected comment or unterminated literal"
    if "expected string literal in asm block" in lower_message:
        return "source_asm_syntax", "asm operand uses foreign compiler syntax"
    if source.startswith("from ") or source.startswith("import "):
        return "source_foreign_import_syntax", "Python-style import in a .spl source"
    if "//" in source:
        return "source_foreign_comment_syntax", "C/Rust-style comment in a .spl source"
    if re.search(r"fn\s+\w+<[^>]+><", source) or re.search(r"(?:class|fn)\s+\w+\[[^]]+\]", source):
        return "source_legacy_generic_syntax", "legacy/square or repeated generic parameter syntax"
    if re.search(r":\s*\*\w", source):
        return "source_foreign_pointer_type", "Rust/C pointer type spelling"
    if "sort_by(|" in source or ".map(|" in source:
        return "source_rust_closure_syntax", "Rust closure spelling in a .spl source"
    if "=>" in source:
        return "source_foreign_match_arrow", "foreign match-arm arrow; Simple uses case blocks"
    if "->" in source and (
        "Result." in source
        or re.match(r"\d+\s*->", source)
        or source.startswith(("Ok(", "Err(", "DmaDir."))
    ):
        return "source_foreign_match_arrow", "Rust-style match arm in a .spl source"
    if " case " in source and ";" in source:
        return "source_inline_match_semicolon", "multiple match arms compressed with semicolons"
    if source in {"else:", "case _:"}:
        return "source_empty_control_body", "empty branch/match arm"
    if " then" in source or (" if " in source and " else " in source and not source.startswith("if ")):
        return "source_foreign_conditional_expression", "foreign inline conditional spelling"
    if source.startswith("if val ==") or source.startswith("if val >") or source.startswith("if val <"):
        return "source_reserved_binding_name", "`val` is parsed as a binding keyword, not an identifier"
    if source.startswith("var fn ") or "self" in source and source.startswith("fn "):
        return "source_legacy_function_syntax", "legacy function modifier/receiver spelling"
    if source.startswith("export ") and " = " in source:
        return "source_export_assignment", "export assignment is not a declaration"
    if re.match(r"(?:struct|class)\s+\w+$", source):
        return "source_incomplete_declaration", "type declaration has no body delimiter"
    if message.endswith("EOF ''"):
        return "source_forward_declaration_without_body", "bodyless function declaration reaches EOF"
    if source.startswith("val result = if ") and " then" in source:
        return "source_foreign_conditional_expression", "foreign then-form conditional"
    if source.startswith("."):
        return "source_foreign_fluent_chain", "leading-dot fluent chain is not a Simple statement"
    if " { " in source and " } else { " in source:
        return "source_foreign_brace_expression", "C/Rust brace-form conditional"
    if source.startswith("val ") and " for _ in " in source:
        return "source_comprehension_syntax", "unsupported comprehension spelling"
    if source.startswith("fn ") and "list[" in source:
        return "source_legacy_type_syntax", "square generic type spelling"
    if path.startswith("src/app/interpreter/") and source.startswith("If {"):
        return "source_rust_enum_variant_syntax", "Rust struct-variant spelling"
    return None


def classify_failure(path: str, text: str, message: str, source: str) -> dict[str, str]:
    if "E-PAR-" in text:
        return {
            "classification": "checker_false_positive",
            "route_key": "checker_raw_text_concurrency_lint",
            "confidence": "high",
            "owner_surface": "src/app/check/main.spl; src/app/cli/check.spl",
            "evidence": "lint matched forbidden text inside its own implementation or canonical rt_pool owner",
        }
    if "E-SSPEC-CHECK" in text:
        return {
            "classification": "invalid_source_for_check_surface",
            "route_key": "sspec_command_block_layout",
            "confidence": "high",
            "owner_surface": "source/test layout owner",
            "evidence": "checker intentionally requires command-block source to run through bin/simple test",
        }
    if "Usage: simple check" in text and path == "src/app/check/main.spl":
        return {
            "classification": "checker_false_positive",
            "route_key": "checker_entry_path_argument_collision",
            "confidence": "high",
            "owner_surface": "src/app/check/main.spl get_cli_args",
            "evidence": "target path equals embedded entry suffix and is discarded as argv prefix",
        }

    invalid = invalid_source_reason(message, source, path)
    if invalid:
        route_key, evidence = invalid
        return {
            "classification": "invalid_source",
            "route_key": route_key,
            "confidence": "high",
            "owner_surface": path,
            "evidence": evidence,
        }

    lower_message = message.lower()
    if path.startswith("src/compiler/85.mdsoc/") and "got =" in lower_message:
        route = "pure_parser_metadata_block_gap"
        evidence = "Rust parser parse_metadata_block explicitly accepts arch/config/metadata key=value blocks"
    elif "m{" in source or "img{" in source:
        route = "pure_parser_custom_block_gap"
        evidence = "Rust parser exposes custom block expressions including m{...}"
    elif source.startswith("if val ") and "." in source and " = " in source:
        route = "pure_parser_enum_if_val_pattern_gap"
        evidence = "Rust parser_patterns supports dotted enum-variant patterns"
    elif "&" in source and ("fn " in source or "Option<&" in source or "match &mut" in source):
        route = "pure_parser_reference_type_gap"
        evidence = "Rust parser_types handles Ampersand reference capabilities"
    elif "[u" in source and ";" in source:
        route = "pure_parser_fixed_array_type_gap"
        evidence = "Rust parser_types explicitly accepts [T; N]"
    elif source.startswith("export "):
        route = "pure_parser_structured_or_keyword_export_gap"
        evidence = "canonical sources use structured/star/keyword-named exports"
    elif "unexpected token in class body" in lower_message or source.startswith(("pub fn ", "pub file:", "type:", "pass:", "after:")):
        route = "pure_parser_class_member_gap"
        evidence = "canonical parser permits keyword method/field names and public members"
    elif "expected type annotation" in lower_message or "expected )" in lower_message or "expected parameter name" in lower_message:
        route = "pure_parser_type_or_multiline_signature_gap"
        evidence = "canonical parser supports reference/function/empty-array types, capabilities, and multiline signatures"
    elif "expected ident, got" in lower_message:
        route = "pure_parser_keyword_identifier_gap"
        evidence = "Rust parser helper accepts contextual keywords as method/field names"
    elif "expected :, got =" in lower_message or "unexpected token in expression: =" in lower_message:
        route = "pure_parser_assignment_context_gap"
        evidence = "valid metadata/member/destructuring context was parsed as an expression"
    elif "expected :, got fn" in lower_message or "expected ident, got (" in lower_message:
        route = "pure_parser_declaration_boundary_gap"
        evidence = "valid following declaration/destructuring was consumed by the previous construct"
    elif "dedent" in lower_message:
        route = "pure_parser_dedent_context_gap"
        evidence = "isolated canonical source reaches a false expression-at-dedent state"
    elif "expected :, got is" in lower_message:
        route = "pure_parser_type_test_gap"
        evidence = "canonical `is Type` expression rejected"
    elif "unexpected token in expression: *" in lower_message:
        route = "pure_parser_pointer_deref_gap"
        evidence = "canonical raw-pointer dereference rejected"
    elif "unknown(" in lower_message and "..." in source:
        route = "pure_parser_relative_import_gap"
        evidence = "relative import ellipsis token is lexed but not accepted by pure parser"
    elif "expected :, got (" in lower_message and ("m{" in source or "." in source):
        route = "pure_parser_custom_or_method_call_gap"
        evidence = "canonical custom block or method call parsed as a declaration"
    elif "expected =, got (" in lower_message:
        route = "pure_parser_keyword_receiver_gap"
        evidence = "contextual keyword receiver parsed as a declaration"
    elif "expected :, got newline" in lower_message or "unexpected token in expression: newline" in lower_message:
        route = "pure_parser_declaration_newline_gap"
        evidence = "canonical declaration/custom-block boundary rejected at newline"
    else:
        route = "pure_parser_unmatched_surface_gap"
        evidence = "isolated repository source rejected without a proven source-contract violation"
    return {
        "classification": "checker_parser_false_positive",
        "route_key": route,
        "confidence": "medium" if route == "pure_parser_unmatched_surface_gap" else "high",
        "owner_surface": "src/compiler/10.frontend/core parser parity",
        "evidence": evidence,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence-dir", required=True)
    args = parser.parse_args()
    base = Path(args.evidence_dir).resolve()
    file_results_path = base / "file-results.jsonl"
    manifest_path = base / "manifest.tsv"
    if not file_results_path.is_file() or not manifest_path.is_file():
        raise SystemExit("classification requires file-results.jsonl and manifest.tsv")

    manifest = {}
    for raw in manifest_path.read_text(encoding="utf-8").splitlines():
        item_id, digest, path = raw.split("\t")
        manifest[item_id] = {"id": item_id, "source_digest": digest, "path": path}

    routes = Counter()
    classes = Counter()
    actionable = []
    for raw in file_results_path.read_text(encoding="utf-8").splitlines():
        result = json.loads(raw)
        status = result["status"]
        # A nonzero batch only proves that at least one file in the batch
        # failed.  Files that pass when isolated are not actionable failures;
        # the checker's own `files_with_errors` count confirms this.  Never
        # promote aggregate batch membership into a per-file false positive.
        if status != "fail_individual":
            continue
        item_id = result["id"]
        raw_result = json.loads((base / "file" / f"{item_id}.result.json").read_text(encoding="utf-8"))
        stdout = Path(raw_result["stdout"]).read_text(encoding="utf-8", errors="replace")
        stderr = Path(raw_result["stderr"]).read_text(encoding="utf-8", errors="replace")
        combined = stderr + "\n" + stdout
        line_no, column, diagnostic = primary_diagnostic(combined)
        source_path = ROOT / result["path"]
        if source_path.is_file() and sha256_file(source_path) != result["source_digest"]:
            raise SystemExit(f"source changed since sweep: {result['path']}")
        lines = source_path.read_text(encoding="utf-8", errors="replace").splitlines()
        source = lines[line_no - 1].strip() if line_no and line_no <= len(lines) else ""
        classification = classify_failure(result["path"], combined, diagnostic, source)
        row = {
            **manifest[result["id"]],
            "observed_status": status,
            "diagnostic": diagnostic,
            "line": line_no,
            "column": column,
            "source_excerpt": source,
            **classification,
        }
        actionable.append(row)
        routes[row["route_key"]] += 1
        classes[row["classification"]] += 1

    with (base / "routing-manifest.jsonl").open("w", encoding="utf-8") as stream:
        for row in sorted(actionable, key=lambda item: (item["route_key"], item["path"])):
            stream.write(json.dumps(row, sort_keys=True) + "\n")
    summary = {
        "schema_version": 1,
        "evidence_dir": str(base),
        "manifest_digest": sha256_file(manifest_path),
        "manifest_sources": len(manifest),
        "actionable_outcomes": len(actionable),
        "classifications": dict(sorted(classes.items())),
        "routes": dict(sorted(routes.items())),
        "routing_complete": len(actionable) == sum(classes.values()) == sum(routes.values()),
    }
    (base / "routing-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
