#!/usr/bin/env python3
"""Append deterministic RFC 3492 ASCII aliases for Unicode PSL rules."""

from pathlib import Path
import sys


def ascii_domain(rule: str) -> str:
    labels: list[str] = []
    for label in rule.split("."):
        if label.isascii():
            labels.append(label.lower())
        else:
            labels.append("xn--" + label.encode("punycode").decode("ascii"))
    return ".".join(labels)


source, exact_path, wildcard_path, exception_path = map(Path, sys.argv[1:5])
outputs = {
    "exact": exact_path.open("a", encoding="utf-8"),
    "wildcard": wildcard_path.open("a", encoding="utf-8"),
    "exception": exception_path.open("a", encoding="utf-8"),
}
try:
    for raw in source.read_text(encoding="utf-8").splitlines():
        rule = raw.split(" //", 1)[0].strip()
        if not rule or rule.startswith("//"):
            continue
        kind = "exact"
        if rule.startswith("!"):
            kind, rule = "exception", rule[1:]
        elif rule.startswith("*."):
            kind, rule = "wildcard", rule[2:]
        alias = ascii_domain(rule)
        if alias != rule:
            outputs[kind].write(alias + "\n")
finally:
    for output in outputs.values():
        output.close()
