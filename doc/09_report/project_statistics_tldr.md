# Project Statistics — TLDR

Latest [checkout LOC report, 2026-11-24](project_loc_2026-11-24.md): **84,587
files**, **25,736,032 code/data lines**, **2,385,390 comments**, and **1,685,357
blank lines**, totaling **29,806,779 physical lines**. Includes tracked Simple,
SHS, SDN, C/headers, Rust, and Python files, submodules, vendored code, tests,
and fixtures. SDN lines are data. This is not a build/test qualification.

The following owned-code portfolio is the **historical 2026-08-13 inventory**;
its vendor-excluding scope differs from the November report.

| Portfolio | Value |
|---|---:|
| Owned source/test files | 41,544 |
| Owned source/test SLOC | 7,307,459 |
| Source SLOC | 4,767,640 |
| Project test SLOC | 2,539,819 |
| Runnable test SLOC including Markdown/comments | 3,187,596 |
| Markdown files excluding TLDR | 17,897 |

Largest owned areas by SLOC are app (2.48M), lib/std/core (1.38M), compiler (1.32M), and verification tests (1.06M). Coverage, duplication, coupling, and cohesion are unavailable because retained artifacts contain no current measurements. The nine-slide SimpleOS-themed PPTX is generated and package-validated.

Cross-cutting product views include UI/rendering (293,796 SLOC), Web Browser
(178,495), Agent Caret (91,525), Office (50,930), SPipe (49,383), DB server (2,892), Agents Manager
(2,148), Web server (2,078), and CRM (84). These views overlap project totals.
