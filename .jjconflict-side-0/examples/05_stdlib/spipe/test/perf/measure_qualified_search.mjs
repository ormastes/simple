#!/usr/bin/env node
// P11 — measureQualifiedSearch, the sole qualified-performance collection
// entry point (design doc §14.6.2). Frozen signature (by flag, not
// positional, for clarity — semantics match the design's five-argument
// signature exactly):
//
//   node measure_qualified_search.mjs \
//     --profile <path> --fixture <path> --operation-plan <path> \
//     --functional-receipt <file://...> --output <path>
//
// Env: SPIPE_SIMPLE_BIN (absolute admitted simple binary),
//      SPIPE_STAGE4_PROVENANCE (absolute admitted stage4 provenance record).
//
// This harness is ADMISSION-FIRST and FAIL-CLOSED: it verifies every
// precondition the design requires (absolute canonical non-symlink paths,
// an admitted Stage 4 binary + provenance pair, schema-valid profile/fixture/
// operation-plan JSON) before it would ever measure anything. On this host,
// as of this design freeze, no admitted Stage 4 executable/provenance pair
// exists (§14.6.2: "Because no admitted Stage 4 executable exists at this
// design freeze, W4-SRCH-09 remains NOT EVIDENCE; no seed or source-mode run
// can satisfy it."). So this harness's expected, honest outcome on this host
// is a typed `not_evidence` diagnostic on stderr, NO receipt written, any
// temporary output removed, and a nonzero exit status. Fabricating a PASS
// here would violate the design contract outright.
"use strict";

import { existsSync, lstatSync, realpathSync, unlinkSync } from "node:fs";
import { isAbsolute } from "node:path";

function parseArgs(argv) {
    const out = {};
    for (let i = 0; i < argv.length; i += 1) {
        const tok = argv[i];
        if (tok.startsWith("--")) {
            const key = tok.slice(2);
            const val = argv[i + 1];
            out[key] = val;
            i += 1;
        }
    }
    return out;
}

function notEvidence(reason, detail) {
    const diagnostic = {
        schema: "spipe-qualified-search-not-evidence-v1",
        status: "not_evidence",
        reason,
        detail: detail ?? null,
        design_reference:
            "spipe_knowledge_compiler_search_providers.md#14.6.2",
        timestamp_utc: new Date().toISOString(),
    };
    process.stderr.write(JSON.stringify(diagnostic, null, 2) + "\n");
    return diagnostic;
}

function isCanonicalAbsoluteNonSymlink(p) {
    if (typeof p !== "string" || p.length === 0) return false;
    if (!isAbsolute(p)) return false;
    if (!existsSync(p)) return false;
    try {
        const st = lstatSync(p);
        if (st.isSymbolicLink()) return false;
        const real = realpathSync(p);
        return real === p;
    } catch {
        return false;
    }
}

function main() {
    const args = parseArgs(process.argv.slice(2));
    const required = [
        "profile",
        "fixture",
        "operation-plan",
        "functional-receipt",
        "output",
    ];
    for (const key of required) {
        if (!args[key]) {
            notEvidence("missing_required_argument", { argument: key });
            return 2;
        }
    }

    // functional-receipt is a canonical file:// URI resolving to an absolute
    // nonsymlink path; every other path argument is a plain absolute path.
    let functionalReceiptPath = null;
    if (args["functional-receipt"].startsWith("file://")) {
        functionalReceiptPath = args["functional-receipt"].slice(
            "file://".length,
        );
    } else {
        notEvidence("functional_receipt_not_file_uri", {
            value: args["functional-receipt"],
        });
        return 2;
    }

    const pathArgs = {
        profile: args.profile,
        fixture: args.fixture,
        "operation-plan": args["operation-plan"],
        "functional-receipt": functionalReceiptPath,
        output: args.output,
    };

    // `output` need not exist yet (it is what we would write), but every
    // input must be an absolute, canonical, non-symlink path that exists.
    for (const [name, p] of Object.entries(pathArgs)) {
        if (!isAbsolute(p)) {
            notEvidence("path_not_absolute", { argument: name, value: p });
            return 2;
        }
        if (name === "output") continue;
        if (!isCanonicalAbsoluteNonSymlink(p)) {
            notEvidence("path_not_admitted_canonical_nonsymlink", {
                argument: name,
                value: p,
            });
            cleanupTemporaryOutput(args.output);
            return 2;
        }
    }

    // Stage 4 admission: SPIPE_SIMPLE_BIN and SPIPE_STAGE4_PROVENANCE must
    // both name an admitted, absolute, canonical, non-symlink artifact.
    const simpleBin = process.env.SPIPE_SIMPLE_BIN;
    const stage4Provenance = process.env.SPIPE_STAGE4_PROVENANCE;
    if (!simpleBin || !stage4Provenance) {
        notEvidence("stage4_admission_env_missing", {
            SPIPE_SIMPLE_BIN: simpleBin ?? null,
            SPIPE_STAGE4_PROVENANCE: stage4Provenance ?? null,
            design_statement:
                "Because no admitted Stage 4 executable exists at this " +
                "design freeze, W4-SRCH-09 remains NOT EVIDENCE; no seed " +
                "or source-mode run can satisfy it.",
        });
        cleanupTemporaryOutput(args.output);
        return 1;
    }
    if (
        !isCanonicalAbsoluteNonSymlink(simpleBin) ||
        !isCanonicalAbsoluteNonSymlink(stage4Provenance)
    ) {
        notEvidence("stage4_admission_paths_invalid", {
            SPIPE_SIMPLE_BIN: simpleBin,
            SPIPE_STAGE4_PROVENANCE: stage4Provenance,
        });
        cleanupTemporaryOutput(args.output);
        return 1;
    }

    // Even with a syntactically-admitted pair, this harness performs no
    // independent Stage 4 provenance verification of its own (that verifier
    // is a separate canonical component per §14.6.2, not reimplemented here)
    // — so it never fabricates a receipt from this point either. Any run
    // that reaches here on THIS repository's current state is still
    // NOT EVIDENCE, because no such verifier/candidate pair has been
    // reviewed and admitted for Wave 4 as of this design freeze.
    notEvidence("stage4_provenance_verification_unavailable", {
        SPIPE_SIMPLE_BIN: simpleBin,
        SPIPE_STAGE4_PROVENANCE: stage4Provenance,
        design_statement:
            "No seed or source-mode run can satisfy W4-SRCH-09 until a " +
            "reviewed Stage 4 provenance verifier and an admitted " +
            "candidate both exist.",
    });
    cleanupTemporaryOutput(args.output);
    return 1;
}

function cleanupTemporaryOutput(outputPath) {
    if (!outputPath) return;
    try {
        if (existsSync(outputPath)) unlinkSync(outputPath);
    } catch {
        // best-effort cleanup only
    }
}

process.exit(main());
