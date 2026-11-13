#!/usr/bin/env python3
# Faithful model of native_build_module_environment_snapshot_fingerprint_v1
# (src/compiler/80.driver/cache/native_build_environment_identity.spl) used to
# verify the resource-budget exclusion change without a Simple runtime.
# Mirrors: complete capture (all present SIMPLE_* pairs -> "present|len:name|len:value"
# rows; absent rows for SEMANTIC fields), then the module projection drop-list,
# then sha256 over the sorted, length-framed rows.
import hashlib

SCHEMA = "simple-native-build-environment-v1"
SEMANTIC = ["AR","BOOTSTRAP_MINIMAL","BOOTSTRAP_NO_C","BOOTSTRAP_NO_EVAL","BOOTSTRAP_NO_GPU","CC","CFLAGS","CPATH","CPPFLAGS","CXX","DEVELOPER_DIR","DYLD_LIBRARY_PATH","HOMEBREW_PREFIX","LANG","LC_ALL","LD","LDFLAGS","LIBRARY_PATH","MACOSX_DEPLOYMENT_TARGET","MSYSTEM","NM","OBJCOPY","OBJDUMP","OS","PATH","PKG_CONFIG_PATH","PWD","SDKROOT","SIMPLE_ABI_ADMISSION_RECEIPT","SIMPLE_ABI_POLICY","SIMPLE_ACTION_ABI_DIGEST","SIMPLE_ALLOW_UNLOWERED_MIR","SIMPLE_AR","SIMPLE_BINARY","SIMPLE_BOOTSTRAP","SIMPLE_BOOTSTRAP_AUTHORITY_DIGEST","SIMPLE_BOOTSTRAP_DEBUG","SIMPLE_BOOTSTRAP_DIRECT_STUB_IR","SIMPLE_BOOTSTRAP_EMPTY_NATIVE_OBJ","SIMPLE_BOOTSTRAP_LOW_MEMORY","SIMPLE_BOOTSTRAP_REAL_LLVM","SIMPLE_BOOTSTRAP_SKIP_MIR_LOWER","SIMPLE_BOOTSTRAP_STAGE4","SIMPLE_CACHE_SCOPE","SIMPLE_CC","SIMPLE_COMPILER_ARTIFACT_OWNER","SIMPLE_COMPILER_ARTIFACT_SERVICE_AVAILABLE","SIMPLE_COMPILER_DIGEST","SIMPLE_COVERAGE","SIMPLE_COMPILE_DELEGATED","SIMPLE_COMPILE_FAIL_FAST","SIMPLE_CORE_RUNTIME_PATH","SIMPLE_CRT0_PATH","SIMPLE_DETERMINISTIC","SIMPLE_FORCE_ARGS","SIMPLE_FRONTEND_CACHE","SIMPLE_FRONTEND_CACHE_DIR","SIMPLE_FRONTEND_CACHE_SCOPE","SIMPLE_HIR_CACHE","SIMPLE_HIR_CACHE_DIR","SIMPLE_HIR_CODEC_ROUNDTRIP","SIMPLE_HIR_SHARD","SIMPLE_HIR_SHARD_QUEUE","SIMPLE_HIR_SHARDING","SIMPLE_LIBC_PATH","SIMPLE_LINKER","SIMPLE_LINKER_FLAVOR","SIMPLE_LINKER_SCRIPT","SIMPLE_LINK_OBJECTS","SIMPLE_LLVM_BITCODE_DEBUG","SIMPLE_M4_WORK_RECEIPT","SIMPLE_MCDC_EXCLUDE","SIMPLE_MCDC_GLOBAL_BYTES","SIMPLE_MCDC_INCLUDE","SIMPLE_MCDC_MODE","SIMPLE_MCDC_OWNER_BYTES","SIMPLE_MIR_BULK_OPS","SIMPLE_MIR_VERIFY_EACH","SIMPLE_NATIVE_ARENA_DECLS","SIMPLE_NATIVE_BUILD_CACHE_DIR","SIMPLE_NATIVE_BUILD_CLEAN","SIMPLE_NATIVE_BUILD_EMIT_OBJECT","SIMPLE_NATIVE_BUILD_ENTRY","SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE","SIMPLE_NATIVE_BUILD_LINKER_SCRIPT","SIMPLE_NATIVE_BUILD_NO_MANGLE","SIMPLE_NATIVE_BUILD_TARGET","SIMPLE_NATIVE_BUILD_THREADS","SIMPLE_NATIVE_BUILD_TRACE_CLOSURE","SIMPLE_NATIVE_CPU","SIMPLE_NATIVE_RUNTIME_BUNDLE","SIMPLE_NM","SIMPLE_NO_STUB_FALLBACK","SIMPLE_OBJCOPY","SIMPLE_OBJDUMP","SIMPLE_PACKAGE_INDEX_CHANGED_MODULES","SIMPLE_PACKAGE_INDEX_COLD_INIT","SIMPLE_PACKAGE_INDEX_PRODUCER_DIGEST","SIMPLE_PACKAGE_INDEX_PUBLIC_INTERFACE_CHANGED","SIMPLE_PACKAGE_INDEX_ROOT_GENERATION","SIMPLE_PACKAGE_INDEX_VARIANT_DIGEST","SIMPLE_PARSE_SHARD","SIMPLE_PARSE_SHARD_QUEUE","SIMPLE_PHASE2_COMPATIBILITY_MANIFEST_READ","SIMPLE_PHASE3_COMPATIBILITY_CACHE_ROOT","SIMPLE_PROJECT_ROOT","SIMPLE_RT_OBJ_CACHE","SIMPLE_RT_OBJ_CACHE_DIR","SIMPLE_RUNTIME_ABI_DIGEST","SIMPLE_RUNTIME_ACTION_DIGEST","SIMPLE_RUNTIME_BINARY","SIMPLE_RUNTIME_PATH","SIMPLE_RUNTIME_RISCV64_VECTOR","SIMPLE_SAFETY_PROFILE","SIMPLE_SAFETY_WARN","SIMPLE_SCV_INVENTORY_DIGEST","SIMPLE_SCV_INVENTORY_GENERATION","SIMPLE_SCV_REVISION","SIMPLE_SCV_REVISION_ID","SIMPLE_SCV_SNAPSHOT_ROOT","SIMPLE_SCV_SOURCE_INVENTORY_DIGEST","SIMPLE_SCV_TREE_DIGEST","SIMPLE_SCV_TREE_ID","SIMPLE_SIMPLE_CORE_PATH","SIMPLE_STDLIB_ABI_DIGEST","SIMPLE_STDLIB_ACTION_DIGEST","SIMPLE_STRICT_ARRAY_GLOBALS","SIMPLE_STUB_HIR","SIMPLE_SYSROOT","SIMPLE_TARGET","SIMPLE_TYPECHECK_PROFILE","SIMPLE_TYPECHECK_WARN","SIMPLE_UNSTABLE_BUILD","SIMPLE_UNSTUB_HIR","SIMPLE_WINDOWS_ABI","SIMPLEOS_SYSROOT"]

# Pre-change drop list (module projection), reconstructed from git show
# fef2112684e:f40086fb16f:c458ffe5cbc of native_build_environment_identity.spl.
DROP_BEFORE = {
    "SIMPLE_MIR_SHARDING","SIMPLE_MIR_SHARD","SIMPLE_MIR_SHARD_QUEUE","SIMPLE_MIR_SHARD_OWNER",
    "SIMPLE_MIR_SHARD_LINK","SIMPLE_MIR_SHARD_WORKER_KB","SIMPLE_MIR_SHARD_COUNT",
    "SIMPLE_MIR_SHARD_ONLY_PATHS","SIMPLE_MIR_FORK_WORKERS","SIMPLE_SHARD_MEM_CLAMP",
    "SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB","SIMPLE_MIR_SHARD_EXPORT_DIR",
    "SIMPLE_MIR_SHARD_EXPORT_WRITE","SIMPLE_MIR_SHARD_EXPORT_SUMMARIES",
    "SIMPLE_MIR_SELECTIVE_PARENT_KIB","SIMPLE_MIR_SELECTIVE_WORKER_KIB",
    "SIMPLE_MIR_SELECTIVE_EXPORTER_KIB","SIMPLE_MIR_SELECTIVE_PHASE_KIB",
    "SIMPLE_MIR_SELECTIVE_DISK_BYTES","SIMPLE_MIR_SELECTIVE_DISK_RESERVE_BYTES",
    "SIMPLE_NATIVE_STAGED_CODEGEN_BATCH","SIMPLE_NATIVE_PRELOWER_CACHE",
    "SIMPLE_NATIVE_GO_TO_END","SIMPLE_ICE_SKIP_MODULES",
    "SIMPLE_COMPILER_PHASE_PROFILE","SIMPLE_COMPILER_PHASE_PROFILE_FILE",
    "SIMPLE_MEM_SNAPSHOT_FILE","SIMPLE_EVIDENCE_RUN_ID","SIMPLE_BUILD_PROGRESS_EVENTS",
    "SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB","SIMPLE_ICE_DIR",
    "SIMPLE_NATIVE_BUILD_WARM_CLOSURE_CANDIDATE",
}
# Post-change drop list = DROP_BEFORE + the #8920 additions + this change's
# additions (start-guard reserve sizing and host-config path selection; both
# are pre-admitted resource knobs that reach no compiler decision).
DROP_AFTER = DROP_BEFORE | {
    "SIMPLE_PARSE_SHARD_WORKER_KB","SIMPLE_HIR_SHARD_WORKER_KB",
    "SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP","SIMPLE_PROCESS_TREE_RSS_DECLARED_JOBS",
    "SIMPLE_PROCESS_TREE_RSS_RECEIPT","SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB",
    "SIMPLE_PROCESS_TREE_RSS_CAP_KIB","SIMPLE_BOOTSTRAP_RSS_CAP_MODE",
    "SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS",
    "SIMPLE_BUILD_MEMORY_RESERVE_BYTES","SIMPLE_HOST_CONFIG",
}

def complete_rows(snapshot):
    observed = {}
    rows = []
    for name, value in snapshot:
        assert name not in observed, name
        observed[name] = value
        if name.startswith("SIMPLE_"):
            rows.append(f"present|{len(name)}:{name}|{len(value)}:{value}")
    for name in SEMANTIC:
        if name in observed:
            if not name.startswith("SIMPLE_"):
                rows.append(f"present|{len(name)}:{name}|{len(observed[name])}:{observed[name]}")
        else:
            rows.append(f"absent|{len(name)}:{name}")
    return sorted(rows)

def frame(rows):
    out = f"{len(SCHEMA)}:{SCHEMA}{len(rows)};"
    for row in rows:
        out += f"{len(row)}:{row}"
    return out

def complete_digest(snapshot):
    return hashlib.sha256(frame(complete_rows(snapshot)).encode()).hexdigest()

def module_digest(snapshot, drop):
    projected = [(n, v) for n, v in snapshot if n not in drop]
    inner = complete_digest(projected)
    return hashlib.sha256(("simple-native-module-environment-v1\n" + inner).encode()).hexdigest()

BASE = [("PATH", "/usr/bin")]
RUN_A = BASE + [("SIMPLE_SHARD_MEM_CLAMP","1"),("SIMPLE_PARSE_SHARD_WORKER_KB","3800000"),
    ("SIMPLE_HIR_SHARD_WORKER_KB","9000000"),("SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB","14680064"),
    ("SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB","62914560"),
    ("SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP","row-101"),("SIMPLE_PROCESS_TREE_RSS_RECEIPT","r-101"),
    ("SIMPLE_BOOTSTRAP_RSS_CAP_MODE","enforce"),("SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS","250"),
    ("SIMPLE_BUILD_MEMORY_RESERVE_BYTES","1073741824"),
    ("SIMPLE_HOST_CONFIG","/home/me/.config/simple/host.sdn")]
RUN_B = BASE + [("SIMPLE_SHARD_MEM_CLAMP","1"),("SIMPLE_PARSE_SHARD_WORKER_KB","3800000"),
    ("SIMPLE_HIR_SHARD_WORKER_KB","9000000"),("SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB","11534336"),
    ("SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB","11534336"),
    ("SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP","row-202"),("SIMPLE_PROCESS_TREE_RSS_RECEIPT","r-202"),
    ("SIMPLE_BOOTSTRAP_RSS_CAP_MODE","enforce"),("SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS","250"),
    ("SIMPLE_BUILD_MEMORY_RESERVE_BYTES","12884901888"),
    ("SIMPLE_HOST_CONFIG","/home/me/.config/simple/host.sdn")]
RUN_C = BASE + [("SIMPLE_SHARD_MEM_CLAMP","1"),("SIMPLE_PARSE_SHARD_WORKER_KB","2500000"),
    ("SIMPLE_HIR_SHARD_WORKER_KB","7000000"),("SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB","13631488"),
    ("SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB","14680064"),
    ("SIMPLE_PROCESS_TREE_RSS_SCOPE_GROUP","row-303"),("SIMPLE_PROCESS_TREE_RSS_RECEIPT","r-303"),
    ("SIMPLE_BOOTSTRAP_RSS_CAP_MODE","off"),("SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS","500"),
    ("SIMPLE_BUILD_MEMORY_RESERVE_BYTES","1073741824"),
    ("SIMPLE_HOST_CONFIG","/alt/host.sdn")]
SEMANTIC_CHANGE = BASE + [("SIMPLE_NATIVE_ARENA_DECLS","1")]
THREADS_CHANGE = BASE + [("SIMPLE_NATIVE_BUILD_THREADS","8")]

fails = []
def check(label, cond):
    print(("PASS " if cond else "FAIL ") + label)
    if not cond: fails.append(label)

for label, drop in (("BEFORE fix", DROP_BEFORE), ("AFTER fix", DROP_AFTER)):
    print(f"== {label}")
    base = module_digest(BASE, drop)
    same_kb = module_digest(RUN_A, drop) == module_digest(RUN_B, drop)
    reuse_across_kb = module_digest(RUN_A, drop) == module_digest(RUN_C, drop)
    if label == "BEFORE fix":
        # Watchdog scope group / receipt / cap and the worker-KB budgets were
        # all unexcluded, so any retuned run got a private object scope.
        check("run A != run B (watchdog coords unexcluded)", not same_kb)
        check("run A != run C when worker-KB budgets differ (the bug)",
              not reuse_across_kb)
    else:
        check("run A == run B (watchdog coords excluded)", same_kb)
        check("run A == run C when worker-KB budgets differ (fixed)",
              reuse_across_kb)
        check("resource runs all share the bare baseline scope",
              module_digest(RUN_B, drop) == base and module_digest(RUN_C, drop) == base)
    check("semantics flag still moves the module scope",
          module_digest(SEMANTIC_CHANGE, drop) != base)
    check("--threads still moves the module scope (kept hashed)",
          module_digest(THREADS_CHANGE, drop) != base)
    check("complete capture still records the knobs",
          complete_digest(RUN_A) != complete_digest(RUN_B))

print("RESULT:", "FAIL" if fails else "PASS")
raise SystemExit(1 if fails else 0)
