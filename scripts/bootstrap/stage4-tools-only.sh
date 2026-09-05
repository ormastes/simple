#!/bin/sh
# Validate one approved Stage-4 tool journal and atomically publish its output.
set -eu

die() {
  echo "stage4-tools-only: $*" >&2
  exit 1
}

manifest=
journal=
cache=
publish=
tool_id=
entry_path=
linker=cc

for arg in "$@"; do
  case "$arg" in
    --compiler-manifest=*) manifest=${arg#*=} ;;
    --tool-compile-journal=*) journal=${arg#*=} ;;
    --cache-dir=*) cache=${arg#*=} ;;
    --publish-dir=*) publish=${arg#*=} ;;
    --tool-id=*) tool_id=${arg#*=} ;;
    --entry=*) entry_path=${arg#*=} ;;
    --linker=*) linker=${arg#*=} ;;
    *) die "unknown option: $arg" ;;
  esac
done

[ -f "$manifest" ] || die "compiler manifest is required"
[ -f "$journal" ] || die "tool compile journal is required"
case "$cache" in
  build/mini_cache_stage4_*) ;;
  *) die "cache must be a contained Stage-4 mini cache" ;;
esac
case "${cache#build/mini_cache_stage4_}" in
  ''|*/*|*..*) die "invalid cache identity" ;;
esac
case "$publish" in
  build/stage4-tools/*) ;;
  *) die "publish directory must be contained" ;;
esac
case "${publish#build/stage4-tools/}" in
  ''|*/*|*..*) die "invalid publish identity" ;;
esac

case "$tool_id:$entry_path" in
  cli:src/app/cli/main.spl) output_name=simple ;;
  mcp:src/app/mcp/main.spl) output_name=simple_mcp_server ;;
  lsp:src/app/simple_lsp_mcp/main.spl) output_name=simple_lsp_mcp_server ;;
  *) die "unapproved tool identity: $tool_id:$entry_path" ;;
esac

[ ! -e "$publish" ] || die "publish directory already exists"

value() {
  value_file=$1
  value_key=$2
  value_count=$(awk -F= -v key="$value_key" '$1 == key { count++ } END { print count + 0 }' "$value_file")
  [ "$value_count" -eq 1 ] || die "$value_key must occur once"
  sed -n "s/^${value_key}=//p" "$value_file"
}

valid_hash() {
  printf '%s\n' "$1" | grep -Eq '^[0-9a-f]{64}$'
}

hash_file() {
  sha256sum "$1" | awk '{print $1}'
}

verify_file() {
  verify_path=$1
  verify_hash=$2
  verify_label=$3
  [ -f "$verify_path" ] || die "$verify_label missing"
  valid_hash "$verify_hash" || die "$verify_label hash invalid"
  [ "$(hash_file "$verify_path")" = "$verify_hash" ] || die "$verify_label hash mismatch"
}

schema=$(value "$manifest" schema_version)
[ "$schema" = CompilerArtifactManifestV1 ] || die "manifest schema"
source_hash=$(value "$manifest" source_hash)
producer_hash=$(value "$manifest" producer_hash)
backend=$(value "$manifest" backend)
[ -n "$backend" ] || die "Stage3 backend identity required"
target=$(value "$manifest" target)
compiler_abi=$(value "$manifest" compiler_abi)
runtime_abi=$(value "$manifest" runtime_abi)
identity=$(value "$manifest" compiler_identity)
case "$identity" in
  ''|*Rust-built*|*'bootstrap seed only'*) die "admitted pure-Simple Stage3 identity required" ;;
esac

admission=$(value "$manifest" admission_receipt_path)
admission_hash=$(value "$manifest" admission_receipt_hash)
compiler_exe=$(value "$manifest" compiler_executable_path)
compiler_exe_hash=$(value "$manifest" compiler_executable_hash)
compiler_archive=$(value "$manifest" compiler_archive_path)
compiler_archive_hash=$(value "$manifest" compiler_archive_hash)
compiler_interface=$(value "$manifest" compiler_interface_path)
compiler_interface_hash=$(value "$manifest" compiler_interface_hash)
runtime_archive=$(value "$manifest" runtime_archive_path)
runtime_archive_hash=$(value "$manifest" runtime_archive_hash)

valid_hash "$source_hash" && valid_hash "$producer_hash" || die "provenance hash invalid"
verify_file "$admission" "$admission_hash" admission
verify_file "$compiler_exe" "$compiler_exe_hash" executable
verify_file "$compiler_archive" "$compiler_archive_hash" compiler_archive
verify_file "$compiler_interface" "$compiler_interface_hash" interface
verify_file "$runtime_archive" "$runtime_archive_hash" runtime
[ "$(value "$admission" schema_version)" = Stage3AdmissionReceiptV1 ] || die "Stage3 admission schema"
[ "$(value "$admission" admission_status)" = PASS ] || die "Stage3 not admitted"
[ "$(value "$admission" compiler_identity)" = "$identity" ] || die "admission identity mismatch"
for key in backend compiler_executable_hash compiler_archive_hash compiler_interface_hash runtime_archive_hash target compiler_abi runtime_abi; do
  [ "$(value "$manifest" "$key")" = "$(value "$admission" "$key")" ] || die "admission mismatch $key"
done

mkdir -p "$cache" "$(dirname "$publish")"
canonical="$cache/manifest.canonical"
: >"$canonical"
frame() {
  frame_name=$1
  frame_value=$2
  frame_file=$3
  name_len=$(printf %s "$frame_name" | wc -c | tr -d ' ')
  value_len=$(printf %s "$frame_value" | wc -c | tr -d ' ')
  printf '%s:%s%s:%s' "$name_len" "$frame_name" "$value_len" "$frame_value" >>"$frame_file"
}
for pair in \
  "schema=$schema" "source=$source_hash" "producer=$producer_hash" \
  "backend=$backend" "target=$target" "compiler_abi=$compiler_abi" \
  "runtime_abi=$runtime_abi" "compiler_identity=$identity" \
  "admission_receipt_path=$admission" "admission_receipt_hash=$admission_hash" \
  "compiler_executable_path=$compiler_exe" "compiler_executable_hash=$compiler_exe_hash" \
  "compiler_archive_path=$compiler_archive" "compiler_archive_hash=$compiler_archive_hash" \
  "compiler_interface_path=$compiler_interface" "compiler_interface_hash=$compiler_interface_hash" \
  "runtime_archive_path=$runtime_archive" "runtime_archive_hash=$runtime_archive_hash"; do
  frame "${pair%%=*}" "${pair#*=}" "$canonical"
done
manifest_hash=$(hash_file "$canonical")

[ "$(value "$journal" schema_version)" = ToolCompileJournalV1 ] || die "journal schema"
[ "$(value "$journal" tool_id)" = "$tool_id" ] || die "journal tool mismatch"
[ "$(value "$journal" entry_path)" = "$entry_path" ] || die "journal entry mismatch"
[ "$(value "$journal" compiler_manifest_hash)" = "$manifest_hash" ] || die "journal manifest mismatch"
[ "$(value "$journal" compiler_executable_hash)" = "$compiler_exe_hash" ] || die "journal compiler mismatch"
[ "$(value "$journal" source_hash)" = "$source_hash" ] || die "journal source mismatch"
[ "$(value "$journal" producer_hash)" = "$producer_hash" ] || die "journal producer mismatch"
[ "$(value "$journal" backend)" = "$backend" ] || die "journal backend mismatch"
[ "$(value "$journal" target)" = "$target" ] || die "journal target mismatch"
[ "$(value "$journal" compiler_abi)" = "$compiler_abi" ] || die "journal compiler ABI mismatch"
[ "$(value "$journal" runtime_abi)" = "$runtime_abi" ] || die "journal runtime ABI mismatch"
[ "$(value "$journal" compiler_archive_hash)" = "$compiler_archive_hash" ] || die "journal compiler archive mismatch"
[ "$(value "$journal" compiler_interface_hash)" = "$compiler_interface_hash" ] || die "journal compiler interface mismatch"
[ "$(value "$journal" runtime_archive_hash)" = "$runtime_archive_hash" ] || die "journal runtime archive mismatch"
[ "$(value "$journal" compiler_sources_compiled)" = 0 ] || die "journal compiled compiler sources"
[ "$(value "$journal" stage4_compiler_files)" = 0 ] || die "journal Stage4 compiler files"

objects="$cache/objects"
sources="$cache/sources"
: >"$objects"
: >"$sources"
unit_count=0
entry_source_hash=
entry_object_hash=
tab=$(printf '\t')
while IFS="$tab" read -r kind source_path source_sha object_path object_sha extra; do
  [ "$kind" = unit ] || continue
  [ -z "${extra:-}" ] || die "bad unit row"
  case "$source_path" in
    /*|../*|*/../*|*//*|src/compiler|src/compiler/*|./src/compiler|./src/compiler/*)
      die "compiler traversal"
      ;;
    src/app/*|src/lib/*|./src/app/*|./src/lib/*) ;;
    *) die "unowned source" ;;
  esac
  verify_file "$source_path" "$source_sha" source
  verify_file "$object_path" "$object_sha" object
  grep -Fqx "$source_path" "$sources" && die "duplicate source"
  grep -Fqx "$object_path" "$objects" && die "duplicate object"
  printf '%s\n' "$source_path" >>"$sources"
  printf '%s\n' "$object_path" >>"$objects"
  normalized_source=${source_path#./}
  if [ "$normalized_source" = "$entry_path" ]; then
    entry_source_hash=$source_sha
    entry_object_hash=$object_sha
  fi
  unit_count=$((unit_count + 1))
done <"$journal"
[ "$unit_count" -gt 0 ] || die "empty journal"
[ -n "$entry_source_hash" ] || die "journal does not contain the approved entry source"
source_set_hash=$(hash_file "$sources")
object_set_hash=$(hash_file "$objects")

publish_parent=$(dirname "$publish")
publish_name=$(basename "$publish")
staging="$publish_parent/.${publish_name}.tmp.$$"
trap 'rm -rf "$staging"' EXIT INT TERM HUP
mkdir "$staging"
set --
while IFS= read -r object_path; do
  set -- "$@" "$object_path"
done <"$objects"
"$linker" -o "$staging/$output_name" "$@" "$compiler_archive" "$runtime_archive"
[ -s "$staging/$output_name" ] || die "empty output"

output_hash=$(hash_file "$staging/$output_name")
journal_hash=$(hash_file "$journal")
receipt="$staging/ToolingLinkReceiptV1.env"
{
  echo "schema_version=ToolingLinkReceiptV1"
  echo "tool_id=$tool_id"
  echo "entry_path=$entry_path"
  echo "compiler_manifest_hash=$manifest_hash"
  echo "compiler_manifest_file_hash=$(hash_file "$manifest")"
  echo "source_hash=$source_hash"
  echo "producer_hash=$producer_hash"
  echo "backend=$backend"
  echo "target=$target"
  echo "compiler_identity=$identity"
  echo "compiler_executable_hash=$compiler_exe_hash"
  echo "compiler_archive_hash=$compiler_archive_hash"
  echo "compiler_interface_hash=$compiler_interface_hash"
  echo "runtime_archive_hash=$runtime_archive_hash"
  echo "compiler_abi=$compiler_abi"
  echo "runtime_abi=$runtime_abi"
  echo "tool_compile_journal_hash=$journal_hash"
  echo "compiled_unit_count=$unit_count"
  echo "source_set_hash=$source_set_hash"
  echo "object_set_hash=$object_set_hash"
  echo "entry_source_hash=$entry_source_hash"
  echo "entry_object_hash=$entry_object_hash"
  echo "compiler_sources_compiled=0"
  echo "stage4_compiler_files=0"
  echo "output_path=$publish/$output_name"
  echo "output_hash=$output_hash"
  echo "help_smoke_passed=false"
  echo "version_smoke_passed=false"
} >"$receipt"
mv "$staging" "$publish"
trap - EXIT INT TERM HUP
echo "Stage4 tools-only PASS tool_id=$tool_id stage4_compiler_files=0"
