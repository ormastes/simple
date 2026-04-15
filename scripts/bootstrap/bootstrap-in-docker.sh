#!/bin/sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "${script_dir}/../.." && pwd)
image_name="${SIMPLE_BOOTSTRAP_IMAGE:-simple-bootstrap:latest}"

if ! command -v docker >/dev/null 2>&1; then
  echo "error: docker is required for bootstrap-in-docker.sh" >&2
  exit 1
fi

build_image=1
run_args=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --no-build)
      build_image=0
      ;;
    *)
      escaped_arg=$(printf "%s" "$1" | sed "s/'/'\\\\''/g")
      run_args="${run_args} '${escaped_arg}'"
      ;;
  esac
  shift
done

if [ "${build_image}" -eq 1 ]; then
  echo "Building bootstrap image: ${image_name}"
  docker build -t "${image_name}" -f "${repo_root}/tools/docker/Dockerfile.bootstrap" "${repo_root}/tools/docker"
fi

echo "Running bootstrap in Docker"
exec docker run --rm \
  -v "${repo_root}:/workspace" \
  -w /workspace \
  "${image_name}" \
  bash -lc "set -eu; scripts/bootstrap/bootstrap-from-scratch.sh --deploy${run_args}"
