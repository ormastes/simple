#!/usr/bin/env node
'use strict';

// Exercise the workflow's actual shell commands without building a compiler or
// starting Docker/Podman. The fake engine preserves the image's Bash entrypoint.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { spawnSync } = require('node:child_process');

const root = path.resolve(__dirname, '../..');
const workflow = fs.readFileSync(path.join(root, '.github/workflows/containerized-tests.yml'), 'utf8');
const dockerfile = fs.readFileSync(path.join(root, 'tools/docker/Dockerfile.test-isolation'), 'utf8');
assert.match(dockerfile, /^ENTRYPOINT \["\/bin\/bash"\]\r?$/m);
const commands = [...workflow.matchAll(/^        (?:docker|podman) run --rm \\\n(?:.*\\\n)*.*$/gm)]
  .map(match => match[0])
  .filter(command => /\n\s+test /.test(command));
assert.equal(commands.length, 8, 'exercise all discovery and resource-limit invocations');

const temporary = fs.mkdtempSync(path.join(os.tmpdir(), 'simple-container-invocation-'));
try {
  fs.mkdirSync(path.join(temporary, 'test'));
  const runtime = path.join(temporary, 'fake-simple');
  fs.writeFileSync(runtime, '#!/bin/sh\nprintf "%s\\n" "$@"\nexit "${FAKE_RUNTIME_EXIT:-0}"\n', { mode: 0o755 });
  const engine = `
docker() {
  while [ "$#" -gt 0 ]; do
    case "$1" in simple-test-isolation:*) shift; break;; esac
    shift
  done
  /bin/bash "$@"
}
podman() { docker "$@"; }
`;
  const run = (command, exitCode = 0) => spawnSync('/bin/bash', ['-c', engine + command], {
    cwd: temporary,
    encoding: 'utf8',
    env: { ...process.env, FAKE_RUNTIME_EXIT: String(exitCode) },
  });
  const broken = run('docker run --rm simple-test-isolation:fixture test test/example.spl --list');
  assert.equal(broken.status, 126, 'reproduce Bash opening the test directory');
  assert.match(broken.stderr, /is a directory/i);

  for (const command of commands) {
    const expanded = command
      .replaceAll('${{ github.sha }}', 'fixture')
      .replaceAll('${{ matrix.path }}', 'test/matrix_spec.spl')
      .replaceAll('/workspace/bin/release/x86_64-unknown-linux-gnu/simple', runtime);
    const target = expanded.match(/\n\s+test (\S+)/)[1];
    const expected = ['test', target, '--list', '--no-db', '--no-cover-check'];
    const success = run(expanded);
    assert.equal(success.status, 0, success.stderr);
    assert.deepEqual(success.stdout.trimEnd().split('\n'), expected);
    assert.equal(run(expanded, 43).status, 43, 'propagate the runtime failure');
  }
  console.log('PASS: reproduced exit 126; all 8 Docker/Podman commands forward argv and exit status');
} finally {
  fs.rmSync(temporary, { recursive: true, force: true });
}
