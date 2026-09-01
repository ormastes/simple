import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import test from "node:test";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "../../../..");
const producer = join(root, "scripts/release/self-review-changed-manifest.shs");

function run(cwd, command, args) {
  const result = spawnSync(command, args, { cwd, encoding: "utf8" });
  assert.equal(result.status, 0, `${command} ${args.join(" ")}\n${result.stderr}`);
  return result.stdout.trim();
}

test("manifest blob reads do not parse malformed historical submodule configuration", () => {
  const directory = mkdtempSync(join(tmpdir(), "self-review-manifest-"));
  try {
    run(directory, "git", ["init", "-q"]);
    run(directory, "git", ["config", "user.email", "test@example.invalid"]);
    run(directory, "git", ["config", "user.name", "Self Review Test"]);
    writeFileSync(join(directory, ".gitmodules"), [
      '[submodule "dup"]', "\tpath = deps/one", "\turl = https://example.invalid/one",
      '[submodule "dup"]', "\tpath = deps/two", "\turl = https://example.invalid/two", "",
    ].join("\n"));
    writeFileSync(join(directory, "review.sdn"), "value: base\n");
    run(directory, "git", ["add", ".gitmodules", "review.sdn"]);
    run(directory, "git", ["commit", "-q", "-m", "base"]);
    const base = run(directory, "git", ["rev-parse", "HEAD"]);
    writeFileSync(join(directory, "review.sdn"), "value: head\n");
    run(directory, "git", ["add", "review.sdn"]);
    run(directory, "git", ["commit", "-q", "-m", "head"]);
    const head = run(directory, "git", ["rev-parse", "HEAD"]);
    const mergeBase = run(directory, "git", ["merge-base", base, head]);
    const rawDiff = spawnSync("git", [
      "diff", "--raw", "-z", "--find-renames", "--find-copies", mergeBase, head, "--",
    ], { cwd: directory });
    assert.equal(rawDiff.status, 0, rawDiff.stderr.toString());
    const diffSha256 = createHash("sha256").update(rawDiff.stdout).digest("hex");
    const output = join(directory, "manifest.sdn");
    const result = spawnSync(producer, [
      "github", "1", "R_test", "owner/repo", "1", "1", "R_test",
      "owner/repo", "refs/heads/main", base, head, mergeBase, output,
    ], { cwd: directory, encoding: "utf8" });

    assert.equal(result.status, 0, result.stderr);
    assert.doesNotMatch(result.stderr, /multiple configurations found|\.gitmodules/);
    const manifest = readFileSync(output, "utf8");
    assert.equal((manifest.match(/^[ ]{6}path: review\.sdn$/gm) ?? []).length, 1);
    assert.equal((manifest.match(/^[ ]{4}- status:/gm) ?? []).length, 1);
    assert.doesNotMatch(manifest, /^[ ]{6}path: \.gitmodules$/m);
    assert.match(manifest, new RegExp(`^[ ]{2}base_sha: ${base}$`, "m"));
    assert.match(manifest, new RegExp(`^[ ]{2}head_sha: ${head}$`, "m"));
    assert.match(manifest, new RegExp(`^[ ]{2}merge_base_sha: ${mergeBase}$`, "m"));
    assert.match(manifest, new RegExp(`^[ ]{2}diff_sha256: ${diffSha256}$`, "m"));

    const source = readFileSync(producer, "utf8");
    assert.match(source, /git cat-file blob "\$revision:\$path"/);
    assert.doesNotMatch(source, /git show[ ]+"\$revision:\$path"/);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});
