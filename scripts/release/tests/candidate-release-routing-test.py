"""Execute extracted routing/ancestry guards only; no provider or native admission."""
import json
from pathlib import Path
import re
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[3]
WORKFLOW = ROOT / '.github/workflows/candidate.yml'


def routing_block(text):
    begin = '          release_line=$(printf'
    end = '          integration_pr_number=$(jq -r '
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError('routing extraction boundaries must be unique')
    start = text.index(begin)
    return text[start:text.index(end, start)]


def admission_block(text):
    begin = '          if git merge-base --is-ancestor "$release_sha" "$main_sha"; then'
    end = '          pr_json=$(gh api'
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError('admission guard extraction boundaries must be unique')
    start = text.index(begin)
    return text[start:text.index(end, start)]


def evaluate(text, version, ancestry='diverged', commit='release-sha',
             admission=False, release_ref='release/1.0'):
    # Git transport is a deterministic fixture; execute the actual workflow
    # shell route, exact-head check, and both ancestry guards without fetching.
    shell = r'''set -eu
VERSION=$1
ANCESTRY=$2
COMMIT=$3
RELEASE_REF=$4
main_sha=main-sha
release_sha=release-sha
git() {
  case "$1" in
    fetch) return 0 ;;
    rev-parse)
      case "$2" in
        refs/remotes/origin/main) printf '%s\n' main-sha ;;
        refs/remotes/origin/release/*|refs/remotes/origin/release_phase3) printf '%s\n' release-sha ;;
        *) return 97 ;;
      esac ;;
    merge-base)
      [ "$2" = --is-ancestor ] || return 98
      case "$ANCESTRY:$3:$4" in
        release-in-main:release-sha:main-sha|main-in-release:main-sha:release-sha|equal:*) return 0 ;;
        *) return 1 ;;
      esac ;;
    *) return 99 ;;
  esac
}
''' + (admission_block(text) + '\necho GUARDS_ONLY\n' if admission else
           routing_block(text) + '\nprintf "ROUTE=%s\n" "$release_ref"\n')
    return subprocess.run(['bash', '-c', shell, 'routing-control', version, ancestry, commit, release_ref],
                          capture_output=True, text=True, timeout=5)


class CandidateReleaseRouting(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = WORKFLOW.read_text()
        cls.admission = (ROOT / '.github/workflows/pr-admission.yml').read_text()

    def test_routing_extraction_rejects_missing_or_duplicate_boundary(self):
        for changed in (self.source.replace('          release_line=$(printf', '          moved_route=$(printf'),
                        self.source + '\n          release_line=$(printf',
                        self.source.replace('          integration_pr_number=$(jq -r ', '          replaced_boundary=')):
            with self.subTest(length=len(changed)), self.assertRaises(ValueError):
                routing_block(changed)

    def test_version_derived_route(self):
        for version, expected in [('1.0.0-rc.1', 'release/1.0'),
                                  ('1.0.0-beta.2', 'release/1.0'),
                                  ('2.3.4', 'release/2.3')]:
            with self.subTest(version=version):
                result = evaluate(self.source, version)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), 'ROUTE=' + expected)

    def test_both_ancestry_directions_fail_closed_for_rc_and_stable(self):
        for version in ('1.0.0-rc.1', '2.3.4'):
            for ancestry in ('main-in-release', 'release-in-main', 'equal'):
                with self.subTest(version=version, ancestry=ancestry):
                    result = evaluate(self.source, version, ancestry)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertNotIn('ROUTE=', result.stdout)

    def test_candidate_must_equal_exact_release_head(self):
        result = evaluate(self.source, '1.0.0-rc.1', commit='different-candidate')
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('ROUTE=', result.stdout)

    def test_admission_guard_never_exempts_work_branch_alias(self):
        for ref in ('release/1.0', 'release_phase3'):
            for ancestry in ('main-in-release', 'release-in-main', 'equal'):
                with self.subTest(ref=ref, ancestry=ancestry):
                    result = evaluate(self.admission, '', ancestry,
                                      admission=True, release_ref=ref)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertNotIn('GUARDS_ONLY', result.stdout)
            result = evaluate(self.admission, '', admission=True, release_ref=ref)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), 'GUARDS_ONLY')

    def test_admission_input_accepts_only_protected_release_lines(self):
        checks = [line.strip() for line in self.admission.splitlines()
                  if line.strip().startswith('[[ "$RELEASE_REF" =~ ')]
        self.assertEqual(len(checks), 1)
        for ref, accepted in [('release/1.0', True), ('release/2.3', True),
                              ('release_phase3', False), ('main', False),
                              ('release/1.0/extra', False), ('release/1x0', False)]:
            with self.subTest(ref=ref):
                result = subprocess.run(
                    ['bash', '-c', 'RELEASE_REF=$1; ' + checks[0],
                     'admission-input-control', ref],
                    capture_output=True, text=True, timeout=5)
                self.assertEqual(result.returncode == 0, accepted, result.stderr)

    def test_current_version_route_matches_checked_in_manifest(self):
        version = re.search(r'^\s*semver:\s*([^\s]+)',
                            (ROOT / 'release/version.sdn').read_text(), re.M)
        self.assertIsNotNone(version)
        result = evaluate(self.source, version.group(1).strip('"'))
        self.assertEqual(result.returncode, 0, result.stderr)
        manifest = json.loads((ROOT / '.github/release-convergence-manifest.json').read_text())
        self.assertEqual(result.stdout.strip(), 'ROUTE=' + manifest['release_ref'])


if __name__ == '__main__':
    unittest.main()
