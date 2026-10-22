"""Source/template contract controls; never execute a Simple compiler or probe."""
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[3]
HARNESS = ROOT / 'scripts/check/lib/check-cold-hir-path-diagnostic.py'
spec = importlib.util.spec_from_file_location('cold_hir_diagnostic', HARNESS)
diagnostic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diagnostic)


class ColdHirDiagnosticContract(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.driver = (ROOT / 'src/compiler/80.driver/driver_hir_pipeline_lowering.spl').read_text()
        cls.helper = (ROOT / 'src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl').read_text()
        cls.template = json.loads(HARNESS.with_name('cold-hir-path-diagnostic-template.json').read_text())

    def test_exact_production_helper_closes_fixture(self):
        block, helper, fixture = diagnostic.extract_fixture(self.driver, self.helper, self.template)
        self.assertEqual(fixture.count('fn cold_hir_source_mismatch_evidence_v1('), 1)
        self.assertIn(helper, self.helper)
        self.assertIn(helper, fixture)
        self.assertIn('self.ctx.add_error(cold_hir_source_mismatch_evidence_v1(', block)
        self.assertNotIn('{{production_helper}}', fixture)
        self.assertNotIn('ProbeHir', fixture)
        hir_fields = set(re.findall(r'^    (\w+):', fixture.split('\n\n', 1)[0], re.M))
        required_fields = set(re.findall(r'\bmodule\.(\w+)', helper))
        self.assertEqual(required_fields, {'name', 'path'})
        self.assertLessEqual(required_fields, hir_fields)
        for constructor in re.findall(r'HirModule\(([^)]*)\)', self.template['suffix']):
            self.assertIn('name:', constructor)
            self.assertIn('path:', constructor)

    def test_helper_source_changes_flow_into_fixture(self):
        changed = self.helper.replace('no mismatched lowered source located', 'SOURCE_AUTHORITY_SENTINEL')
        self.assertNotEqual(changed, self.helper)
        _, helper, fixture = diagnostic.extract_fixture(self.driver, changed, self.template)
        self.assertIn('SOURCE_AUTHORITY_SENTINEL', helper)
        self.assertIn('SOURCE_AUTHORITY_SENTINEL', fixture)

    def test_missing_or_duplicate_production_helper_rejected(self):
        for helper in ('', self.helper + '\nfn cold_hir_source_mismatch_evidence_v1('):
            with self.subTest(helper_length=len(helper)), self.assertRaises(ValueError):
                diagnostic.extract_fixture(self.driver, helper, self.template)

    def test_missing_or_duplicate_template_helper_slot_rejected(self):
        for replacement in ('', '{{production_helper}}{{production_helper}}'):
            template = dict(self.template)
            template['prefix'] = template['prefix'].replace('{{production_helper}}', replacement)
            with self.subTest(replacement=replacement), self.assertRaises(ValueError):
                diagnostic.extract_fixture(self.driver, self.helper, template)

    def test_changed_caller_boundary_rejected(self):
        for changed in (self.driver.replace('case Ok(receipts):', 'case Ok(other):'),
                        self.driver.replace('self.ctx.add_error(cold_hir_source_mismatch_evidence_v1(',
                                            'self.ctx.add_error(unbound_helper(')):
            with self.subTest(length=len(changed)), self.assertRaises(ValueError):
                diagnostic.extract_fixture(changed, self.helper, self.template)

    def test_oracle_matches_current_five_case_contract(self):
        evidence = [
            "cold HIR path evidence: index=0 root='/frozen' source='/other/main.spl' module='pkg.main' hir=''",
            "cold HIR path evidence: index=0 root='/frozen' source='/other/main.spl' module='pkg.main' hir=''",
            "cold HIR path evidence: index=0 root='/frozen' source='/other/main.spl' module='' hir=''",
            "cold HIR path evidence: index=0 root='/frozen' source='/other/main.spl' module='pkg.main' hir='/other/main.spl'",
            'cold HIR path evidence: no mismatched lowered source located',
        ]
        expected = []
        labels = ['empty-map', 'missing-name', 'empty-names', 'present-name', 'empty-sources']
        for label, line in zip(labels, evidence):
            expected.extend(['CASE ' + label, line,
                             'cold HIR receipt capture failed: cold-hir-module-source-mismatch',
                             'CASE_DONE ' + label])
        expected.append('NATIVE_DIAGNOSTIC_CASES_COMPLETED 5')
        self.assertEqual(diagnostic.expected_output(), expected)


if __name__ == '__main__':
    unittest.main()
