"""Small synthetic regressions for the source inventory's fail-closed boundary."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    'source_census', Path(__file__).with_name('source_census.py'))
CENSUS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CENSUS)


class SourceCensusTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.lean = self.root/'toolchain'
        self.write('toolchain/Init.lean', 'prelude\n')
        self.write('Compact/Selected.lean', 'import Lib.Selected\n')
        (self.root/'.lake/packages/lib').mkdir(parents=True)
        for target, name, value in (
                (CENSUS, 'ROOT', self.root),
                (CENSUS, 'LEAN', self.lean),
                (CENSUS.VERIFY, 'ROOT', self.root)):
            self.enterContext(patch.object(target, name, value))

    def write(self, path, content):
        target = self.root/path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)

    def run_census(self, all_retained=False):
        with contextlib.redirect_stdout(io.StringIO()):
            CENSUS.main(['Compact.Selected'], all_retained=all_retained)

    def report(self):
        return json.loads((self.root/'.verification/current-source-census.json').read_text())

    def test_missing_external_cannot_report_budget_pass(self):
        # A fresh checkout must retain a diagnostic report, then fail closed,
        # even though the partial count lies well below either module limit.
        with self.assertRaisesRegex(SystemExit, 'incomplete'):
            self.run_census()
        report = self.report()
        self.assertEqual(report['missing_external_sources'], ['Lib.Selected'])
        self.assertIsNone(report['current_source_under_8000'])
        self.assertIsNone(report['current_source_under_hard_limit'])
        self.assertFalse(report['source_census_complete'])

    def test_retained_alternative_has_its_own_external_closure(self):
        self.write('.lake/packages/lib/Lib/Selected.lean', '')
        self.write('Compact/Alternative.lean', 'import Lib.Extra\n')
        self.write('.lake/packages/lib/Lib/Extra.lean', 'import Lib.Leaf\n')
        self.write('.lake/packages/lib/Lib/Leaf.lean', '')
        self.run_census()
        report = self.report()
        self.assertEqual(report['combined_modules'], 3)
        self.assertEqual(report['all_project_files_plus_current_external_closure'], 4)
        self.assertEqual(report['retained_external_modules'], 4)
        self.assertEqual(report['retained_combined_modules'], 6)
        self.assertTrue(report['source_census_complete'])

    def test_missing_retained_import_is_unknown_but_selected_can_proceed(self):
        self.write('.lake/packages/lib/Lib/Selected.lean', '')
        self.write('Compact/Alternative.lean', 'import Lib.Missing\n')
        self.run_census()
        report = self.report()
        self.assertTrue(report['enforced_source_closure_complete'])
        self.assertEqual(report['enforced_scope'], 'selected')
        self.assertIsNone(report['retained_source_under_hard_limit'])
        with self.assertRaisesRegex(SystemExit, 'incomplete'):
            self.run_census(all_retained=True)
        report = self.report()
        self.assertTrue(report['current_source_under_hard_limit'])
        self.assertIsNone(report['retained_source_under_hard_limit'])
        self.assertEqual(report['missing_retained_external_sources'], ['Lib.Missing'])
        self.assertFalse(report['source_census_complete'])
        self.assertFalse(report['enforced_source_closure_complete'])
        self.assertEqual(report['enforced_scope'], 'all_retained')

    def test_header_stream_handles_nested_comments_and_implicit_init(self):
        self.write('Compact/Header.lean',
            '/- outer\n/- nested -/\n-/\nimport Lib.One /- tail -/\n'
            'import Lib.Two -- tail\ndef body := "import Lib.NotAnImport"\n')
        self.assertEqual(CENSUS.header_imports(self.root/'Compact/Header.lean'),
                         ['Lib.One', 'Lib.Two', 'Init'])

    def test_lake_source_layout_is_included_in_external_closure(self):
        self.write('.lake/packages/lib/Lib/Selected.lean', 'import Lake\n')
        self.write('toolchain/lake/Lake.lean', 'import Lake.Config\n')
        self.write('toolchain/lake/Lake/Config.lean', '')
        self.run_census()
        report = self.report()
        self.assertEqual(report['external_modules'], 4)
        self.assertEqual(report['missing_external_sources'], [])
        self.assertTrue(report['selected_source_closure_complete'])

    def test_module_header_includes_public_and_meta_dependencies(self):
        self.write('Compact/Header.lean',
            'module\nprelude\npublic import Lib.One\n'
            'public meta import Lib.Two\nmeta import Lib.Three\n'
            'def body := 0\n')
        self.assertEqual(CENSUS.header_imports(self.root/'Compact/Header.lean'),
                         ['Lib.One', 'Lib.Two', 'Lib.Three'])

    def test_import_all_is_a_modifier_not_a_module(self):
        self.write('Compact/Header.lean',
            'module\nimport all Lib.One\npublic import all Lib.Two\n'
            'public meta import all Lib.Three\ndef body := 0\n')
        self.assertEqual(CENSUS.header_imports(self.root/'Compact/Header.lean'),
                         ['Lib.One', 'Lib.Two', 'Lib.Three', 'Init'])


if __name__ == '__main__':
    unittest.main()
