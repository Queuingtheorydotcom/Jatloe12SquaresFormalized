from pathlib import Path
import tempfile
import unittest

from audit_native_axioms import AuditError, authenticated_sites, native_sites, query, sha, validate_log, validate_runtime


class NativeAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.original = b'namespace S12\ndef data : Bool := true\ntheorem checked : data = true := by native_decide\nend S12\n'
        self.vendor = self.root/'vendor/S12/Data.lean'
        self.vendor.parent.mkdir(parents=True)
        self.vendor.write_bytes(self.original)
        self.current = self.root/'source/S12/Data/Chunk00.lean'
        self.current.parent.mkdir(parents=True)
        self.current.write_bytes(self.original)
        self.provenance = {'records': [{'vendor': 'vendor/S12/Data.lean',
            'vendor_sha256': sha(self.original), 'site_occurrences': 1}]}
        self.snapshot = {'files': [{'path': 'source/S12/Data/Chunk00.lean', 'sha256': sha(self.original)}]}
        self.sites = {'S12.checked': {'module': 'S12.Data.Chunk00'}}
        self.axiom = 'S12.checked._native.native_decide.ax_1'

    def authenticate(self):
        return authenticated_sites({'S12.Data.Chunk00': (self.current, self.current.read_bytes())},
                                   self.provenance, self.snapshot, self.root, self.root)

    def log(self, final=None, owner=None):
        return ("'Final.result' depends on axioms: [" + (final or self.axiom) + "]\n" +
                "'S12.checked' depends on axioms: [" + (owner or self.axiom) + ']\n')

    def test_exact_relocation_and_owned_axiom(self):
        self.assertEqual(set(self.authenticate()), {'S12.checked'})
        result = validate_log(self.log(), 'Final.result', self.sites)
        self.assertTrue(result['inherited_native_compiler_trust'])
        self.assertEqual(result['native_axiom_owners'], {self.axiom: 'S12.checked'})

    def test_changed_numerical_data_rejected(self):
        self.current.write_bytes(self.original.replace(b':= true', b':= false'))
        with self.assertRaisesRegex(AuditError, 'Native source hash mismatch'):
            self.authenticate()

    def test_changed_original_rejected(self):
        self.vendor.write_bytes(self.original + b'\n')
        with self.assertRaisesRegex(AuditError, 'Original hash mismatch'):
            self.authenticate()

    def test_missing_original_rejected(self):
        self.vendor.unlink()
        with self.assertRaisesRegex(AuditError, 'Missing original'):
            self.authenticate()

    def test_uninventoried_site_even_with_snapshot_hash_rejected(self):
        raw = self.original.replace(b'checked', b'extra')
        self.current.write_bytes(raw)
        self.snapshot['files'][0]['sha256'] = sha(raw)
        with self.assertRaisesRegex(AuditError, 'differs from original|Uninventoried native declaration'):
            self.authenticate()

    def test_changed_data_rejected_even_if_current_snapshot_is_replaced(self):
        raw = self.original.replace(b':= true', b':= false')
        self.current.write_bytes(raw)
        self.snapshot['files'][0]['sha256'] = sha(raw)
        with self.assertRaisesRegex(AuditError, 'Numerical definition differs from original'):
            self.authenticate()

    def test_inline_numerical_hypotheses(self):
        raw = b'namespace S12\ndef certificate : Bool := (by native_decide)\nend S12\n'
        self.assertEqual(set(native_sites(raw)), {'S12.certificate'})

    def test_unrelated_native_suffix_rejected(self):
        with self.assertRaisesRegex(AuditError, 'Unmapped axiom'):
            validate_log(self.log('Unrelated._native.native_decide.ax_1'), 'Final.result', self.sites)

    def test_approved_prefix_without_owner_dependency_rejected(self):
        with self.assertRaisesRegex(AuditError, 'Unmapped axiom'):
            validate_log(self.log(owner='propext'), 'Final.result', self.sites)

    def test_arbitrary_axiom_in_approved_certificate_rejected(self):
        with self.assertRaisesRegex(AuditError, 'Unmapped axiom'):
            validate_log(self.log(owner=self.axiom + ', arbitraryOracle'), 'Final.result', self.sites)

    def test_missing_duplicate_and_failed_query_rejected(self):
        for log in [self.log().splitlines()[0], self.log()+self.log(), self.log()+': error(lean.unknownIdentifier): bad']:
            with self.assertRaises(AuditError):
                validate_log(log, 'Final.result', self.sites)

    def test_explicit_axiom_and_unsupported_native_syntax_rejected(self):
        raw = self.original.replace(b'def data', b'axiom arbitrary : True\ndef data')
        self.current.write_bytes(raw)
        self.snapshot['files'][0]['sha256'] = sha(raw)
        with self.assertRaisesRegex(AuditError, 'Unapproved trust syntax'):
            self.authenticate()
        with self.assertRaisesRegex(AuditError, 'supported theorem'):
            native_sites(b'example : True := by native_decide\n')

    def test_multiline_numerical_theorem(self):
        raw = b'namespace S12\ntheorem multiline :\n    (true = true) := by native_decide\nend S12\n'
        self.assertEqual(set(native_sites(raw)), {'S12.multiline'})

    def test_query_uses_fully_qualified_names(self):
        self.assertIn('set_option pp.fullNames true', query('Final', 'Final.result', self.sites))
        with self.assertRaises(AuditError):
            query('Final\naxiom bad : False', 'Final.result', self.sites)

    def test_compiler_disambiguated_axiom_names(self):
        renamed = self.axiom + '_1'
        result = validate_log(self.log(renamed, renamed), 'Final.result', self.sites)
        self.assertEqual(result['native_axiom_owners'], {renamed: 'S12.checked'})

    def test_runtime_requires_exact_frozen_source_and_axiom(self):
        sites = self.authenticate()
        manifest = validate_log(self.log(), 'Final.result', sites)
        files = {'S12.Data.Chunk00': (self.current, self.original)}
        result = validate_runtime(files, manifest, {self.axiom}, self.root)
        self.assertTrue(result['inherited_native_compiler_trust'])
        with self.assertRaisesRegex(AuditError, 'Unmapped final axiom'):
            validate_runtime(files, manifest, {self.axiom + '_1'}, self.root)
        files['S12.Data.Chunk00'] = (self.current, self.original.replace(b':= true', b':= false'))
        with self.assertRaisesRegex(AuditError, 'hash/owner mismatch'):
            validate_runtime(files, manifest, {self.axiom}, self.root)

    def test_runtime_rejects_missing_and_new_sites(self):
        manifest = validate_log(self.log(), 'Final.result', self.authenticate())
        with self.assertRaisesRegex(AuditError, 'closure differs'):
            validate_runtime({}, manifest, {self.axiom}, self.root)
        files = {'S12.Data.Chunk00': (self.current, self.original.replace(b'checked', b'extra'))}
        with self.assertRaisesRegex(AuditError, 'Uninventoried native declaration'):
            validate_runtime(files, manifest, {self.axiom}, self.root)


if __name__ == '__main__':
    unittest.main()
