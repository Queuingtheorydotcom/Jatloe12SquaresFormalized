"""Tiny proposer regressions; these do not establish Lean soundness."""
import unittest

from generate_c981_indexed_chunks import (
    exact_target_slice, parse_row, propose_indices, render_chunk, shape,
)


class IndexedProposalTests(unittest.TestCase):
    def test_all_compatible_choices_in_original_order(self):
        # Bit 1 overlaps the front; bit 2 and the empty set both survive.
        # Target order deliberately differs from choice order.
        before = [(1,)]
        after = [(8,8),(1,0),(1,2)]
        self.assertEqual(propose_indices(before,(1,2,0),after),[2,1])

    def test_missing_target_is_not_silently_skipped(self):
        with self.assertRaises(KeyError):
            propose_indices([(1,)],(2,),[(1,0)])

    def test_slice_rebases_every_index_in_order(self):
        self.assertEqual(exact_target_slice([172,173,174]),(172,3,[0,1,2]))
        self.assertEqual(exact_target_slice([]),(0,0,[]))

    def test_slice_rejects_gaps_reordering_and_duplicates(self):
        for indices in ([1,3],[2,1],[1,1],[-1,0]):
            with self.subTest(indices=indices), self.assertRaises(AssertionError):
                exact_target_slice(indices)

    def test_parser_rejects_unaccounted_literal_text(self):
        with self.assertRaises(AssertionError):
            parse_row('[{1}, bogus, ∅]')

    def test_final_chunk_checks_entire_suffix(self):
        self.assertEqual(shape(10,32,67),(68,2144,'(prefix09.drop 2144)'))
        self.assertIn('.take 32',shape(10,32,66)[2])

    def test_four_decisions_stay_in_one_module(self):
        fronts = [(1 << i,) for i in range(32)]
        tables = {'prefix09':fronts,'prefix10':[row+(0,) for row in fronts],
            'allowed5':(0,)}
        source,record = render_chunk(tables,10,32,0,8)
        text = source.decode()
        self.assertEqual(text.count('  decide +kernel'),4)
        self.assertEqual(len(record['decisions']),4)
        self.assertEqual([r['target_slice_start'] for r in record['decisions']],[0,8,16,24])
        self.assertTrue(record['decisions'][-1]['checks_entire_remaining_suffix'])
        self.assertEqual(text.count('apply takeDropStepCheck 8'),3)


if __name__ == '__main__':
    unittest.main()
