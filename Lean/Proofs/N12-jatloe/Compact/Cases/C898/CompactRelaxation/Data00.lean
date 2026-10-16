import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data00
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 1752, 1751)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 1754, 1753)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 1756, 1755)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 1758, 1757)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 1760, 1759)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 1762, 1761)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 1764, 1763)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 1765, 1763)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 1767, 1766)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 1768, 1766)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 1769, 1766)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 1771, 1770)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 1772, 1770)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 1773, 1770)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 1775, 1774)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 1776, 1774)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 1777, 1774)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 1778, 1774)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 1780, 1779)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 1781, 1779)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 1782, 1779)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 1783, 1779)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 1785, 1784)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 1786, 1784)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 1787, 1784)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 1788, 1784)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 1790, 1789)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 1791, 1789)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 1792, 1789)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 1793, 1789)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 1795, 1794)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 1796, 1794)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 1797, 1794)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 1799, 1798)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 1800, 1798)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 1802, 1801)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 1804, 1803)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 1806, 1805)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 1808, 1807)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 1810, 1809)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 1812, 1811)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 1813, 1811)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 1815, 1814)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 1816, 1814)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 1817, 1814)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 1819, 1818)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 1820, 1818)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 1822, 1821)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 1823, 1821)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 1825, 1824)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 1826, 1824)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 1828, 1827)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 1829, 1827)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 1831, 1830)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 1832, 1830)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 1834, 1833)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 1835, 1833)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 1837, 1836)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 1838, 1836)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 1840, 1839)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 1841, 1839)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 1843, 1842)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 1844, 1842)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 1846, 1845)

def data : Array (Entry dictionary) := #[
  entry0,
  entry1,
  entry2,
  entry3,
  entry4,
  entry5,
  entry6,
  entry7,
  entry8,
  entry9,
  entry10,
  entry11,
  entry12,
  entry13,
  entry14,
  entry15,
  entry16,
  entry17,
  entry18,
  entry19,
  entry20,
  entry21,
  entry22,
  entry23,
  entry24,
  entry25,
  entry26,
  entry27,
  entry28,
  entry29,
  entry30,
  entry31,
  entry32,
  entry33,
  entry34,
  entry35,
  entry36,
  entry37,
  entry38,
  entry39,
  entry40,
  entry41,
  entry42,
  entry43,
  entry44,
  entry45,
  entry46,
  entry47,
  entry48,
  entry49,
  entry50,
  entry51,
  entry52,
  entry53,
  entry54,
  entry55,
  entry56,
  entry57,
  entry58,
  entry59,
  entry60,
  entry61,
  entry62,
  entry63
]

def get (i : Fin 64) : Entry dictionary :=
  data[i.val]'(by change i.val < 64; exact i.isLt)

def Claim (i : Fin 64) : Prop := (get i).Check

instance (i : Fin 64) : Decidable (Claim i) :=
  inferInstanceAs (Decidable ((get i).Check))

theorem block0 : FiniteCheckChunks.Check Claim 0 := by
  decide +kernel

theorem block1 : FiniteCheckChunks.Check Claim 1 := by
  decide +kernel

theorem block2 : FiniteCheckChunks.Check Claim 2 := by
  decide +kernel

theorem block3 : FiniteCheckChunks.Check Claim 3 := by
  decide +kernel

theorem block4 : FiniteCheckChunks.Check Claim 4 := by
  decide +kernel

theorem block5 : FiniteCheckChunks.Check Claim 5 := by
  decide +kernel

theorem block6 : FiniteCheckChunks.Check Claim 6 := by
  decide +kernel

theorem block7 : FiniteCheckChunks.Check Claim 7 := by
  decide +kernel

theorem checked (i : Fin 64) : (get i).Check := by
  refine FiniteCheckChunks.sound Claim (count := 8) (by decide) ?_ i
  intro part
  fin_cases part
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7

end
end N12Compact.C898CompactRelaxation.Data00
