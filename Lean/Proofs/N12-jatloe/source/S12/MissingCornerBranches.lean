import S12.SingletonMissing
import S12.DisjointCornerSplit
import S12.PackingEnclosure
namespace S12
open S12Pilot
set_option maxHeartbeats 0

theorem singleton_zero_missing_points (q : OpenSquare) (ha : 1<q.side)
    (hs : q.side≤1001/1000) (hb : InsideContainer q)
    (he : ExactMarkers q {0}) (hm : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 ∧ q.Inside (49/25) (19/25) := by
  apply corner_singleton_missing_forces q ha hs hb ((he 0).mpr (by simp))
  · intro i hi hh
    have h := (he i).mp hh
    exact hi (Finset.mem_singleton.mp h)
  · exact hm

theorem singleton_one_missing_points (q : OpenSquare) (ha : 1<q.side)
    (hs : q.side≤1001/1000) (hb : InsideContainer q)
    (he : ExactMarkers q {1}) (hm : ¬q.Inside 1 1) :
    q.Inside 1 (91/50) ∧ q.Inside (19/25) (49/25) := by
  have ht : ExactMarkers (pullSwap q) {0} := by
    intro i
    rw [owns_pullSwap,he]
    fin_cases i <;> decide
  have hmiss : ¬(pullSwap q).Inside 1 1 := by simpa only [inside_pullSwap] using hm
  have hh := singleton_zero_missing_points (pullSwap q) ha hs (container_pullSwap q hb) ht hmiss
  simpa only [inside_pullSwap] using hh


#print axioms singleton_one_missing_points
#print axioms disjoint_corner_split
end S12
