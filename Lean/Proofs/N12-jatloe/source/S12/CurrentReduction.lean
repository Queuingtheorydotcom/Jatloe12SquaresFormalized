import S12.To18
namespace S12
def survivingRows : List CoverRow := afterPushJoined18
theorem survivingRows_count : survivingRows.length=18 := afterPushJoined18_count
theorem packing_reduction_current (p : NormalizedPacking) :
    ∃ t∈allTransforms,∃ r∈survivingRows,codedMarkerFamily (t.pullPacking p)=r.groups :=
  packing_reduction_to_18 p
theorem unit_packing_reduction_current {L : ℝ} (p : UnitPacking L) (hL : 0<L) (h4 : L<4) :
    ∃ t∈allTransforms,∃ r∈survivingRows,
      codedMarkerFamily (t.pullPacking (p.normalize hL h4))=r.groups :=
  packing_reduction_current (p.normalize hL h4)
#print axioms unit_packing_reduction_current
end S12
