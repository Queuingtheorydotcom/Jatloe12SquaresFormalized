import Compact.Assembly.Final
import Compact.Core.Dag
import Compact.Core.LinearCombination
import Compact.Core.DirectLinear
import Compact.Core.IntegerSupportCase
import Compact.Geometry.WallChain
import Compact.Geometry.BorderEndpoint
import Compact.Geometry.C696Symmetry
import Compact.Geometry.ChordRadius
import Compact.Geometry.FourSquareAnchors
import Compact.Bridge.BorderEndpoint
import Compact.Bridge.C977DisjointChain
import Compact.Geometry.ThreeSquareRadius
import Compact.Geometry.C981Midpoint

/- The complete N12 source assembly and its reusable mathematical rules.
The source is uncompiled; this entry point is not a verification receipt. -/
#print axioms N12Compact.Final.optimality
#print axioms N12Compact.Dag.checkedRefuteOn
#print axioms N12Compact.strictCombination_refutes
#print axioms N12Compact.twoNodeCycle_refutes
#print axioms N12Compact.WallChain.first_center_cut
#print axioms N12Compact.BorderEndpoint.positive_endpoints
#print axioms N12Compact.IntegerSupportCase.original_implication
#print axioms N12Compact.SectionCapacity.multi_cut_capacity
#print axioms N12Compact.LongSectionGeometry.horizontal_long_section
#print axioms N12Compact.CongruentSAT.faceSeparation_of_disjoint
#print axioms N12Compact.ThreeSquare.forced_point_of_radius
#print axioms N12Compact.FourSquareAnchors.centroid_inside
#print axioms N12Compact.C977ChainBridge.openSquare_chain_cut_of_disjoint
#print axioms N12Compact.C981Midpoint.excludes
