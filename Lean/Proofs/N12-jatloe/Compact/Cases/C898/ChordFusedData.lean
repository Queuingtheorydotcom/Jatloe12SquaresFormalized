import Compact.Cases.C898.ChordFusedCache
import Compact.Cases.C898.SharedDomains

namespace N12Compact.C898Chord.Fused
open C898Shared CoordinateBound
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def plan00 : DirectPlan := ⟨1377, none, [], 1, 2⟩
private def cache00 : PlanCache := ⟨[⟨25000000,0,-51911879,true⟩, ⟨-100000000,0,204370621,true⟩, ⟨129543300000000,2024200000000,-241917006083587,false⟩, ⟨0,25000000,-37406011,false⟩, ⟨-1964325000000,300708500000000,-446309840327057,false⟩, ⟨-2970150000000,190079150000000,-278511090683639,false⟩, ⟨-10000000,0,21606813,false⟩, ⟨-15141430000000,-236600000000,33070468522361,false⟩, ⟨0,-5000000,7570717,false⟩, ⟨24733100000000,-1582821400000000,2343184131092721,false⟩, ⟨100000000,0,-184387841,false⟩, ⟨100000000,0,-184387841,false⟩, ⟨-10000000,0,21606813,false⟩, ⟨0,25000000,-37406011,false⟩, ⟨0,-5000000,7570717,false⟩, ⟨0,0,1,true⟩], [], ⟨-25000000,0,51911879,false⟩⟩
private theorem angle00_exact : poseAngle 1377 = 0 := by
  decide +kernel
private theorem radius00_exact : poseRadius 1377 = radius0 := by
  unfold poseRadius; rw [angle00_exact]; rfl
private theorem cache00_exact : cache00.Exact plan00 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache00.inputs = cutRows 1377
    simp only [cutRows,lowerCut,upperCut,radius00_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache00.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache00.supports) (by decide +kernel)
  · change cache00.closing = upper (leftHi + (poseRadius 1377).radius) false
    rw [radius00_exact]
    decide +kernel
private theorem shape00 : plan00.Shape := by decide +kernel
private theorem numeric00 : cache00.Numeric plan00 := by
  decide +kernel
private theorem plan00_checked : plan00.Check :=
  cache00.toCheck plan00 cache00_exact shape00 numeric00

def plan01 : DirectPlan := ⟨1378, none, [], 1, 2⟩
private def cache01 : PlanCache := ⟨[⟨100000000,0,-206025189,true⟩, ⟨-25000000,0,51498237,true⟩, ⟨15189220000,712380000,-29141581719,false⟩, ⟨0,50000000,-75227101,false⟩, ⟨-74255468750,4317619140625,-6358814691203,false⟩, ⟨-11276950000000,240443175000000,-339338191394599,false⟩, ⟨-5000000,0,10826239,false⟩, ⟨-8841443750000,-414675000000,19771260476437,false⟩, ⟨0,-1000000,1527003,false⟩, ⟨37160900000000,-792330200000000,1129452765626921,false⟩, ⟨100000000,0,-184765023,false⟩, ⟨100000000,0,-184765023,false⟩, ⟨-5000000,0,10826239,false⟩, ⟨0,50000000,-75227101,false⟩, ⟨0,-1000000,1527003,false⟩, ⟨0,0,1,true⟩], [], ⟨-100000000,0,206025189,false⟩⟩
private theorem angle01_exact : poseAngle 1378 = 1 := by
  decide +kernel
private theorem radius01_exact : poseRadius 1378 = radius1 := by
  unfold poseRadius; rw [angle01_exact]; rfl
private theorem cache01_exact : cache01.Exact plan01 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache01.inputs = cutRows 1378
    simp only [cutRows,lowerCut,upperCut,radius01_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache01.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache01.supports) (by decide +kernel)
  · change cache01.closing = upper (leftHi + (poseRadius 1378).radius) false
    rw [radius01_exact]
    decide +kernel
private theorem shape01 : plan01.Shape := by decide +kernel
private theorem numeric01 : cache01.Numeric plan01 := by
  decide +kernel
private theorem plan01_checked : plan01.Check :=
  cache01.toCheck plan01 cache01_exact shape01 numeric01

def plan02 : DirectPlan := ⟨1379, some 3056, [⟨24802, 0, 4⟩, ⟨24803, 1, 4⟩, ⟨24804, 0, 5⟩, ⟨24805, 1, 2⟩, ⟨24806, 1, 9⟩, ⟨24807, 0, 9⟩, ⟨24808, 0, 2⟩], 0, 0⟩
private def cache02 : PlanCache := ⟨[⟨25000000,0,-51094267,true⟩, ⟨-100000000,0,207641069,true⟩, ⟨1275320000000,99790000000,-2511491975373,false⟩, ⟨0,50000000,-75675501,false⟩, ⟨-24429050000000,1012214850000000,-1486782133502031,false⟩, ⟨-22704525000000,290174275000000,-393979738194151,false⟩, ⟨-625000,0,1355869,false⟩, ⟨-152035875000,-11896000000,347996065597,false⟩, ⟨0,-25000000,38491063,false⟩, ⟨248551700000000,-3176607900000000,4351871961595001,false⟩, ⟨12500000,0,-23134699,false⟩, ⟨12500000,0,-23134699,false⟩, ⟨-625000,0,1355869,false⟩, ⟨0,50000000,-75675501,false⟩, ⟨0,-25000000,38491063,false⟩, ⟨0,0,1,true⟩], [(⟨24802, 0, 4⟩,⟨0,50000000,-75908167,false⟩), (⟨24803, 1, 4⟩,⟨-1152450000000,47750050000000,-70137029568101,false⟩), (⟨24804, 0, 5⟩,⟨-9032900000000,115445000000000,-156743517177849,false⟩), (⟨24805, 1, 2⟩,⟨-100000000,0,207641169,false⟩), (⟨24806, 1, 9⟩,⟨0,-100000000,153244409,false⟩), (⟨24807, 0, 9⟩,⟨25539800000000,-326410100000000,447174140460647,false⟩), (⟨24808, 0, 2⟩,⟨25000000,0,-51094217,false⟩)], ⟨-25000000,0,51094267,false⟩⟩
private theorem angle02_exact : poseAngle 1379 = 2 := by
  decide +kernel
private theorem radius02_exact : poseRadius 1379 = radius2 := by
  unfold poseRadius; rw [angle02_exact]; rfl
private theorem cache02_exact : cache02.Exact plan02 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache02.inputs = cutRows 1379
    simp only [cutRows,lowerCut,upperCut,radius02_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache02.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache02.supports) (by decide +kernel)
  · change cache02.closing = upper (leftHi + (poseRadius 1379).radius) false
    rw [radius02_exact]
    decide +kernel
private theorem shape02 : plan02.Shape := by decide +kernel
private theorem numeric02 : cache02.Numeric plan02 := by
  decide +kernel
private theorem plan02_checked : plan02.Check :=
  cache02.toCheck plan02 cache02_exact shape02 numeric02

def plan03 : DirectPlan := ⟨1380, some 3058, [⟨24810, 0, 2⟩, ⟨24811, 0, 3⟩, ⟨24812, 0, 4⟩, ⟨24813, 1, 2⟩, ⟨24814, 1, 8⟩, ⟨24815, 0, 8⟩, ⟨24816, 2, 8⟩], 0, 0⟩
private def cache03 : PlanCache := ⟨[⟨100000000,0,-202714629,true⟩, ⟨-25000000,0,52325877,true⟩, ⟨9208360000000,1010180000000,-20304815594017,false⟩, ⟨0,100000000,-152796737,false⟩, ⟨-14878220000000,135622600000000,-176913699893099,false⟩, ⟨-4000000,0,8692177,false⟩, ⟨-18416700000000,-2020360000000,43137411616111,false⟩, ⟨0,-20000000,31041119,false⟩, ⟨74391050000000,-678113000000000,890889570845287,false⟩, ⟨50000000,0,-101820473,false⟩, ⟨50000000,0,-101820473,false⟩, ⟨-4000000,0,8692177,false⟩, ⟨0,100000000,-152796737,false⟩, ⟨0,-20000000,31041119,false⟩, ⟨0,0,1,true⟩], [(⟨24810, 0, 2⟩,⟨9208360000000,1010180000000,-20304795156937,false⟩), (⟨24811, 0, 3⟩,⟨0,100000000,-152796537,false⟩), (⟨24812, 0, 4⟩,⟨-30504250000000,278062150000000,-362719255532233,false⟩), (⟨24813, 1, 2⟩,⟨-12500000,0,26162951,false⟩), (⟨24814, 1, 8⟩,⟨0,-50000000,77169593,false⟩), (⟨24815, 0, 8⟩,⟨15530300000000,-141566550000000,185987213745659,false⟩), (⟨24816, 2, 8⟩,⟨50000000,0,-101820373,false⟩)], ⟨-100000000,0,202714629,false⟩⟩
private theorem angle03_exact : poseAngle 1380 = 3 := by
  decide +kernel
private theorem radius03_exact : poseRadius 1380 = radius3 := by
  unfold poseRadius; rw [angle03_exact]; rfl
private theorem cache03_exact : cache03.Exact plan03 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache03.inputs = cutRows 1380
    simp only [cutRows,lowerCut,upperCut,radius03_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache03.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache03.supports) (by decide +kernel)
  · change cache03.closing = upper (leftHi + (poseRadius 1380).radius) false
    rw [radius03_exact]
    decide +kernel
private theorem shape03 : plan03.Shape := by decide +kernel
private theorem numeric03 : cache03.Numeric plan03 := by
  decide +kernel
private theorem plan03_checked : plan03.Check :=
  cache03.toCheck plan03 cache03_exact shape03 numeric03

def plan04 : DirectPlan := ⟨1381, some 3060, [⟨24818, 0, 2⟩, ⟨24819, 0, 3⟩, ⟨24820, 1, 3⟩, ⟨24821, 1, 2⟩, ⟨24822, 1, 9⟩, ⟨24823, 0, 9⟩, ⟨24824, 2, 9⟩], 0, 0⟩
private def cache04 : PlanCache := ⟨[⟨100000000,0,-201049191,true⟩, ⟨-50000000,0,105484473,true⟩, ⟨53082800000000,7501900000000,-118832039256051,false⟩, ⟨131628575000000,368602225000000,-832636531457589,false⟩, ⟨0,50000000,-74220399,false⟩, ⟨-24722300000000,174933700000000,-206054381088729,false⟩, ⟨-25000000,0,54658219,false⟩, ⟨-4395318750000,-621162500000,10533207269473,false⟩, ⟨0,-100000000,156423983,false⟩, ⟨5467532500000,-38687997500000,48623267651551,false⟩, ⟨10000000,0,-20206423,false⟩, ⟨10000000,0,-20206423,false⟩, ⟨-25000000,0,54658219,false⟩, ⟨0,50000000,-74220399,false⟩, ⟨0,-100000000,156423983,false⟩, ⟨0,0,1,true⟩], [(⟨24818, 0, 2⟩,⟨53082800000000,7501900000000,-118831918086651,false⟩), (⟨24819, 0, 3⟩,⟨315313800000000,882979700000000,-1994562807450339,false⟩), (⟨24820, 1, 3⟩,⟨0,100000000,-150552603,false⟩), (⟨24821, 1, 2⟩,⟨-50000000,0,105484523,false⟩), (⟨24822, 1, 9⟩,⟨0,-6250000,9718477,false⟩), (⟨24823, 0, 9⟩,⟨6292310000000,-44524080000000,55958185794443,false⟩), (⟨24824, 2, 9⟩,⟨10000000,0,-20206403,false⟩)], ⟨-100000000,0,201049191,false⟩⟩
private theorem angle04_exact : poseAngle 1381 = 4 := by
  decide +kernel
private theorem radius04_exact : poseRadius 1381 = radius4 := by
  unfold poseRadius; rw [angle04_exact]; rfl
private theorem cache04_exact : cache04.Exact plan04 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache04.inputs = cutRows 1381
    simp only [cutRows,lowerCut,upperCut,radius04_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache04.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache04.supports) (by decide +kernel)
  · change cache04.closing = upper (leftHi + (poseRadius 1381).radius) false
    rw [radius04_exact]
    decide +kernel
private theorem shape04 : plan04.Shape := by decide +kernel
private theorem numeric04 : cache04.Numeric plan04 := by
  decide +kernel
private theorem plan04_checked : plan04.Check :=
  cache04.toCheck plan04 cache04_exact shape04 numeric04

def plan05 : DirectPlan := ⟨1382, some 3062, [⟨24826, 0, 2⟩, ⟨24827, 0, 3⟩, ⟨24828, 1, 3⟩, ⟨24829, 1, 2⟩, ⟨24830, 1, 9⟩, ⟨24831, 0, 9⟩, ⟨24832, 2, 9⟩], 0, 0⟩
private def cache05 : PlanCache := ⟨[⟨5000000,0,-9969591,true⟩, ⟨-100000000,0,212626317,true⟩, ⟨620325000000,107412500000,-1409936207739,false⟩, ⟨159707700000000,377654000000000,-903985061208441,false⟩, ⟨0,10000000,-14817909,false⟩, ⟨-32425100000000,187261850000000,-207563970165531,false⟩, ⟨-100000000,0,219377371,false⟩, ⟨-109894012500000,-19028562500000,269402385117287,false⟩, ⟨0,-50000000,78809657,false⟩, ⟨60041780000000,-346754100000000,415747482915921,false⟩, ⟨5000000,0,-10025859,false⟩, ⟨5000000,0,-10025859,false⟩, ⟨-100000000,0,219377371,false⟩, ⟨0,10000000,-14817909,false⟩, ⟨0,-50000000,78809657,false⟩, ⟨0,0,1,true⟩], [(⟨24826, 0, 2⟩,⟨77540625000,13426562500,-176241844033,false⟩), (⟨24827, 0, 3⟩,⟨511729300000000,1210064400000000,-2896510748109401,false⟩), (⟨24828, 1, 3⟩,⟨0,20000000,-29889981,false⟩), (⟨24829, 1, 2⟩,⟨-100000000,0,212626417,false⟩), (⟨24830, 1, 9⟩,⟨0,-50000000,78357093,false⟩), (⟨24831, 0, 9⟩,⟨41935220000000,-242184740000000,290372572030589,false⟩), (⟨24832, 2, 9⟩,⟨5000000,0,-10025849,false⟩)], ⟨-5000000,0,9969591,false⟩⟩
private theorem angle05_exact : poseAngle 1382 = 5 := by
  decide +kernel
private theorem radius05_exact : poseRadius 1382 = radius5 := by
  unfold poseRadius; rw [angle05_exact]; rfl
private theorem cache05_exact : cache05.Exact plan05 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache05.inputs = cutRows 1382
    simp only [cutRows,lowerCut,upperCut,radius05_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache05.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache05.supports) (by decide +kernel)
  · change cache05.closing = upper (leftHi + (poseRadius 1382).radius) false
    rw [radius05_exact]
    decide +kernel
private theorem shape05 : plan05.Shape := by decide +kernel
private theorem numeric05 : cache05.Numeric plan05 := by
  decide +kernel
private theorem plan05_checked : plan05.Check :=
  cache05.toCheck plan05 cache05_exact shape05 numeric05

def plan06 : DirectPlan := ⟨1383, some 3064, [⟨24834, 0, 2⟩, ⟨24835, 1, 2⟩, ⟨24836, 1, 2⟩, ⟨24837, 1, 8⟩, ⟨24838, 0, 8⟩, ⟨24839, 2, 8⟩], 0, 0⟩
private def cache06 : PlanCache := ⟨[⟨100000000,0,-197753243,true⟩, ⟨-50000000,0,107132447,true⟩, ⟨486126800000000,99773650000000,-1190010834407947,false⟩, ⟨0,50000000,-73948739,false⟩, ⟨-14643925000000,71349562500000,-74121807194907,false⟩, ⟨-25000000,0,55036929,false⟩, ⟨-194450720000000,-39909460000000,487571528778213,false⟩, ⟨0,-100000000,158791729,false⟩, ⟨117151400000000,-570796500000000,650809460089897,false⟩, ⟨100000000,0,-212444077,false⟩, ⟨100000000,0,-212444077,false⟩, ⟨-25000000,0,55036929,false⟩, ⟨0,50000000,-73948739,false⟩, ⟨0,-100000000,158791729,false⟩, ⟨0,0,1,true⟩], [(⟨24834, 0, 2⟩,⟨443602400000000,91045850000000,-1085912436449767,false⟩), (⟨24835, 1, 2⟩,⟨0,50000000,-74373883,false⟩), (⟨24836, 1, 2⟩,⟨-50000000,0,107132497,false⟩), (⟨24837, 1, 8⟩,⟨0,-3125000,4937317,false⟩), (⟨24838, 0, 8⟩,⟨18686450000000,-91045850000000,103808627756611,false⟩), (⟨24839, 2, 8⟩,⟨100000000,0,-212443877,false⟩)], ⟨-100000000,0,197753243,false⟩⟩
private theorem angle06_exact : poseAngle 1383 = 6 := by
  decide +kernel
private theorem radius06_exact : poseRadius 1383 = radius6 := by
  unfold poseRadius; rw [angle06_exact]; rfl
private theorem cache06_exact : cache06.Exact plan06 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache06.inputs = cutRows 1383
    simp only [cutRows,lowerCut,upperCut,radius06_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache06.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache06.supports) (by decide +kernel)
  · change cache06.closing = upper (leftHi + (poseRadius 1383).radius) false
    rw [radius06_exact]
    decide +kernel
private theorem shape06 : plan06.Shape := by decide +kernel
private theorem numeric06 : cache06.Numeric plan06 := by
  decide +kernel
private theorem plan06_checked : plan06.Check :=
  cache06.toCheck plan06 cache06_exact shape06 numeric06

def plan07 : DirectPlan := ⟨1384, some 3066, [⟨24841, 0, 2⟩, ⟨24842, 0, 3⟩, ⟨24843, 0, 4⟩, ⟨24844, 1, 2⟩, ⟨24845, 1, 8⟩, ⟨24846, 0, 8⟩, ⟨24847, 2, 8⟩], 0, 0⟩
private def cache07 : PlanCache := ⟨[⟨1250000,0,-2451797,true⟩, ⟨-100000000,0,215874377,true⟩, ⟨526375350000000,125087050000000,-1307418038117883,false⟩, ⟨0,20000000,-29520171,false⟩, ⟨-90651200000000,381466900000000,-369684071490507,false⟩, ⟨-25000000,0,55233803,false⟩, ⟨-263187675000000,-62543500000000,674923042843921,false⟩, ⟨0,-100000000,159941587,false⟩, ⟨181302400000000,-762933900000000,824223824699489,false⟩, ⟨25000000,0,-52700983,false⟩, ⟨25000000,0,-52700983,false⟩, ⟨-25000000,0,55233803,false⟩, ⟨0,20000000,-29520171,false⟩, ⟨0,-100000000,159941587,false⟩, ⟨0,0,1,true⟩], [(⟨24841, 0, 2⟩,⟨526375350000000,125087050000000,-1307416735193083,false⟩), (⟨24842, 0, 3⟩,⟨0,20000000,-29520131,false⟩), (⟨24843, 0, 4⟩,⟨-61035100000000,256840300000000,-248906389531991,false⟩), (⟨24844, 1, 2⟩,⟨-100000000,0,215874477,false⟩), (⟨24845, 1, 8⟩,⟨0,-2500000,3983343,false⟩), (⟨24846, 0, 8⟩,⟨120495700000000,-507054500000000,547789576086311,false⟩), (⟨24847, 2, 8⟩,⟨25000000,0,-52700933,false⟩)], ⟨-1250000,0,2451797,false⟩⟩
private theorem angle07_exact : poseAngle 1384 = 7 := by
  decide +kernel
private theorem radius07_exact : poseRadius 1384 = radius7 := by
  unfold poseRadius; rw [angle07_exact]; rfl
private theorem cache07_exact : cache07.Exact plan07 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache07.inputs = cutRows 1384
    simp only [cutRows,lowerCut,upperCut,radius07_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache07.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache07.supports) (by decide +kernel)
  · change cache07.closing = upper (leftHi + (poseRadius 1384).radius) false
    rw [radius07_exact]
    decide +kernel
private theorem shape07 : plan07.Shape := by decide +kernel
private theorem numeric07 : cache07.Numeric plan07 := by
  decide +kernel
private theorem plan07_checked : plan07.Check :=
  cache07.toCheck plan07 cache07_exact shape07 numeric07

def plan08 : DirectPlan := ⟨1385, some 3068, [⟨24849, 0, 2⟩, ⟨24850, 0, 3⟩, ⟨24851, 0, 4⟩, ⟨24852, 1, 2⟩, ⟨24853, 1, 8⟩, ⟨24854, 0, 8⟩, ⟨24855, 2, 8⟩], 0, 0⟩
private def cache08 : PlanCache := ⟨[⟨6250000,0,-12160823,true⟩, ⟨-100000000,0,217444969,true⟩, ⟨112061390000000,30300790000000,-282458419600557,false⟩, ⟨0,20000000,-29458791,false⟩, ⟨-334526171875,1237178125000,-1112325114528,false⟩, ⟨-3125000,0,6929097,false⟩, ⟨-1120613900000000,-303007900000000,2938847261759499,false⟩, ⟨0,-6250000,10066841,false⟩, ⟨10704837500000,-39589700000000,40355346601671,false⟩, ⟨1562500,0,-3268739,false⟩, ⟨1562500,0,-3268739,false⟩, ⟨-3125000,0,6929097,false⟩, ⟨0,20000000,-29458791,false⟩, ⟨0,-6250000,10066841,false⟩, ⟨0,0,1,true⟩], [(⟨24849, 0, 2⟩,⟨112061390000000,30300790000000,-282458134876197,false⟩), (⟨24850, 0, 3⟩,⟨0,20000000,-29458751,false⟩), (⟨24851, 0, 4⟩,⟨-47006200000000,173843100000000,-156298876832293,false⟩), (⟨24852, 1, 2⟩,⟨-100000000,0,217445069,false⟩), (⟨24853, 1, 8⟩,⟨0,-100000000,160730107,false⟩), (⟨24854, 0, 8⟩,⟨74320400000000,-274859100000000,280175429108961,false⟩), (⟨24855, 2, 8⟩,⟨12500000,0,-26149887,false⟩)], ⟨-6250000,0,12160823,false⟩⟩
private theorem angle08_exact : poseAngle 1385 = 8 := by
  decide +kernel
private theorem radius08_exact : poseRadius 1385 = radius8 := by
  unfold poseRadius; rw [angle08_exact]; rfl
private theorem cache08_exact : cache08.Exact plan08 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache08.inputs = cutRows 1385
    simp only [cutRows,lowerCut,upperCut,radius08_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache08.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache08.supports) (by decide +kernel)
  · change cache08.closing = upper (leftHi + (poseRadius 1385).radius) false
    rw [radius08_exact]
    decide +kernel
private theorem shape08 : plan08.Shape := by decide +kernel
private theorem numeric08 : cache08.Numeric plan08 := by
  decide +kernel
private theorem plan08_checked : plan08.Check :=
  cache08.toCheck plan08 cache08_exact shape08 numeric08

def plan09 : DirectPlan := ⟨1386, some 3070, [⟨24857, 0, 2⟩, ⟨24858, 0, 3⟩, ⟨24859, 0, 4⟩, ⟨24860, 1, 2⟩, ⟨24861, 6, 7⟩, ⟨24862, 0, 7⟩, ⟨24863, 0, 8⟩, ⟨24864, 2, 8⟩], 0, 0⟩
private def cache09 : PlanCache := ⟨[⟨100000000,0,-193050689,true⟩, ⟨-12500000,0,27370931,true⟩, ⟨117591130000000,35696390000000,-300830475709857,false⟩, ⟨0,25000000,-36745329,false⟩, ⟨-343546300000000,1131711300000000,-937801591837299,false⟩, ⟨-1562500,0,3476979,false⟩, ⟨-36747231250000,-11155125000000,98551587013437,false⟩, ⟨0,-50000000,81088047,false⟩, ⟨42943300000000,-141463900000000,135393345504171,false⟩, ⟨100000000,0,-207639703,false⟩, ⟨100000000,0,-207639703,false⟩, ⟨-1562500,0,3476979,false⟩, ⟨0,25000000,-36745329,false⟩, ⟨0,-50000000,81088047,false⟩, ⟨0,0,1,true⟩], [(⟨24857, 0, 2⟩,⟨117591130000000,35696390000000,-300830169134817,false⟩), (⟨24858, 0, 3⟩,⟨0,25000000,-36745279,false⟩), (⟨24859, 0, 4⟩,⟨-117749300000000,387890250000000,-321427424390891,false⟩), (⟨24860, 1, 2⟩,⟨-25000000,0,54741887,false⟩), (⟨24861, 6, 7⟩,⟨-141812500000,-43050000000,380325596507,false⟩), (⟨24862, 0, 7⟩,⟨0,-50000000,81088147,false⟩), (⟨24863, 0, 8⟩,⟨42943300000000,-141463900000000,135393714318571,false⟩), (⟨24864, 2, 8⟩,⟨100000000,0,-207639503,false⟩)], ⟨-100000000,0,193050689,false⟩⟩
private theorem angle09_exact : poseAngle 1386 = 9 := by
  decide +kernel
private theorem radius09_exact : poseRadius 1386 = radius9 := by
  unfold poseRadius; rw [angle09_exact]; rfl
private theorem cache09_exact : cache09.Exact plan09 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache09.inputs = cutRows 1386
    simp only [cutRows,lowerCut,upperCut,radius09_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache09.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache09.supports) (by decide +kernel)
  · change cache09.closing = upper (leftHi + (poseRadius 1386).radius) false
    rw [radius09_exact]
    decide +kernel
private theorem shape09 : plan09.Shape := by decide +kernel
private theorem numeric09 : cache09.Numeric plan09 := by
  decide +kernel
private theorem plan09_checked : plan09.Check :=
  cache09.toCheck plan09 cache09_exact shape09 numeric09

def plan10 : DirectPlan := ⟨1387, some 3072, [⟨24866, 0, 2⟩, ⟨24867, 0, 3⟩, ⟨24868, 0, 4⟩, ⟨24869, 1, 2⟩, ⟨24870, 0, 6⟩, ⟨24871, 0, 7⟩, ⟨24872, 0, 8⟩, ⟨24873, 2, 8⟩], 0, 0⟩
private def cache10 : PlanCache := ⟨[⟨50000000,0,-95792457,true⟩, ⟨-100000000,0,220433223,true⟩, ⟨60189445000000,20295955000000,-156312154886701,false⟩, ⟨0,50000000,-73408703,false⟩, ⟨-36724400000000,108909450000000,-82705739783919,false⟩, ⟨-100000000,0,223262601,false⟩, ⟨-1203788900000000,-405919200000000,3301459831365009,false⟩, ⟨0,-12500000,20407803,false⟩, ⟨55086600000000,-163364162500000,145960697266671,false⟩, ⟨4000000,0,-8245363,false⟩, ⟨4000000,0,-8245363,false⟩, ⟨-100000000,0,223262601,false⟩, ⟨0,50000000,-73408703,false⟩, ⟨0,-12500000,20407803,false⟩, ⟨0,0,1,true⟩], [(⟨24866, 0, 2⟩,⟨60189445000000,20295955000000,-156311993915901,false⟩), (⟨24867, 0, 3⟩,⟨0,50000000,-73408603,false⟩), (⟨24868, 0, 4⟩,⟨-43160300000000,127995700000000,-97199493281941,false⟩), (⟨24869, 1, 2⟩,⟨-100000000,0,220433323,false⟩), (⟨24870, 0, 6⟩,⟨-45585300000000,-15371425000000,125020414574669,false⟩), (⟨24871, 0, 7⟩,⟨0,-3125000,5101957,false⟩), (⟨24872, 0, 8⟩,⟨13771650000000,-40841040625000,36490283542049,false⟩), (⟨24873, 2, 8⟩,⟨800000,0,-1649071,false⟩)], ⟨-50000000,0,95792457,false⟩⟩
private theorem angle10_exact : poseAngle 1387 = 10 := by
  decide +kernel
private theorem radius10_exact : poseRadius 1387 = radius10 := by
  unfold poseRadius; rw [angle10_exact]; rfl
private theorem cache10_exact : cache10.Exact plan10 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache10.inputs = cutRows 1387
    simp only [cutRows,lowerCut,upperCut,radius10_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache10.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache10.supports) (by decide +kernel)
  · change cache10.closing = upper (leftHi + (poseRadius 1387).radius) false
    rw [radius10_exact]
    decide +kernel
private theorem shape10 : plan10.Shape := by decide +kernel
private theorem numeric10 : cache10.Numeric plan10 := by
  decide +kernel
private theorem plan10_checked : plan10.Check :=
  cache10.toCheck plan10 cache10_exact shape10 numeric10

def plan11 : DirectPlan := ⟨1388, some 3074, [⟨24875, 0, 2⟩, ⟨24876, 0, 3⟩, ⟨24877, 0, 4⟩, ⟨24878, 1, 2⟩, ⟨24879, 0, 6⟩, ⟨24880, 0, 7⟩, ⟨24881, 0, 8⟩, ⟨24882, 2, 8⟩], 0, 0⟩
private def cache11 : PlanCache := ⟨[⟨50000000,0,-95091873,true⟩, ⟨-100000000,0,221834391,true⟩, ⟨289197150000000,107397850000000,-762562410325929,false⟩, ⟨0,50000000,-73641687,false⟩, ⟨-136951550000000,368778275000000,-256938450124393,false⟩, ⟨-12500000,0,27967239,false⟩, ⟨-1156788500000000,-429591300000000,3244425138445701,false⟩, ⟨0,-50000000,82164761,false⟩, ⟨273903050000000,-737556600000000,610965457562613,false⟩, ⟨50000000,0,-102345333,false⟩, ⟨50000000,0,-102345333,false⟩, ⟨-12500000,0,27967239,false⟩, ⟨0,50000000,-73641687,false⟩, ⟨0,-50000000,82164761,false⟩, ⟨0,0,1,true⟩], [(⟨24875, 0, 2⟩,⟨289197150000000,107397850000000,-762561617135929,false⟩), (⟨24876, 0, 3⟩,⟨0,50000000,-73641587,false⟩), (⟨24877, 0, 4⟩,⟨-238556100000000,642375500000000,-447559834017029,false⟩), (⟨24878, 1, 2⟩,⟨-100000000,0,221834491,false⟩), (⟨24879, 0, 6⟩,⟨-40261750000000,-14951825000000,112921562012309,false⟩), (⟨24880, 0, 7⟩,⟨0,-50000000,82164861,false⟩), (⟨24881, 0, 8⟩,⟨273903050000000,-737556600000000,610967480481913,false⟩), (⟨24882, 2, 8⟩,⟨50000000,0,-102345233,false⟩)], ⟨-50000000,0,95091873,false⟩⟩
private theorem angle11_exact : poseAngle 1388 = 11 := by
  decide +kernel
private theorem radius11_exact : poseRadius 1388 = radius11 := by
  unfold poseRadius; rw [angle11_exact]; rfl
private theorem cache11_exact : cache11.Exact plan11 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache11.inputs = cutRows 1388
    simp only [cutRows,lowerCut,upperCut,radius11_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache11.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache11.supports) (by decide +kernel)
  · change cache11.closing = upper (leftHi + (poseRadius 1388).radius) false
    rw [radius11_exact]
    decide +kernel
private theorem shape11 : plan11.Shape := by decide +kernel
private theorem numeric11 : cache11.Numeric plan11 := by
  decide +kernel
private theorem plan11_checked : plan11.Check :=
  cache11.toCheck plan11 cache11_exact shape11 numeric11

def plan12 : DirectPlan := ⟨1389, some 3076, [⟨24884, 0, 2⟩, ⟨24885, 0, 3⟩, ⟨24886, 0, 4⟩, ⟨24887, 1, 2⟩, ⟨24888, 0, 6⟩, ⟨24889, 0, 7⟩, ⟨24890, 0, 8⟩, ⟨24891, 2, 8⟩], 0, 0⟩
private def cache12 : PlanCache := ⟨[⟨50000000,0,-94427179,true⟩, ⟨-100000000,0,223163779,true⟩, ⟨1100303900000000,446852200000000,-2946417926856607,false⟩, ⟨0,100000000,-147732413,false⟩, ⟨-166073350000000,408929700000000,-259044974043371,false⟩, ⟨-6250000,0,14008933,false⟩, ⟨-275075975000000,-111713075000000,789021016308449,false⟩, ⟨0,-100000000,165378587,false⟩, ⟨664293400000000,-1635718700000000,1245847234680233,false⟩, ⟨100000000,0,-203317017,false⟩, ⟨100000000,0,-203317017,false⟩, ⟨-6250000,0,14008933,false⟩, ⟨0,100000000,-147732413,false⟩, ⟨0,-100000000,165378587,false⟩, ⟨0,0,1,true⟩], [(⟨24884, 0, 2⟩,⟨1100303900000000,446852200000000,-2946414832544407,false⟩), (⟨24885, 0, 3⟩,⟨0,100000000,-147732213,false⟩), (⟨24886, 0, 4⟩,⟨-624524400000000,1537793900000000,-974143064779647,false⟩), (⟨24887, 1, 2⟩,⟨-100000000,0,223163879,false⟩), (⟨24888, 0, 6⟩,⟨-859179100000000,-348927400000000,2464450195798193,false⟩), (⟨24889, 0, 7⟩,⟨0,-100000000,165378787,false⟩), (⟨24890, 0, 8⟩,⟨664293400000000,-1635718700000000,1245851834704433,false⟩), (⟨24891, 2, 8⟩,⟨100000000,0,-203316817,false⟩)], ⟨-50000000,0,94427179,false⟩⟩
private theorem angle12_exact : poseAngle 1389 = 12 := by
  decide +kernel
private theorem radius12_exact : poseRadius 1389 = radius12 := by
  unfold poseRadius; rw [angle12_exact]; rfl
private theorem cache12_exact : cache12.Exact plan12 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache12.inputs = cutRows 1389
    simp only [cutRows,lowerCut,upperCut,radius12_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache12.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache12.supports) (by decide +kernel)
  · change cache12.closing = upper (leftHi + (poseRadius 1389).radius) false
    rw [radius12_exact]
    decide +kernel
private theorem shape12 : plan12.Shape := by decide +kernel
private theorem numeric12 : cache12.Numeric plan12 := by
  decide +kernel
private theorem plan12_checked : plan12.Check :=
  cache12.toCheck plan12 cache12_exact shape12 numeric12

def plan13 : DirectPlan := ⟨1390, some 3078, [⟨24893, 0, 2⟩, ⟨24894, 0, 3⟩, ⟨24895, 0, 4⟩, ⟨24896, 1, 2⟩, ⟨24897, 0, 6⟩, ⟨24898, 0, 7⟩, ⟨24899, 0, 8⟩, ⟨24900, 2, 8⟩], 0, 0⟩
private def cache13 : PlanCache := ⟨[⟨50000000,0,-93801583,true⟩, ⟨-100000000,0,224414971,true⟩, ⟨1035020500000000,456982600000000,-2815335641128757,false⟩, ⟨0,12500000,-18520659,false⟩, ⟨-10669250000000,24164800000000,-13762244688191,false⟩, ⟨-10000000,0,22447189,false⟩, ⟨-258755100000000,-114245650000000,759125045115157,false⟩, ⟨0,-50000000,83205461,false⟩, ⟨197381100000000,-447048800000000,309893313760043,false⟩, ⟨100000000,0,-202019911,false⟩, ⟨100000000,0,-202019911,false⟩, ⟨-10000000,0,22447189,false⟩, ⟨0,12500000,-18520659,false⟩, ⟨0,-50000000,83205461,false⟩, ⟨0,0,1,true⟩], [(⟨24893, 0, 2⟩,⟨1035020500000000,456982600000000,-2815332657122557,false⟩), (⟨24894, 0, 3⟩,⟨0,6250000,-9260317,false⟩), (⟨24895, 0, 4⟩,⟨-393503450000000,891246650000000,-507576920280327,false⟩), (⟨24896, 1, 2⟩,⟨-100000000,0,224415071,false⟩), (⟨24897, 0, 6⟩,⟨-511053050000000,-225640350000000,1499307865310779,false⟩), (⟨24898, 0, 7⟩,⟨0,-50000000,83205561,false⟩), (⟨24899, 0, 8⟩,⟨197381100000000,-447048800000000,309894602619843,false⟩), (⟨24900, 2, 8⟩,⟨100000000,0,-202019711,false⟩)], ⟨-50000000,0,93801583,false⟩⟩
private theorem angle13_exact : poseAngle 1390 = 13 := by
  decide +kernel
private theorem radius13_exact : poseRadius 1390 = radius13 := by
  unfold poseRadius; rw [angle13_exact]; rfl
private theorem cache13_exact : cache13.Exact plan13 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache13.inputs = cutRows 1390
    simp only [cutRows,lowerCut,upperCut,radius13_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache13.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache13.supports) (by decide +kernel)
  · change cache13.closing = upper (leftHi + (poseRadius 1390).radius) false
    rw [radius13_exact]
    decide +kernel
private theorem shape13 : plan13.Shape := by decide +kernel
private theorem numeric13 : cache13.Numeric plan13 := by
  decide +kernel
private theorem plan13_checked : plan13.Check :=
  cache13.toCheck plan13 cache13_exact shape13 numeric13

def plan14 : DirectPlan := ⟨1391, some 3080, [⟨24902, 0, 2⟩, ⟨24903, 0, 3⟩, ⟨24904, 0, 4⟩, ⟨24905, 0, 5⟩, ⟨24906, 1, 2⟩, ⟨24907, 0, 7⟩, ⟨24908, 0, 8⟩, ⟨24909, 0, 9⟩, ⟨24910, 2, 9⟩], 0, 0⟩
private def cache14 : PlanCache := ⟨[⟨100000000,0,-186435797,true⟩, ⟨-5000000,0,11279117,true⟩, ⟨480836950000000,229668250000000,-1328880000323227,false⟩, ⟨0,100000000,-148582599,false⟩, ⟨-4323911200000,15448533600000,-14072565737231,false⟩, ⟨-17853700000000,37378800000000,-17439699273251,false⟩, ⟨-100000000,0,226204741,false⟩, ⟨-254521520000000,-121570340000000,763811294332409,false⟩, ⟨0,-100000000,167427913,false⟩, ⟨922837400000000,-1932066700000000,1203413686201369,false⟩, ⟨25000000,0,-50201339,false⟩, ⟨25000000,0,-50201339,false⟩, ⟨-100000000,0,226204741,false⟩, ⟨0,100000000,-148582599,false⟩, ⟨0,-100000000,167427913,false⟩, ⟨0,0,1,true⟩], [(⟨24902, 0, 2⟩,⟨480836950000000,229668250000000,-1328878579312827,false⟩), (⟨24903, 0, 3⟩,⟨0,100000000,-148582399,false⟩), (⟨24904, 0, 4⟩,⟨-21619556000000,77242668000000,-70362630961707,false⟩), (⟨24905, 0, 5⟩,⟨-41681500000000,87265100000000,-40714750158453,false⟩), (⟨24906, 1, 2⟩,⟨-2500000,0,5639561,false⟩), (⟨24907, 0, 7⟩,⟨-7139248750000,-3410010000000,21424688369951,false⟩), (⟨24908, 0, 8⟩,⟨0,-100000000,167428113,false⟩), (⟨24909, 0, 9⟩,⟨922837400000000,-1932066700000000,1203419396009569,false⟩), (⟨24910, 2, 9⟩,⟨25000000,0,-50201289,false⟩)], ⟨-100000000,0,186435797,false⟩⟩
private theorem angle14_exact : poseAngle 1391 = 14 := by
  decide +kernel
private theorem radius14_exact : poseRadius 1391 = radius14 := by
  unfold poseRadius; rw [angle14_exact]; rfl
private theorem cache14_exact : cache14.Exact plan14 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache14.inputs = cutRows 1391
    simp only [cutRows,lowerCut,upperCut,radius14_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache14.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache14.supports) (by decide +kernel)
  · change cache14.closing = upper (leftHi + (poseRadius 1391).radius) false
    rw [radius14_exact]
    decide +kernel
private theorem shape14 : plan14.Shape := by decide +kernel
private theorem numeric14 : cache14.Numeric plan14 := by
  decide +kernel
private theorem plan14_checked : plan14.Check :=
  cache14.toCheck plan14 cache14_exact shape14 numeric14

def plan15 : DirectPlan := ⟨1392, some 3082, [⟨24912, 0, 2⟩, ⟨24913, 0, 3⟩, ⟨24914, 0, 4⟩, ⟨24915, 0, 5⟩, ⟨24916, 1, 2⟩, ⟨24917, 0, 7⟩, ⟨24918, 0, 8⟩, ⟨24919, 0, 9⟩, ⟨24920, 2, 9⟩], 0, 0⟩
private def cache15 : PlanCache := ⟨[⟨20000000,0,-37071417,true⟩, ⟨-25000000,0,56665263,true⟩, ⟨881041300000000,453345300000000,-2474608370088471,false⟩, ⟨0,50000000,-74492467,false⟩, ⟨-249966550000000,950119000000000,-905071939057043,false⟩, ⟨-92899600000000,180543100000000,-70642500575591,false⟩, ⟨-6250000,0,14176591,false⟩, ⟨-314713625000000,-161937850000000,966218540872733,false⟩, ⟨0,-100000000,168431003,false⟩, ⟨265886375000000,-516729525000000,284458100815347,false⟩, ⟨625000,0,-1247991,false⟩, ⟨625000,0,-1247991,false⟩, ⟨-6250000,0,14176591,false⟩, ⟨0,50000000,-74492467,false⟩, ⟨0,-100000000,168431003,false⟩, ⟨0,0,1,true⟩], [(⟨24912, 0, 2⟩,⟨881041300000000,453345300000000,-2474605701315271,false⟩), (⟨24913, 0, 3⟩,⟨0,50000000,-74492367,false⟩), (⟨24914, 0, 4⟩,⟨-249966550000000,950119000000000,-905069538885943,false⟩), (⟨24915, 0, 5⟩,⟨-2955575000000,5743930000000,-2247456256989,false⟩), (⟨24916, 1, 2⟩,⟨-3125000,0,7083161,false⟩), (⟨24917, 0, 7⟩,⟨-613442200000000,-315650500000000,1883362424369439,false⟩), (⟨24918, 0, 8⟩,⟨0,-100000000,168431203,false⟩), (⟨24919, 0, 9⟩,⟨265886375000000,-516729525000000,284459666047147,false⟩), (⟨24920, 2, 9⟩,⟨2500000,0,-4991959,false⟩)], ⟨-20000000,0,37071417,false⟩⟩
private theorem angle15_exact : poseAngle 1392 = 15 := by
  decide +kernel
private theorem radius15_exact : poseRadius 1392 = radius15 := by
  unfold poseRadius; rw [angle15_exact]; rfl
private theorem cache15_exact : cache15.Exact plan15 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache15.inputs = cutRows 1392
    simp only [cutRows,lowerCut,upperCut,radius15_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache15.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache15.supports) (by decide +kernel)
  · change cache15.closing = upper (leftHi + (poseRadius 1392).radius) false
    rw [radius15_exact]
    decide +kernel
private theorem shape15 : plan15.Shape := by decide +kernel
private theorem numeric15 : cache15.Numeric plan15 := by
  decide +kernel
private theorem plan15_checked : plan15.Check :=
  cache15.toCheck plan15 cache15_exact shape15 numeric15

def plan16 : DirectPlan := ⟨1393, some 3084, [⟨24922, 0, 2⟩, ⟨24923, 0, 3⟩, ⟨24924, 0, 4⟩, ⟨24925, 0, 5⟩, ⟨24926, 2, 6⟩, ⟨24927, 0, 7⟩, ⟨24928, 0, 8⟩, ⟨24929, 0, 9⟩, ⟨24930, 2, 9⟩], 0, 0⟩
private def cache16 : PlanCache := ⟨[⟨5000000,0,-9218553,true⟩, ⟨-100000000,0,227647077,true⟩, ⟨31757336000000,17540764000000,-90677753646919,false⟩, ⟨0,20000000,-29874543,false⟩, ⟨-228965150000000,936028900000000,-933305403191261,false⟩, ⟨-10386650000000,18804900000000,-5918137667731,false⟩, ⟨-25000000,0,56847841,false⟩, ⟨-617672950000000,-341163850000000,1940394912072677,false⟩, ⟨0,-100000000,169421673,false⟩, ⟨151367787500000,-274049525000000,130430561129831,false⟩, ⟨25000000,0,-49660981,false⟩, ⟨25000000,0,-49660981,false⟩, ⟨-25000000,0,56847841,false⟩, ⟨0,20000000,-29874543,false⟩, ⟨0,-100000000,169421673,false⟩, ⟨0,0,1,true⟩], [(⟨24922, 0, 2⟩,⟨31757336000000,17540764000000,-90677655050719,false⟩), (⟨24923, 0, 3⟩,⟨0,20000000,-29874503,false⟩), (⟨24924, 0, 4⟩,⟨-228965150000000,936028900000000,-933303073203161,false⟩), (⟨24925, 0, 5⟩,⟨-10386650000000,18804900000000,-5918079284631,false⟩), (⟨24926, 2, 6⟩,⟨-25000000,0,56847891,false⟩), (⟨24927, 0, 7⟩,⟨-617672950000000,-341163850000000,1940396829746277,false⟩), (⟨24928, 0, 8⟩,⟨0,-100000000,169421873,false⟩), (⟨24929, 0, 9⟩,⟨18920973437500,-34256190625000,16303926495557,false⟩), (⟨24930, 2, 9⟩,⟨25000000,0,-49660931,false⟩)], ⟨-5000000,0,9218553,false⟩⟩
private theorem angle16_exact : poseAngle 1393 = 16 := by
  decide +kernel
private theorem radius16_exact : poseRadius 1393 = radius16 := by
  unfold poseRadius; rw [angle16_exact]; rfl
private theorem cache16_exact : cache16.Exact plan16 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache16.inputs = cutRows 1393
    simp only [cutRows,lowerCut,upperCut,radius16_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache16.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache16.supports) (by decide +kernel)
  · change cache16.closing = upper (leftHi + (poseRadius 1393).radius) false
    rw [radius16_exact]
    decide +kernel
private theorem shape16 : plan16.Shape := by decide +kernel
private theorem numeric16 : cache16.Numeric plan16 := by
  decide +kernel
private theorem plan16_checked : plan16.Check :=
  cache16.toCheck plan16 cache16_exact shape16 numeric16

def plan17 : DirectPlan := ⟨1394, some 3086, [⟨24931, 0, 2⟩, ⟨24932, 0, 3⟩, ⟨24933, 0, 4⟩, ⟨24934, 0, 5⟩, ⟨24935, 2, 6⟩, ⟨24936, 0, 7⟩, ⟨24937, 0, 8⟩, ⟨24938, 0, 9⟩, ⟨24939, 0, 10⟩, ⟨24940, 2, 10⟩], 0, 0⟩
private def cache17 : PlanCache := ⟨[⟨25000000,0,-45870239,true⟩, ⟨-100000000,0,228537181,true⟩, ⟨175296350000000,103612050000000,-508990043510727,false⟩, ⟨0,50000000,-74873139,false⟩, ⟨-207338500000000,923289600000000,-964079610798423,false⟩, ⟨-44807820000000,75808240000000,-17945029089413,false⟩, ⟨-20000000,0,45579269,false⟩, ⟨-1124542700000000,-664681200000000,3615474121003487,false⟩, ⟨0,-50000000,84809729,false⟩, ⟨33651975000000,-101563100000000,97816009855691,false⟩, ⟨115150460000000,-194817620000000,77734583590063,false⟩, ⟨50000000,0,-98852523,false⟩, ⟨50000000,0,-98852523,false⟩, ⟨-20000000,0,45579269,false⟩, ⟨0,50000000,-74873139,false⟩, ⟨0,-50000000,84809729,false⟩, ⟨0,0,1,true⟩], [(⟨24931, 0, 2⟩,⟨175296350000000,103612050000000,-508989485693927,false⟩), (⟨24932, 0, 3⟩,⟨0,50000000,-74873039,false⟩), (⟨24933, 0, 4⟩,⟨-207338500000000,923289600000000,-964077349542223,false⟩), (⟨24934, 0, 5⟩,⟨-44807820000000,75808240000000,-17944787857293,false⟩), (⟨24935, 2, 6⟩,⟨-20000000,0,45579309,false⟩), (⟨24936, 0, 7⟩,⟨-1124542700000000,-664681200000000,3615477699451287,false⟩), (⟨24937, 0, 8⟩,⟨0,-50000000,84809829,false⟩), (⟨24938, 0, 9⟩,⟨33651975000000,-101563100000000,97816280285841,false⟩), (⟨24939, 0, 10⟩,⟨115150460000000,-194817620000000,77735203526223,false⟩), (⟨24940, 2, 10⟩,⟨50000000,0,-98852423,false⟩)], ⟨-25000000,0,45870239,false⟩⟩
private theorem angle17_exact : poseAngle 1394 = 17 := by
  decide +kernel
private theorem radius17_exact : poseRadius 1394 = radius17 := by
  unfold poseRadius; rw [angle17_exact]; rfl
private theorem cache17_exact : cache17.Exact plan17 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache17.inputs = cutRows 1394
    simp only [cutRows,lowerCut,upperCut,radius17_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache17.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache17.supports) (by decide +kernel)
  · change cache17.closing = upper (leftHi + (poseRadius 1394).radius) false
    rw [radius17_exact]
    decide +kernel
private theorem shape17 : plan17.Shape := by decide +kernel
private theorem numeric17 : cache17.Numeric plan17 := by
  decide +kernel
private theorem plan17_checked : plan17.Check :=
  cache17.toCheck plan17 cache17_exact shape17 numeric17

def plan18 : DirectPlan := ⟨1395, some 3088, [⟨24941, 0, 2⟩, ⟨24942, 0, 3⟩, ⟨24943, 0, 4⟩, ⟨24944, 0, 5⟩, ⟨24945, 2, 6⟩, ⟨24946, 0, 7⟩, ⟨24947, 0, 8⟩, ⟨24948, 0, 9⟩, ⟨24949, 0, 10⟩, ⟨24950, 2, 10⟩], 0, 0⟩
private def cache18 : PlanCache := ⟨[⟨4000000,0,-7307569,true⟩, ⟨-6250000,0,14333057,true⟩, ⟨603649100000000,380803600000000,-1782967842028683,false⟩, ⟨0,50000000,-75052931,false⟩, ⟨-185184800000000,911919350000000,-997228577728521,false⟩, ⟨-14861660000000,23558680000000,-3701641188841,false⟩, ⟨-100000000,0,228334821,false⟩, ⟨-57045350000000,-35986250000000,187744023858161,false⟩, ⟨-30899900000000,-226920200000000,452002720662137,false⟩, ⟨0,-100000000,169499677,false⟩, ⟨1335712300000000,-2117369100000000,676567844160639,false⟩, ⟨4000000,0,-7874589,false⟩, ⟨4000000,0,-7874589,false⟩, ⟨-100000000,0,228334821,false⟩, ⟨0,50000000,-75052931,false⟩, ⟨0,-100000000,169499677,false⟩, ⟨0,0,1,true⟩], [(⟨24941, 0, 2⟩,⟨603649100000000,380803600000000,-1782965873123283,false⟩), (⟨24942, 0, 3⟩,⟨0,50000000,-75052831,false⟩), (⟨24943, 0, 4⟩,⟨-185184800000000,911919350000000,-997226383520221,false⟩), (⟨24944, 0, 5⟩,⟨-14861660000000,23558680000000,-3701564348161,false⟩), (⟨24945, 2, 6⟩,⟨-100000000,0,228335021,false⟩), (⟨24946, 0, 7⟩,⟨-57045350000000,-35986250000000,187744209921361,false⟩), (⟨24947, 0, 8⟩,⟨-30899900000000,-226920200000000,452003236302337,false⟩), (⟨24948, 0, 9⟩,⟨0,-100000000,169499877,false⟩), (⟨24949, 0, 10⟩,⟨1335712300000000,-2117369100000000,676574750323439,false⟩), (⟨24950, 2, 10⟩,⟨4000000,0,-7874581,false⟩)], ⟨-4000000,0,7307569,false⟩⟩
private theorem angle18_exact : poseAngle 1395 = 18 := by
  decide +kernel
private theorem radius18_exact : poseRadius 1395 = radius18 := by
  unfold poseRadius; rw [angle18_exact]; rfl
private theorem cache18_exact : cache18.Exact plan18 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache18.inputs = cutRows 1395
    simp only [cutRows,lowerCut,upperCut,radius18_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache18.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache18.supports) (by decide +kernel)
  · change cache18.closing = upper (leftHi + (poseRadius 1395).radius) false
    rw [radius18_exact]
    decide +kernel
private theorem shape18 : plan18.Shape := by decide +kernel
private theorem numeric18 : cache18.Numeric plan18 := by
  decide +kernel
private theorem plan18_checked : plan18.Check :=
  cache18.toCheck plan18 cache18_exact shape18 numeric18

def plan19 : DirectPlan := ⟨1396, some 3090, [⟨24951, 0, 2⟩, ⟨24952, 0, 3⟩, ⟨24953, 0, 4⟩, ⟨24954, 0, 5⟩, ⟨24955, 2, 6⟩, ⟨24956, 0, 7⟩, ⟨24957, 0, 8⟩, ⟨24958, 0, 9⟩, ⟨24959, 0, 10⟩, ⟨24960, 2, 10⟩], 0, 0⟩
private def cache19 : PlanCache := ⟨[⟨100000000,0,-181997553,true⟩, ⟨-12500000,0,28752573,true⟩, ⟨83697500000000,56222550000000,-251562857315933,false⟩, ⟨0,3125000,-4701613,false⟩, ⟨-13550125000000,75160725000000,-86048223816641,false⟩, ⟨-53569300000000,79747650000000,-6041936439317,false⟩, ⟨-20000000,0,45740357,false⟩, ⟨-140255260000000,-94214400000000,472643239645447,false⟩, ⟨-248912900000000,-519061200000000,1430688263295329,false⟩, ⟨0,-100000000,170705441,false⟩, ⟨253862900000000,-377921100000000,89679215452543,false⟩, ⟨50000000,0,-98062493,false⟩, ⟨50000000,0,-98062493,false⟩, ⟨-20000000,0,45740357,false⟩, ⟨0,3125000,-4701613,false⟩, ⟨0,-100000000,170705441,false⟩, ⟨0,0,1,true⟩], [(⟨24951, 0, 2⟩,⟨83697500000000,56222550000000,-251562577475833,false⟩), (⟨24952, 0, 3⟩,⟨0,12500000,-18806427,false⟩), (⟨24953, 0, 4⟩,⟨-13550125000000,75160725000000,-86048046394941,false⟩), (⟨24954, 0, 5⟩,⟨-53569300000000,79747650000000,-6041669805417,false⟩), (⟨24955, 2, 6⟩,⟨-20000000,0,45740397,false⟩), (⟨24956, 0, 7⟩,⟨-140255260000000,-94214400000000,472643708584767,false⟩), (⟨24957, 0, 8⟩,⟨-248912900000000,-519061200000000,1430689799243529,false⟩), (⟨24958, 0, 9⟩,⟨0,-100000000,170705641,false⟩), (⟨24959, 0, 10⟩,⟨253862900000000,-377921100000000,89680479020543,false⟩), (⟨24960, 2, 10⟩,⟨50000000,0,-98062393,false⟩)], ⟨-100000000,0,181997553,false⟩⟩
private theorem angle19_exact : poseAngle 1396 = 19 := by
  decide +kernel
private theorem radius19_exact : poseRadius 1396 = radius19 := by
  unfold poseRadius; rw [angle19_exact]; rfl
private theorem cache19_exact : cache19.Exact plan19 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache19.inputs = cutRows 1396
    simp only [cutRows,lowerCut,upperCut,radius19_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache19.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache19.supports) (by decide +kernel)
  · change cache19.closing = upper (leftHi + (poseRadius 1396).radius) false
    rw [radius19_exact]
    decide +kernel
private theorem shape19 : plan19.Shape := by decide +kernel
private theorem numeric19 : cache19.Numeric plan19 := by
  decide +kernel
private theorem plan19_checked : plan19.Check :=
  cache19.toCheck plan19 cache19_exact shape19 numeric19

def plan20 : DirectPlan := ⟨1397, some 3092, [⟨24961, 0, 2⟩, ⟨24962, 0, 3⟩, ⟨24963, 0, 4⟩, ⟨24964, 0, 5⟩, ⟨24965, 2, 6⟩, ⟨24966, 0, 7⟩, ⟨24967, 0, 8⟩, ⟨24968, 0, 9⟩, ⟨24969, 0, 10⟩, ⟨24970, 2, 10⟩], 0, 0⟩
private def cache20 : PlanCache := ⟨[⟨50000000,0,-90703447,true⟩, ⟨-100000000,0,230611243,true⟩, ⟨56807700000000,40553200000000,-173811912777391,false⟩, ⟨0,25000000,-37695901,false⟩, ⟨-13968455000000,89332050000000,-106995003660091,false⟩, ⟨-36551128000000,51201532000000,386843971451,false⟩, ⟨-100000000,0,228992813,false⟩, ⟨-163787300000000,-116922500000000,565311916526299,false⟩, ⟨-60810400000000,-85834500000000,281001839953817,false⟩, ⟨0,-160000,275017,false⟩, ⟨1712528100000000,-2398942700000000,364840541134193,false⟩, ⟨20000000,0,-39097419,false⟩, ⟨20000000,0,-39097419,false⟩, ⟨-100000000,0,228992813,false⟩, ⟨0,25000000,-37695901,false⟩, ⟨0,-160000,275017,false⟩, ⟨0,0,1,true⟩], [(⟨24961, 0, 2⟩,⟨56807700000000,40553200000000,-173811718055591,false⟩), (⟨24962, 0, 3⟩,⟨0,25000000,-37695851,false⟩), (⟨24963, 0, 4⟩,⟨-13968455000000,89332050000000,-106994797059081,false⟩), (⟨24964, 0, 5⟩,⟨-36551128000000,51201532000000,387019476771,false⟩), (⟨24965, 2, 6⟩,⟨-100000000,0,228993013,false⟩), (⟨24966, 0, 7⟩,⟨-163787300000000,-116922500000000,565312477945899,false⟩), (⟨24967, 0, 8⟩,⟨-60810400000000,-85834500000000,281002133243617,false⟩), (⟨24968, 0, 9⟩,⟨0,-4000000,6875433,false⟩), (⟨24969, 0, 10⟩,⟨1712528100000000,-2398942700000000,364848764075793,false⟩), (⟨24970, 2, 10⟩,⟨20000000,0,-39097379,false⟩)], ⟨-50000000,0,90703447,false⟩⟩
private theorem angle20_exact : poseAngle 1397 = 20 := by
  decide +kernel
private theorem radius20_exact : poseRadius 1397 = radius20 := by
  unfold poseRadius; rw [angle20_exact]; rfl
private theorem cache20_exact : cache20.Exact plan20 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache20.inputs = cutRows 1397
    simp only [cutRows,lowerCut,upperCut,radius20_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache20.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache20.supports) (by decide +kernel)
  · change cache20.closing = upper (leftHi + (poseRadius 1397).radius) false
    rw [radius20_exact]
    decide +kernel
private theorem shape20 : plan20.Shape := by decide +kernel
private theorem numeric20 : cache20.Numeric plan20 := by
  decide +kernel
private theorem plan20_checked : plan20.Check :=
  cache20.toCheck plan20 cache20_exact shape20 numeric20

def plan21 : DirectPlan := ⟨1398, some 3094, [⟨24971, 0, 2⟩, ⟨24972, 0, 3⟩, ⟨24973, 0, 4⟩, ⟨24974, 0, 5⟩, ⟨24975, 2, 6⟩, ⟨24976, 0, 7⟩, ⟨24977, 0, 8⟩, ⟨24978, 0, 9⟩, ⟨24979, 0, 10⟩, ⟨24980, 2, 10⟩], 0, 0⟩
private def cache21 : PlanCache := ⟨[⟨100000000,0,-180917497,true⟩, ⟨-625000,0,1444379,true⟩, ⟨145455150000000,110159650000000,-453225026031601,false⟩, ⟨0,100000000,-151101811,false⟩, ⟨-233055600000000,1772180500000000,-2218316075492191,false⟩, ⟨-108506840000000,143272780000000,13329206867349,false⟩, ⟨-100000000,0,229204077,false⟩, ⟨-56821420000000,-43033380000000,200933647358811,false⟩, ⟨-39408940000000,-46536860000000,167253359457733,false⟩, ⟨0,-6250000,10814729,false⟩, ⟨190245490000000,-251200780000000,15990495483857,false⟩, ⟨250000,0,-487379,false⟩, ⟨250000,0,-487379,false⟩, ⟨-100000000,0,229204077,false⟩, ⟨0,100000000,-151101811,false⟩, ⟨0,-6250000,10814729,false⟩, ⟨0,0,1,true⟩], [(⟨24971, 0, 2⟩,⟨145455150000000,110159650000000,-453224514802001,false⟩), (⟨24972, 0, 3⟩,⟨0,100000000,-151101611,false⟩), (⟨24973, 0, 4⟩,⟨-233055600000000,1772180500000000,-2218312065019991,false⟩), (⟨24974, 0, 5⟩,⟨-108506840000000,143272780000000,13329710426589,false⟩), (⟨24975, 2, 6⟩,⟨-100000000,0,229204277,false⟩), (⟨24976, 0, 7⟩,⟨-56821420000000,-43033380000000,200933847068411,false⟩), (⟨24977, 0, 8⟩,⟨-39408940000000,-46536860000000,167253531349333,false⟩), (⟨24978, 0, 9⟩,⟨0,-12500000,21629483,false⟩), (⟨24979, 0, 10⟩,⟨190245490000000,-251200780000000,15991378376397,false⟩), (⟨24980, 2, 10⟩,⟨500000,0,-974757,false⟩)], ⟨-100000000,0,180917497,false⟩⟩
private theorem angle21_exact : poseAngle 1398 = 21 := by
  decide +kernel
private theorem radius21_exact : poseRadius 1398 = radius21 := by
  unfold poseRadius; rw [angle21_exact]; rfl
private theorem cache21_exact : cache21.Exact plan21 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache21.inputs = cutRows 1398
    simp only [cutRows,lowerCut,upperCut,radius21_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache21.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache21.supports) (by decide +kernel)
  · change cache21.closing = upper (leftHi + (poseRadius 1398).radius) false
    rw [radius21_exact]
    decide +kernel
private theorem shape21 : plan21.Shape := by decide +kernel
private theorem numeric21 : cache21.Numeric plan21 := by
  decide +kernel
private theorem plan21_checked : plan21.Check :=
  cache21.toCheck plan21 cache21_exact shape21 numeric21

def plan22 : DirectPlan := ⟨1399, some 3096, [⟨24981, 0, 2⟩, ⟨24982, 0, 3⟩, ⟨24983, 0, 4⟩, ⟨24984, 0, 5⟩, ⟨24985, 2, 6⟩, ⟨24986, 0, 7⟩, ⟨24987, 0, 8⟩, ⟨24988, 0, 9⟩, ⟨24989, 0, 10⟩, ⟨24990, 2, 10⟩], 0, 0⟩
private def cache22 : PlanCache := ⟨[⟨25000000,0,-45132237,true⟩, ⟨-100000000,0,231489189,true⟩, ⟨182795300000000,146653800000000,-580294060167231,false⟩, ⟨0,20000000,-30281231,false⟩, ⟨-93222550000000,880226800000000,-1150015247183941,false⟩, ⟨-315753400000000,393567950000000,71192549415779,false⟩, ⟨-781250,0,1791659,false⟩, ⟨-20146850000000,-16163500000000,73018643880717,false⟩, ⟨-744465500000000,-809524300000000,3052019167106391,false⟩, ⟨0,-6250000,10884467,false⟩, ⟨130732268750000,-162950056250000,-4602871146171,false⟩, ⟨100000000,0,-194518359,false⟩, ⟨100000000,0,-194518359,false⟩, ⟨-781250,0,1791659,false⟩, ⟨0,20000000,-30281231,false⟩, ⟨0,-6250000,10884467,false⟩, ⟨0,0,1,true⟩], [(⟨24981, 0, 2⟩,⟨182795300000000,146653800000000,-580293401269031,false⟩), (⟨24982, 0, 3⟩,⟨0,20000000,-30281191,false⟩), (⟨24983, 0, 4⟩,⟨-93222550000000,880226800000000,-1150013300285241,false⟩), (⟨24984, 0, 5⟩,⟨-315753400000000,393567950000000,71193968058479,false⟩), (⟨24985, 2, 6⟩,⟨-12500000,0,28666569,false⟩), (⟨24986, 0, 7⟩,⟨-20146850000000,-16163500000000,73018716501417,false⟩), (⟨24987, 0, 8⟩,⟨-744465500000000,-809524300000000,3052022275085991,false⟩), (⟨24988, 0, 9⟩,⟨0,-12500000,21768959,false⟩), (⟨24989, 0, 10⟩,⟨130732268750000,-162950056250000,-4602283781521,false⟩), (⟨24990, 2, 10⟩,⟨100000000,0,-194518159,false⟩)], ⟨-25000000,0,45132237,false⟩⟩
private theorem angle22_exact : poseAngle 1399 = 22 := by
  decide +kernel
private theorem radius22_exact : poseRadius 1399 = radius22 := by
  unfold poseRadius; rw [angle22_exact]; rfl
private theorem cache22_exact : cache22.Exact plan22 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache22.inputs = cutRows 1399
    simp only [cutRows,lowerCut,upperCut,radius22_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache22.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache22.supports) (by decide +kernel)
  · change cache22.closing = upper (leftHi + (poseRadius 1399).radius) false
    rw [radius22_exact]
    decide +kernel
private theorem shape22 : plan22.Shape := by decide +kernel
private theorem numeric22 : cache22.Numeric plan22 := by
  decide +kernel
private theorem plan22_checked : plan22.Check :=
  cache22.toCheck plan22 cache22_exact shape22 numeric22

def plan23 : DirectPlan := ⟨1400, some 3098, [⟨24991, 0, 2⟩, ⟨24992, 0, 3⟩, ⟨24993, 0, 4⟩, ⟨24994, 0, 5⟩, ⟨24995, 2, 6⟩, ⟨24996, 0, 7⟩, ⟨24997, 0, 8⟩, ⟨24998, 0, 9⟩, ⟨24999, 2, 9⟩], 0, 0⟩
private def cache23 : PlanCache := ⟨[⟨100000000,0,-180240211,true⟩, ⟨-50000000,0,115888963,true⟩, ⟨24710100000000,20974400000000,-79956612708767,false⟩, ⟨0,25000000,-37924123,false⟩, ⟨-4366053125000,54732021875000,-74520786255837,false⟩, ⟨-678279150000000,799086350000000,216841638141689,false⟩, ⟨-50000000,0,114155997,false⟩, ⟨-85700370000000,-72744040000000,316899013668863,false⟩, ⟨0,-2000000,3504589,false⟩, ⟨1139572700000000,-1342540100000000,-166356108577353,false⟩, ⟨100000000,0,-194186587,false⟩, ⟨100000000,0,-194186587,false⟩, ⟨-50000000,0,114155997,false⟩, ⟨0,25000000,-37924123,false⟩, ⟨0,-2000000,3504589,false⟩, ⟨0,0,1,true⟩], [(⟨24991, 0, 2⟩,⟨24710100000000,20974400000000,-79956521339767,false⟩), (⟨24992, 0, 3⟩,⟨0,25000000,-37924073,false⟩), (⟨24993, 0, 4⟩,⟨-4366053125000,54732021875000,-74520668059687,false⟩), (⟨24994, 0, 5⟩,⟨-678279150000000,799086350000000,216844592872689,false⟩), (⟨24995, 2, 6⟩,⟨-50000000,0,114156097,false⟩), (⟨24996, 0, 7⟩,⟨-85700370000000,-72744040000000,316899330557683,false⟩), (⟨24997, 0, 8⟩,⟨0,-2000000,3504593,false⟩), (⟨24998, 0, 9⟩,⟨1139572700000000,-1342540100000000,-166351144351753,false⟩), (⟨24999, 2, 9⟩,⟨100000000,0,-194186387,false⟩)], ⟨-100000000,0,180240211,false⟩⟩
private theorem angle23_exact : poseAngle 1400 = 23 := by
  decide +kernel
private theorem radius23_exact : poseRadius 1400 = radius23 := by
  unfold poseRadius; rw [angle23_exact]; rfl
private theorem cache23_exact : cache23.Exact plan23 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache23.inputs = cutRows 1400
    simp only [cutRows,lowerCut,upperCut,radius23_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache23.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache23.supports) (by decide +kernel)
  · change cache23.closing = upper (leftHi + (poseRadius 1400).radius) false
    rw [radius23_exact]
    decide +kernel
private theorem shape23 : plan23.Shape := by decide +kernel
private theorem numeric23 : cache23.Numeric plan23 := by
  decide +kernel
private theorem plan23_checked : plan23.Check :=
  cache23.toCheck plan23 cache23_exact shape23 numeric23

def plan24 : DirectPlan := ⟨1401, some 3100, [⟨25000, 0, 2⟩, ⟨25001, 0, 3⟩, ⟨25002, 0, 4⟩, ⟨25003, 2, 5⟩, ⟨25004, 0, 6⟩, ⟨25005, 0, 7⟩, ⟨25006, 0, 8⟩, ⟨25007, 2, 8⟩], 0, 0⟩
private def cache24 : PlanCache := ⟨[⟨100000000,0,-180049677,true⟩, ⟨-5000000,0,11598423,true⟩, ⟨781567800000,701136100000,-2721929776109,false⟩, ⟨0,6250000,-9556433,false⟩, ⟨-97172900000000,108320212500000,39505237903163,false⟩, ⟨-100000000,0,228429199,false⟩, ⟨-781567900000000,-701136200000000,2966398782521187,false⟩, ⟨0,-12500000,22033309,false⟩, ⟨388691625000000,-433280825000000,-96902983324991,false⟩, ⟨100000000,0,-204086403,false⟩, ⟨100000000,0,-204086403,false⟩, ⟨-100000000,0,228429199,false⟩, ⟨0,6250000,-9556433,false⟩, ⟨0,-12500000,22033309,false⟩, ⟨0,0,1,true⟩], [(⟨25000, 0, 2⟩,⟨1953919500000,1752840250000,-6804817026753,false⟩), (⟨25001, 0, 3⟩,⟨0,12500000,-19112841,false⟩), (⟨25002, 0, 4⟩,⟨-24293225000000,27080053125000,9876412222347,false⟩), (⟨25003, 2, 5⟩,⟨-100000000,0,228429399,false⟩), (⟨25004, 0, 6⟩,⟨-781567900000000,-701136200000000,2966401747929387,false⟩), (⟨25005, 0, 7⟩,⟨0,-6250000,11016667,false⟩), (⟨25006, 0, 8⟩,⟨388691625000000,-433280825000000,-96901339380091,false⟩), (⟨25007, 2, 8⟩,⟨100000000,0,-204086203,false⟩)], ⟨-100000000,0,180049677,false⟩⟩
private theorem angle24_exact : poseAngle 1401 = 24 := by
  decide +kernel
private theorem radius24_exact : poseRadius 1401 = radius24 := by
  unfold poseRadius; rw [angle24_exact]; rfl
private theorem cache24_exact : cache24.Exact plan24 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache24.inputs = cutRows 1401
    simp only [cutRows,lowerCut,upperCut,radius24_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache24.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache24.supports) (by decide +kernel)
  · change cache24.closing = upper (leftHi + (poseRadius 1401).radius) false
    rw [radius24_exact]
    decide +kernel
private theorem shape24 : plan24.Shape := by decide +kernel
private theorem numeric24 : cache24.Numeric plan24 := by
  decide +kernel
private theorem plan24_checked : plan24.Check :=
  cache24.toCheck plan24 cache24_exact shape24 numeric24

def plan25 : DirectPlan := ⟨1402, some 3102, [⟨25008, 0, 2⟩, ⟨25009, 0, 3⟩, ⟨25010, 0, 4⟩, ⟨25011, 1, 2⟩, ⟨25012, 0, 8⟩, ⟨25013, 0, 9⟩, ⟨25014, 0, 10⟩, ⟨25015, 2, 10⟩], 0, 0⟩
private def cache25 : PlanCache := ⟨[⟨100000000,0,-179955209,true⟩, ⟨-6250000,0,14503933,true⟩, ⟨117186750000000,111005600000000,-415470725878543,false⟩, ⟨0,100000000,-152699873,false⟩, ⟨-1172646700000000,2303844200000000,-1056676177456617,false⟩, ⟨-7734675000000,8165368750000,4590391582257,false⟩, ⟨-6250000,0,14639803,false⟩, ⟨-1379936000000,-1307148000000,5397793416899,false⟩, ⟨-562540400000000,-608689900000000,2326319053224271,false⟩, ⟨0,-100000000,177259881,false⟩, ⟨54776881250000,-57827037500000,-18955961511841,false⟩, ⟨10000000,0,-20323141,false⟩, ⟨10000000,0,-20323141,false⟩, ⟨-6250000,0,14639803,false⟩, ⟨0,100000000,-152699873,false⟩, ⟨0,-100000000,177259881,false⟩, ⟨0,0,1,true⟩], [(⟨25008, 0, 2⟩,⟨117186750000000,111005600000000,-415470269493843,false⟩), (⟨25009, 0, 3⟩,⟨0,100000000,-152699673,false⟩), (⟨25010, 0, 4⟩,⟨-1128488200000000,2217088100000000,-1016878167200259,false⟩), (⟨25011, 1, 2⟩,⟨-25000000,0,58015757,false⟩), (⟨25012, 0, 8⟩,⟨-954362800000000,-1032656500000000,3946658065259529,false⟩), (⟨25013, 0, 9⟩,⟨0,-100000000,177260081,false⟩), (⟨25014, 0, 10⟩,⟨109553762500000,-115654075000000,-37911472608007,false⟩), (⟨25015, 2, 10⟩,⟨10000000,0,-20323121,false⟩)], ⟨-100000000,0,179955209,false⟩⟩
private theorem angle25_exact : poseAngle 1402 = 25 := by
  decide +kernel
private theorem radius25_exact : poseRadius 1402 = radius25 := by
  unfold poseRadius; rw [angle25_exact]; rfl
private theorem cache25_exact : cache25.Exact plan25 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache25.inputs = cutRows 1402
    simp only [cutRows,lowerCut,upperCut,radius25_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache25.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache25.supports) (by decide +kernel)
  · change cache25.closing = upper (leftHi + (poseRadius 1402).radius) false
    rw [radius25_exact]
    decide +kernel
private theorem shape25 : plan25.Shape := by decide +kernel
private theorem numeric25 : cache25.Numeric plan25 := by
  decide +kernel
private theorem plan25_checked : plan25.Check :=
  cache25.toCheck plan25 cache25_exact shape25 numeric25

def plan26 : DirectPlan := ⟨1403, some 3104, [⟨25017, 0, 2⟩, ⟨25018, 0, 3⟩, ⟨25019, 0, 4⟩, ⟨25020, 1, 2⟩, ⟨25021, 0, 8⟩, ⟨25022, 0, 9⟩, ⟨25023, 0, 10⟩, ⟨25024, 2, 10⟩], 0, 0⟩
private def cache26 : PlanCache := ⟨[⟨25000000,0,-44985789,true⟩, ⟨-100000000,0,232074981,true⟩, ⟨155604850000000,155524650000000,-561917610243313,false⟩, ⟨0,50000000,-76242857,false⟩, ⟨-515662900000000,1214381200000000,-775510621727571,false⟩, ⟨-73801400000000,73839475000000,51746630302041,false⟩, ⟨-25000000,0,58988149,false⟩, ⟨-10887350000000,-10881700000000,43725536446699,false⟩, ⟨-50993750000000,-57238037500000,215207481906121,false⟩, ⟨0,-25000000,44551869,false⟩, ⟨243717087500000,-243842825000000,-106500019189771,false⟩, ⟨50000000,0,-101245103,false⟩, ⟨50000000,0,-101245103,false⟩, ⟨-25000000,0,58988149,false⟩, ⟨0,50000000,-76242857,false⟩, ⟨0,-25000000,44551869,false⟩, ⟨0,0,1,true⟩], [(⟨25017, 0, 2⟩,⟨155604850000000,155524650000000,-561916987984313,false⟩), (⟨25018, 0, 3⟩,⟨0,50000000,-76242757,false⟩), (⟨25019, 0, 4⟩,⟨-992084100000000,2336348800000000,-1491998947503119,false⟩), (⟨25020, 1, 2⟩,⟨-100000000,0,232075081,false⟩), (⟨25021, 0, 8⟩,⟨-179554180000000,-201540960000000,757768208773369,false⟩), (⟨25022, 0, 9⟩,⟨0,-25000000,44551919,false⟩), (⟨25023, 0, 10⟩,⟨121858543750000,-121921412500000,-53249522034973,false⟩), (⟨25024, 2, 10⟩,⟨50000000,0,-101245003,false⟩)], ⟨-25000000,0,44985789,false⟩⟩
private theorem angle26_exact : poseAngle 1403 = 26 := by
  decide +kernel
private theorem radius26_exact : poseRadius 1403 = radius26 := by
  unfold poseRadius; rw [angle26_exact]; rfl
private theorem cache26_exact : cache26.Exact plan26 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache26.inputs = cutRows 1403
    simp only [cutRows,lowerCut,upperCut,radius26_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache26.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache26.supports) (by decide +kernel)
  · change cache26.closing = upper (leftHi + (poseRadius 1403).radius) false
    rw [radius26_exact]
    decide +kernel
private theorem shape26 : plan26.Shape := by decide +kernel
private theorem numeric26 : cache26.Numeric plan26 := by
  decide +kernel
private theorem plan26_checked : plan26.Check :=
  cache26.toCheck plan26 cache26_exact shape26 numeric26

def plan27 : DirectPlan := ⟨1404, some 3106, [⟨25026, 0, 2⟩, ⟨25027, 0, 3⟩, ⟨25028, 0, 4⟩, ⟨25029, 0, 5⟩, ⟨25030, 1, 2⟩, ⟨25031, 0, 7⟩, ⟨25032, 0, 8⟩, ⟨25033, 0, 9⟩, ⟨25034, 2, 9⟩], 0, 0⟩
private def cache27 : PlanCache := ⟨[⟨100000000,0,-179954193,true⟩, ⟨-12500000,0,29007993,true⟩, ⟨47372430000000,49929170000000,-174346910586493,false⟩, ⟨0,50000000,-76130791,false⟩, ⟨-262938550000000,599474175000000,-367025563972317,false⟩, ⟨-49197537500000,46678262500000,37926766308987,false⟩, ⟨-100000000,0,235268681,false⟩, ⟨-73297400000000,-77253337500000,301238826684691,false⟩, ⟨0,-12500000,22305339,false⟩, ⟨48735650000000,-46240025000000,-26123681745271,false⟩, ⟨20000000,0,-40512467,false⟩, ⟨20000000,0,-40512467,false⟩, ⟨-100000000,0,235268681,false⟩, ⟨0,50000000,-76130791,false⟩, ⟨0,-12500000,22305339,false⟩, ⟨0,0,1,true⟩], [(⟨25026, 0, 2⟩,⟨47372430000000,49929170000000,-174346715983293,false⟩), (⟨25027, 0, 3⟩,⟨0,50000000,-76130691,false⟩), (⟨25028, 0, 4⟩,⟨-262938550000000,599474175000000,-367023839146867,false⟩), (⟨25029, 0, 5⟩,⟨-13949925000000,13235600000000,10754138574091,false⟩), (⟨25030, 1, 2⟩,⟨-25000000,0,58016011,false⟩), (⟨25031, 0, 7⟩,⟨-86868580000000,-91556970000000,357014239147339,false⟩), (⟨25032, 0, 8⟩,⟨0,-3125000,5576341,false⟩), (⟨25033, 0, 9⟩,⟨48735650000000,-46240025000000,-26123491793921,false⟩), (⟨25034, 2, 9⟩,⟨20000000,0,-40512427,false⟩)], ⟨-100000000,0,179954193,false⟩⟩
private theorem angle27_exact : poseAngle 1404 = 27 := by
  decide +kernel
private theorem radius27_exact : poseRadius 1404 = radius27 := by
  unfold poseRadius; rw [angle27_exact]; rfl
private theorem cache27_exact : cache27.Exact plan27 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache27.inputs = cutRows 1404
    simp only [cutRows,lowerCut,upperCut,radius27_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache27.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache27.supports) (by decide +kernel)
  · change cache27.closing = upper (leftHi + (poseRadius 1404).radius) false
    rw [radius27_exact]
    decide +kernel
private theorem shape27 : plan27.Shape := by decide +kernel
private theorem numeric27 : cache27.Numeric plan27 := by
  decide +kernel
private theorem plan27_checked : plan27.Check :=
  cache27.toCheck plan27 cache27_exact shape27 numeric27

def plan28 : DirectPlan := ⟨1405, some 3108, [⟨25036, 0, 2⟩, ⟨25037, 0, 3⟩, ⟨25038, 0, 4⟩, ⟨25039, 0, 5⟩, ⟨25040, 1, 2⟩, ⟨25041, 0, 7⟩, ⟨25042, 0, 8⟩, ⟨25043, 0, 9⟩, ⟨25044, 0, 10⟩, ⟨25045, 0, 11⟩, ⟨25046, 2, 11⟩], 0, 0⟩
private def cache28 : PlanCache := ⟨[⟨10000000,0,-18004359,true⟩, ⟨-100000000,0,231974547,true⟩, ⟨28573793750000,31743337500000,-107241819395287,false⟩, ⟨0,20000000,-30405699,false⟩, ⟨-214352500000000,472949560000000,-276544664780947,false⟩, ⟨-21517020000000,19368560000000,17982788315927,false⟩, ⟨-100000000,0,233944457,false⟩, ⟨-233148400000000,-120689100000000,747048568039163,false⟩, ⟨-231833000000000,-257549100000000,979009005180013,false⟩, ⟨0,-100000000,178667683,false⟩, ⟨1054218000000000,-1078759100000000,-431988174140527,false⟩, ⟨98282000000000,-88468700000000,-59342610614679,false⟩, ⟨25000000,0,-50336033,false⟩, ⟨25000000,0,-50336033,false⟩, ⟨-100000000,0,233944457,false⟩, ⟨0,20000000,-30405699,false⟩, ⟨0,-100000000,178667683,false⟩, ⟨0,0,1,true⟩], [(⟨25036, 0, 2⟩,⟨57147587500000,63486675000000,-214483397522049,false⟩), (⟨25037, 0, 3⟩,⟨0,20000000,-30405659,false⟩), (⟨25038, 0, 4⟩,⟨-214352500000000,472949560000000,-276543290176827,false⟩), (⟨25039, 0, 5⟩,⟨-21148700000000,19037020000000,17675040605631,false⟩), (⟨25040, 1, 2⟩,⟨-100000000,0,231974647,false⟩), (⟨25041, 0, 7⟩,⟨-4082300000000,-2113200000000,13080421765001,false⟩), (⟨25042, 0, 8⟩,⟨-231833000000000,-257549100000000,979009983944213,false⟩), (⟨25043, 0, 9⟩,⟨0,-100000000,178667883,false⟩), (⟨25044, 0, 10⟩,⟨1054218000000000,-1078759100000000,-431983908186327,false⟩), (⟨25045, 0, 11⟩,⟨98282000000000,-88468700000000,-59342237113279,false⟩), (⟨25046, 2, 11⟩,⟨25000000,0,-50335983,false⟩)], ⟨-10000000,0,18004359,false⟩⟩
private theorem angle28_exact : poseAngle 1405 = 28 := by
  decide +kernel
private theorem radius28_exact : poseRadius 1405 = radius28 := by
  unfold poseRadius; rw [angle28_exact]; rfl
private theorem cache28_exact : cache28.Exact plan28 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache28.inputs = cutRows 1405
    simp only [cutRows,lowerCut,upperCut,radius28_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache28.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache28.supports) (by decide +kernel)
  · change cache28.closing = upper (leftHi + (poseRadius 1405).radius) false
    rw [radius28_exact]
    decide +kernel
private theorem shape28 : plan28.Shape := by decide +kernel
private theorem numeric28 : cache28.Numeric plan28 := by
  decide +kernel
private theorem plan28_checked : plan28.Check :=
  cache28.toCheck plan28 cache28_exact shape28 numeric28

def plan29 : DirectPlan := ⟨1406, some 3110, [⟨25048, 0, 2⟩, ⟨25049, 0, 3⟩, ⟨25050, 0, 4⟩, ⟨25051, 0, 5⟩, ⟨25052, 1, 2⟩, ⟨25053, 0, 8⟩, ⟨25054, 0, 9⟩, ⟨25055, 0, 10⟩, ⟨25056, 0, 11⟩, ⟨25057, 2, 11⟩], 0, 0⟩
private def cache29 : PlanCache := ⟨[⟨25000000,0,-45054997,true⟩, ⟨-100000000,0,231798149,true⟩, ⟨46754800000000,54730250000000,-179067644143339,false⟩, ⟨0,50000000,-75893683,false⟩, ⟨-544902350000000,1165497550000000,-650317417225379,false⟩, ⟨-85126460000000,72721600000000,76312010252701,false⟩, ⟨-95037900000000,16858700000000,192590815341073,false⟩, ⟨-10000000,0,23310293,false⟩, ⟨-23982670000000,-28073650000000,104105031929499,false⟩, ⟨0,-100000000,178888633,false⟩, ⟨2061697000000000,-2140140100000000,-803766521584147,false⟩, ⟨137185600000000,-117194500000000,-93384151371913,false⟩, ⟨100000000,0,-200935343,false⟩, ⟨100000000,0,-200935343,false⟩, ⟨-10000000,0,23310293,false⟩, ⟨0,50000000,-75893683,false⟩, ⟨0,-100000000,178888633,false⟩, ⟨0,0,1,true⟩], [(⟨25048, 0, 2⟩,⟨46754800000000,54730250000000,-179067441173239,false⟩), (⟨25049, 0, 3⟩,⟨0,50000000,-75893583,false⟩), (⟨25050, 0, 4⟩,⟨-544902350000000,1165497550000000,-650313996425579,false⟩), (⟨25051, 0, 5⟩,⟨-23222362500000,19838337500000,20817879130183,false⟩), (⟨25052, 1, 2⟩,⟨-100000000,0,231798249,false⟩), (⟨25053, 0, 8⟩,⟨-608007100000000,-711721400000000,2639266751824747,false⟩), (⟨25054, 0, 9⟩,⟨0,-100000000,178888833,false⟩), (⟨25055, 0, 10⟩,⟨2061697000000000,-2140140100000000,-803758117909947,false⟩), (⟨25056, 0, 11⟩,⟨137185600000000,-117194500000000,-93383642611713,false⟩), (⟨25057, 2, 11⟩,⟨100000000,0,-200935143,false⟩)], ⟨-25000000,0,45054997,false⟩⟩
private theorem angle29_exact : poseAngle 1406 = 29 := by
  decide +kernel
private theorem radius29_exact : poseRadius 1406 = radius29 := by
  unfold poseRadius; rw [angle29_exact]; rfl
private theorem cache29_exact : cache29.Exact plan29 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache29.inputs = cutRows 1406
    simp only [cutRows,lowerCut,upperCut,radius29_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache29.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache29.supports) (by decide +kernel)
  · change cache29.closing = upper (leftHi + (poseRadius 1406).radius) false
    rw [radius29_exact]
    decide +kernel
private theorem shape29 : plan29.Shape := by decide +kernel
private theorem numeric29 : cache29.Numeric plan29 := by
  decide +kernel
private theorem plan29_checked : plan29.Check :=
  cache29.toCheck plan29 cache29_exact shape29 numeric29

def plan30 : DirectPlan := ⟨1407, some 3112, [⟨25059, 0, 2⟩, ⟨25060, 0, 3⟩, ⟨25061, 0, 4⟩, ⟨25062, 0, 5⟩, ⟨25063, 0, 6⟩, ⟨25064, 1, 2⟩, ⟨25065, 0, 8⟩, ⟨25066, 0, 9⟩, ⟨25067, 0, 10⟩, ⟨25068, 0, 11⟩, ⟨25069, 2, 11⟩], 0, 0⟩
private def cache30 : PlanCache := ⟨[⟨100000000,0,-180479651,true⟩, ⟨-50000000,0,115769243,true⟩, ⟨291426400000000,359386900000000,-1139781200769063,false⟩, ⟨0,100000000,-151539003,false⟩, ⟨-221178340000000,459353300000000,-244394230406487,false⟩, ⟨-3317492000000,2690152000000,3163023022989,false⟩, ⟨-100109440000000,81048020000000,95666009923347,false⟩, ⟨-25000000,0,58652359,false⟩, ⟨-183869450000000,-226747650000000,820815207000539,false⟩, ⟨0,-25000000,44776309,false⟩, ⟨503671600000000,-531342425000000,-184315442739191,false⟩, ⟨56311300000000,-45662775000000,-42451091342393,false⟩, ⟨10000000,0,-20063261,false⟩, ⟨10000000,0,-20063261,false⟩, ⟨-25000000,0,58652359,false⟩, ⟨0,100000000,-151539003,false⟩, ⟨0,-25000000,44776309,false⟩, ⟨0,0,1,true⟩], [(⟨25059, 0, 2⟩,⟨291426400000000,359386900000000,-1139779899142463,false⟩), (⟨25060, 0, 3⟩,⟨0,100000000,-151538803,false⟩), (⟨25061, 0, 4⟩,⟨-221178340000000,459353300000000,-244392869343207,false⟩), (⟨25062, 0, 5⟩,⟨-3317492000000,2690152000000,3163035038277,false⟩), (⟨25063, 0, 6⟩,⟨-2424302000000,1962702000000,2316704354563,false⟩), (⟨25064, 1, 2⟩,⟨-50000000,0,115769293,false⟩), (⟨25065, 0, 8⟩,⟨-121611650000000,-149971400000000,542889516903849,false⟩), (⟨25066, 0, 9⟩,⟨0,-25000000,44776359,false⟩), (⟨25067, 0, 10⟩,⟨503671600000000,-531342425000000,-184313372711141,false⟩), (⟨25068, 0, 11⟩,⟨56311300000000,-45662775000000,-42450887394243,false⟩), (⟨25069, 2, 11⟩,⟨10000000,0,-20063241,false⟩)], ⟨-100000000,0,180479651,false⟩⟩
private theorem angle30_exact : poseAngle 1407 = 30 := by
  decide +kernel
private theorem radius30_exact : poseRadius 1407 = radius30 := by
  unfold poseRadius; rw [angle30_exact]; rfl
private theorem cache30_exact : cache30.Exact plan30 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache30.inputs = cutRows 1407
    simp only [cutRows,lowerCut,upperCut,radius30_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache30.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache30.supports) (by decide +kernel)
  · change cache30.closing = upper (leftHi + (poseRadius 1407).radius) false
    rw [radius30_exact]
    decide +kernel
private theorem shape30 : plan30.Shape := by decide +kernel
private theorem numeric30 : cache30.Numeric plan30 := by
  decide +kernel
private theorem plan30_checked : plan30.Check :=
  cache30.toCheck plan30 cache30_exact shape30 numeric30

def plan31 : DirectPlan := ⟨1408, some 3114, [⟨25071, 0, 2⟩, ⟨25072, 0, 3⟩, ⟨25073, 0, 4⟩, ⟨25074, 0, 5⟩, ⟨25075, 1, 2⟩, ⟨25076, 0, 8⟩, ⟨25077, 0, 9⟩, ⟨25078, 0, 10⟩, ⟨25079, 0, 11⟩, ⟨25080, 2, 11⟩], 0, 0⟩
private def cache31 : PlanCache := ⟨[⟨25000000,0,-45204643,true⟩, ⟨-20000000,0,46239913,true⟩, ⟨52490225000000,68188700000000,-209798001345867,false⟩, ⟨0,50000000,-75642059,false⟩, ⟨-224008500000000,452437100000000,-229368559912433,false⟩, ⟨-617022700000000,598442100000000,420752823342921,false⟩, ⟨-204606400000000,157501750000000,208575559186837,false⟩, ⟨-25000000,0,58729217,false⟩, ⟨-328509400000000,-426757900000000,1508935885568913,false⟩, ⟨0,-100000000,179317287,false⟩, ⟨245945000000000,-264145100000000,-83116175246613,false⟩, ⟨4888874218750,-3763353906250,-4026527830281,false⟩, ⟨12500000,0,-25054101,false⟩, ⟨12500000,0,-25054101,false⟩, ⟨-25000000,0,58729217,false⟩, ⟨0,50000000,-75642059,false⟩, ⟨0,-100000000,179317287,false⟩, ⟨0,0,1,true⟩], [(⟨25071, 0, 2⟩,⟨52490225000000,68188700000000,-209797759988017,false⟩), (⟨25072, 0, 3⟩,⟨0,50000000,-75641959,false⟩), (⟨25073, 0, 4⟩,⟨-224008500000000,452437100000000,-229367207021233,false⟩), (⟨25074, 0, 5⟩,⟨-558524300000000,541705300000000,380864455493537,false⟩), (⟨25075, 1, 2⟩,⟨-20000000,0,46239933,false⟩), (⟨25076, 0, 8⟩,⟨-74172160000000,-96355100000000,340693896412593,false⟩), (⟨25077, 0, 9⟩,⟨0,-100000000,179317487,false⟩), (⟨25078, 0, 10⟩,⟨245945000000000,-264145100000000,-83115155066413,false⟩), (⟨25079, 0, 11⟩,⟨19555496875000,-15053415625000,-16106042103299,false⟩), (⟨25080, 2, 11⟩,⟨3125000,0,-6263519,false⟩)], ⟨-25000000,0,45204643,false⟩⟩
private theorem angle31_exact : poseAngle 1408 = 31 := by
  decide +kernel
private theorem radius31_exact : poseRadius 1408 = radius31 := by
  unfold poseRadius; rw [angle31_exact]; rfl
private theorem cache31_exact : cache31.Exact plan31 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache31.inputs = cutRows 1408
    simp only [cutRows,lowerCut,upperCut,radius31_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache31.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache31.supports) (by decide +kernel)
  · change cache31.closing = upper (leftHi + (poseRadius 1408).radius) false
    rw [radius31_exact]
    decide +kernel
private theorem shape31 : plan31.Shape := by decide +kernel
private theorem numeric31 : cache31.Numeric plan31 := by
  decide +kernel
private theorem plan31_checked : plan31.Check :=
  cache31.toCheck plan31 cache31_exact shape31 numeric31

def plan32 : DirectPlan := ⟨1409, some 3116, [⟨25082, 0, 2⟩, ⟨25083, 0, 3⟩, ⟨25084, 0, 4⟩, ⟨25085, 0, 5⟩, ⟨25086, 0, 6⟩, ⟨25087, 1, 2⟩, ⟨25088, 0, 8⟩, ⟨25089, 0, 9⟩, ⟨25090, 0, 10⟩, ⟨25091, 0, 11⟩, ⟨25092, 2, 11⟩], 0, 0⟩
private def cache32 : PlanCache := ⟨[⟨50000000,0,-90616259,true⟩, ⟨-100000000,0,230785619,true⟩, ⟨260441000000,356422400000,-1064670165959,false⟩, ⟨0,20000000,-30204667,false⟩, ⟨-113228400000000,222737020000000,-107533570368629,false⟩, ⟨-598875800000000,580418300000000,401521269893897,false⟩, ⟨-58732490000000,42916360000000,62954644591347,false⟩, ⟨-50000000,0,117242139,false⟩, ⟨-6110700000000,-8362700000000,28897155220887,false⟩, ⟨0,-25000000,44881173,false⟩, ⟨48011645000000,-52586455000000,-14680880500617,false⟩, ⟨79942930000000,-58415020000000,-71170513403911,false⟩, ⟨25000000,0,-50083111,false⟩, ⟨25000000,0,-50083111,false⟩, ⟨-50000000,0,117242139,false⟩, ⟨0,20000000,-30204667,false⟩, ⟨0,-25000000,44881173,false⟩, ⟨0,0,1,true⟩], [(⟨25082, 0, 2⟩,⟨1302205000000,1782112000000,-5323344661161,false⟩), (⟨25083, 0, 3⟩,⟨0,20000000,-30204627,false⟩), (⟨25084, 0, 4⟩,⟨-113228400000000,222737020000000,-107532898437789,false⟩), (⟨25085, 0, 5⟩,⟨-598875800000000,580418300000000,401523628482097,false⟩), (⟨25086, 0, 6⟩,⟨-81137200000000,59287700000000,86970235102383,false⟩), (⟨25087, 1, 2⟩,⟨-100000000,0,230785719,false⟩), (⟨25088, 0, 8⟩,⟨-4083737500000,-5588734375000,19311785587807,false⟩), (⟨25089, 0, 9⟩,⟨0,-25000000,44881223,false⟩), (⟨25090, 0, 10⟩,⟨48011645000000,-52586455000000,-14680679304417,false⟩), (⟨25091, 0, 11⟩,⟨79942930000000,-58415020000000,-71170236688011,false⟩), (⟨25092, 2, 11⟩,⟨25000000,0,-50083061,false⟩)], ⟨-50000000,0,90616259,false⟩⟩
private theorem angle32_exact : poseAngle 1409 = 32 := by
  decide +kernel
private theorem radius32_exact : poseRadius 1409 = radius32 := by
  unfold poseRadius; rw [angle32_exact]; rfl
private theorem cache32_exact : cache32.Exact plan32 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache32.inputs = cutRows 1409
    simp only [cutRows,lowerCut,upperCut,radius32_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache32.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache32.supports) (by decide +kernel)
  · change cache32.closing = upper (leftHi + (poseRadius 1409).radius) false
    rw [radius32_exact]
    decide +kernel
private theorem shape32 : plan32.Shape := by decide +kernel
private theorem numeric32 : cache32.Numeric plan32 := by
  decide +kernel
private theorem plan32_checked : plan32.Check :=
  cache32.toCheck plan32 cache32_exact shape32 numeric32

def plan33 : DirectPlan := ⟨1410, some 3118, [⟨25094, 0, 2⟩, ⟨25095, 0, 3⟩, ⟨25096, 0, 4⟩, ⟨25097, 0, 5⟩, ⟨25098, 0, 6⟩, ⟨25099, 1, 2⟩, ⟨25100, 0, 8⟩, ⟨25101, 0, 9⟩, ⟨25102, 0, 10⟩, ⟨25103, 0, 11⟩, ⟨25104, 2, 11⟩], 0, 0⟩
private def cache33 : PlanCache := ⟨[⟨100000000,0,-181717077,true⟩, ⟨-5000000,0,11515053,true⟩, ⟨52745100000000,76055900000000,-220723947640177,false⟩, ⟨0,25000000,-37689299,false⟩, ⟨-285662375000000,548108325000000,-251878659699147,false⟩, ⟨-144149475000000,142143625000000,90937998512117,false⟩, ⟨-381792600000000,264775150000000,428465118996887,false⟩, ⟨-20000000,0,46798809,false⟩, ⟨-414173600000000,-597217700000000,2017770576391091,false⟩, ⟨0,-100000000,179727459,false⟩, ⟨78064312500000,-87341612500000,-21026685898713,false⟩, ⟨15167462500000,-10518712500000,-14471411164129,false⟩, ⟨12500000,0,-25040963,false⟩, ⟨12500000,0,-25040963,false⟩, ⟨-20000000,0,46798809,false⟩, ⟨0,25000000,-37689299,false⟩, ⟨0,-100000000,179727459,false⟩, ⟨0,0,1,true⟩], [(⟨25094, 0, 2⟩,⟨52745100000000,76055900000000,-220723690038177,false⟩), (⟨25095, 0, 3⟩,⟨0,25000000,-37689249,false⟩), (⟨25096, 0, 4⟩,⟨-285662375000000,548108325000000,-251876992157747,false⟩), (⟨25097, 0, 5⟩,⟨-144149475000000,142143625000000,90938571098317,false⟩), (⟨25098, 0, 6⟩,⟨-115530350000000,80120900000000,129653830168967,false⟩), (⟨25099, 1, 2⟩,⟨-2500000,0,5757529,false⟩), (⟨25100, 0, 8⟩,⟨-39514050000000,-56977300000000,192504721411961,false⟩), (⟨25101, 0, 9⟩,⟨0,-100000000,179727659,false⟩), (⟨25102, 0, 10⟩,⟨78064312500000,-87341612500000,-21026355086863,false⟩), (⟨25103, 0, 11⟩,⟨15167462500000,-10518712500000,-14471359791779,false⟩), (⟨25104, 2, 11⟩,⟨6250000,0,-12520469,false⟩)], ⟨-100000000,0,181717077,false⟩⟩
private theorem angle33_exact : poseAngle 1410 = 33 := by
  decide +kernel
private theorem radius33_exact : poseRadius 1410 = radius33 := by
  unfold poseRadius; rw [angle33_exact]; rfl
private theorem cache33_exact : cache33.Exact plan33 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache33.inputs = cutRows 1410
    simp only [cutRows,lowerCut,upperCut,radius33_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache33.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache33.supports) (by decide +kernel)
  · change cache33.closing = upper (leftHi + (poseRadius 1410).radius) false
    rw [radius33_exact]
    decide +kernel
private theorem shape33 : plan33.Shape := by decide +kernel
private theorem numeric33 : cache33.Numeric plan33 := by
  decide +kernel
private theorem plan33_checked : plan33.Check :=
  cache33.toCheck plan33 cache33_exact shape33 numeric33

def plan34 : DirectPlan := ⟨1411, some 3120, [⟨25106, 0, 2⟩, ⟨25107, 0, 3⟩, ⟨25108, 0, 4⟩, ⟨25109, 0, 5⟩, ⟨25110, 1, 2⟩, ⟨25111, 0, 7⟩, ⟨25112, 0, 8⟩, ⟨25113, 0, 9⟩, ⟨25114, 2, 9⟩], 0, 0⟩
private def cache34 : PlanCache := ⟨[⟨20000000,0,-36453541,true⟩, ⟨-3125000,0,7179701,true⟩, ⟨42518920000000,64617900000000,-198925204702849,false⟩, ⟨0,100000000,-161997957,false⟩, ⟨-550769400000000,562970900000000,308810445497451,false⟩, ⟨-937292400000000,616743100000000,1097249376450879,false⟩, ⟨-50000000,0,116726423,false⟩, ⟨-16927250000000,-25725100000000,85019388879311,false⟩, ⟨0,-100000000,179925681,false⟩, ⟨790078850000000,-519875850000000,-872485066080101,false⟩, ⟨10000000,0,-21842461,false⟩, ⟨10000000,0,-21842461,false⟩, ⟨-50000000,0,116726423,false⟩, ⟨0,100000000,-161997957,false⟩, ⟨0,-100000000,179925681,false⟩, ⟨0,0,1,true⟩], [(⟨25106, 0, 2⟩,⟨42518920000000,64617900000000,-198924990429209,false⟩), (⟨25107, 0, 3⟩,⟨0,100000000,-161997757,false⟩), (⟨25108, 0, 4⟩,⟨-550769400000000,562970900000000,308812672978051,false⟩), (⟨25109, 0, 5⟩,⟨-93651125000000,61622925000000,109633776970027,false⟩), (⟨25110, 1, 2⟩,⟨-25000000,0,57437633,false⟩), (⟨25111, 0, 7⟩,⟨-2180825000000,-3314300000000,10953502370239,false⟩), (⟨25112, 0, 8⟩,⟨0,-100000000,179925881,false⟩), (⟨25113, 0, 9⟩,⟨790078850000000,-519875850000000,-872482446170701,false⟩), (⟨25114, 2, 9⟩,⟨10000000,0,-21842441,false⟩)], ⟨-20000000,0,36453541,false⟩⟩
private theorem angle34_exact : poseAngle 1411 = 34 := by
  decide +kernel
private theorem radius34_exact : poseRadius 1411 = radius34 := by
  unfold poseRadius; rw [angle34_exact]; rfl
private theorem cache34_exact : cache34.Exact plan34 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache34.inputs = cutRows 1411
    simp only [cutRows,lowerCut,upperCut,radius34_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache34.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache34.supports) (by decide +kernel)
  · change cache34.closing = upper (leftHi + (poseRadius 1411).radius) false
    rw [radius34_exact]
    decide +kernel
private theorem shape34 : plan34.Shape := by decide +kernel
private theorem numeric34 : cache34.Numeric plan34 := by
  decide +kernel
private theorem plan34_checked : plan34.Check :=
  cache34.toCheck plan34 cache34_exact shape34 numeric34

def plan35 : DirectPlan := ⟨1412, some 3122, [⟨25116, 0, 2⟩, ⟨25117, 0, 3⟩, ⟨25118, 0, 4⟩, ⟨25119, 0, 5⟩, ⟨25120, 1, 2⟩, ⟨25121, 1, 9⟩, ⟨25122, 0, 9⟩, ⟨25123, 2, 9⟩], 0, 0⟩
private def cache35 : PlanCache := ⟨[⟨100000000,0,-182879767,true⟩, ⟨-10000000,0,22913837,true⟩, ⟨4817070000000,7718860000000,-23101165411803,false⟩, ⟨0,100000000,-161789823,false⟩, ⟨-521952400000000,563624500000000,238065069105353,false⟩, ⟨-3692697000000,2304482000000,4495084496671,false⟩, ⟨-12500000,0,29108391,false⟩, ⟨-20318910000000,-32558980000000,105299580922387,false⟩, ⟨0,-10000000,18011953,false⟩, ⟨868304600000000,-541878250000000,-1017694569842109,false⟩, ⟨12500000,0,-27346683,false⟩, ⟨12500000,0,-27346683,false⟩, ⟨-12500000,0,29108391,false⟩, ⟨0,100000000,-161789823,false⟩, ⟨0,-10000000,18011953,false⟩, ⟨0,0,1,true⟩], [(⟨25116, 0, 2⟩,⟨4817070000000,7718860000000,-23101140339943,false⟩), (⟨25117, 0, 3⟩,⟨0,100000000,-161789623,false⟩), (⟨25118, 0, 4⟩,⟨-521952400000000,563624500000000,238067240259153,false⟩), (⟨25119, 0, 5⟩,⟨-127574400000000,79614700000000,155295477881599,false⟩), (⟨25120, 1, 2⟩,⟨-10000000,0,22913847,false⟩), (⟨25121, 1, 9⟩,⟨0,-100000000,179362503,false⟩), (⟨25122, 0, 9⟩,⟨415221625000000,-259125150000000,-486658293248383,false⟩), (⟨25123, 2, 9⟩,⟨6250000,0,-13673329,false⟩)], ⟨-100000000,0,182879767,false⟩⟩
private theorem angle35_exact : poseAngle 1412 = 35 := by
  decide +kernel
private theorem radius35_exact : poseRadius 1412 = radius35 := by
  unfold poseRadius; rw [angle35_exact]; rfl
private theorem cache35_exact : cache35.Exact plan35 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache35.inputs = cutRows 1412
    simp only [cutRows,lowerCut,upperCut,radius35_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache35.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache35.supports) (by decide +kernel)
  · change cache35.closing = upper (leftHi + (poseRadius 1412).radius) false
    rw [radius35_exact]
    decide +kernel
private theorem shape35 : plan35.Shape := by decide +kernel
private theorem numeric35 : cache35.Numeric plan35 := by
  decide +kernel
private theorem plan35_checked : plan35.Check :=
  cache35.toCheck plan35 cache35_exact shape35 numeric35

def plan36 : DirectPlan := ⟨1413, some 3124, [⟨25125, 0, 2⟩, ⟨25126, 0, 3⟩, ⟨25127, 0, 4⟩, ⟨25128, 1, 2⟩, ⟨25129, 1, 8⟩, ⟨25130, 0, 8⟩, ⟨25131, 2, 8⟩], 0, 0⟩
private def cache36 : PlanCache := ⟨[⟨25000000,0,-45887143,true⟩, ⟨-20000000,0,45693913,true⟩, ⟨109642800000000,185346500000000,-554911584834393,false⟩, ⟨0,100000000,-166467009,false⟩, ⟨-424853600000000,251324700000000,536287505596409,false⟩, ⟨-50000000,0,116121539,false⟩, ⟨-13705350000000,-23168300000000,73350290003367,false⟩, ⟨0,-50000000,90154623,false⟩, ⟨318640200000000,-188493550000000,-394241987598393,false⟩, ⟨100000000,0,-222849671,false⟩, ⟨100000000,0,-222849671,false⟩, ⟨-50000000,0,116121539,false⟩, ⟨0,100000000,-166467009,false⟩, ⟨0,-50000000,90154623,false⟩, ⟨0,0,1,true⟩], [(⟨25125, 0, 2⟩,⟨109642800000000,185346500000000,-554910994855793,false⟩), (⟨25126, 0, 3⟩,⟨0,100000000,-166466809,false⟩), (⟨25127, 0, 4⟩,⟨-212215900000000,125537600000000,267878196561199,false⟩), (⟨25128, 1, 2⟩,⟨-20000000,0,45693933,false⟩), (⟨25129, 1, 8⟩,⟨0,-20000000,35412839,false⟩), (⟨25130, 0, 8⟩,⟨38001428000000,-22479976000000,-47017670703367,false⟩), (⟨25131, 2, 8⟩,⟨100000000,0,-222849471,false⟩)], ⟨-25000000,0,45887143,false⟩⟩
private theorem angle36_exact : poseAngle 1413 = 36 := by
  decide +kernel
private theorem radius36_exact : poseRadius 1413 = radius36 := by
  unfold poseRadius; rw [angle36_exact]; rfl
private theorem cache36_exact : cache36.Exact plan36 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache36.inputs = cutRows 1413
    simp only [cutRows,lowerCut,upperCut,radius36_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache36.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache36.supports) (by decide +kernel)
  · change cache36.closing = upper (leftHi + (poseRadius 1413).radius) false
    rw [radius36_exact]
    decide +kernel
private theorem shape36 : plan36.Shape := by decide +kernel
private theorem numeric36 : cache36.Numeric plan36 := by
  decide +kernel
private theorem plan36_checked : plan36.Check :=
  cache36.toCheck plan36 cache36_exact shape36 numeric36

def plan37 : DirectPlan := ⟨1414, some 3126, [⟨25133, 0, 2⟩, ⟨25134, 0, 3⟩, ⟨25135, 0, 4⟩, ⟨25136, 1, 2⟩, ⟨25137, 1, 8⟩, ⟨25138, 0, 8⟩, ⟨25139, 2, 8⟩], 0, 0⟩
private def cache37 : PlanCache := ⟨[⟨100000000,0,-184269413,true⟩, ⟨-25000000,0,56937181,true⟩, ⟨2999212500000,5352237500000,-15582793063817,false⟩, ⟨0,100000000,-165884641,false⟩, ⟨-718517150000000,402631600000000,938226012535357,false⟩, ⟨-50000000,0,115793307,false⟩, ⟨-11996850000000,-21409000000000,66373931258309,false⟩, ⟨0,-50000000,90247561,false⟩, ⟨1437034300000000,-805263100000000,-1868362480717937,false⟩, ⟨50000000,0,-111552801,false⟩, ⟨50000000,0,-111552801,false⟩, ⟨-50000000,0,115793307,false⟩, ⟨0,100000000,-165884641,false⟩, ⟨0,-50000000,90247561,false⟩, ⟨0,0,1,true⟩], [(⟨25133, 0, 2⟩,⟨2999212500000,5352237500000,-15582776360917,false⟩), (⟨25134, 0, 3⟩,⟨0,100000000,-165884441,false⟩), (⟨25135, 0, 4⟩,⟨-188031225000000,105366050000000,245528177662049,false⟩), (⟨25136, 1, 2⟩,⟨-12500000,0,28468603,false⟩), (⟨25137, 1, 8⟩,⟨0,-100000000,174411053,false⟩), (⟨25138, 0, 8⟩,⟨82860740000000,-46432220000000,-107731271352941,false⟩), (⟨25139, 2, 8⟩,⟨50000000,0,-111552701,false⟩)], ⟨-100000000,0,184269413,false⟩⟩
private theorem angle37_exact : poseAngle 1414 = 37 := by
  decide +kernel
private theorem radius37_exact : poseRadius 1414 = radius37 := by
  unfold poseRadius; rw [angle37_exact]; rfl
private theorem cache37_exact : cache37.Exact plan37 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache37.inputs = cutRows 1414
    simp only [cutRows,lowerCut,upperCut,radius37_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache37.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache37.supports) (by decide +kernel)
  · change cache37.closing = upper (leftHi + (poseRadius 1414).radius) false
    rw [radius37_exact]
    decide +kernel
private theorem shape37 : plan37.Shape := by decide +kernel
private theorem numeric37 : cache37.Numeric plan37 := by
  decide +kernel
private theorem plan37_checked : plan37.Check :=
  cache37.toCheck plan37 cache37_exact shape37 numeric37

def plan38 : DirectPlan := ⟨1415, some 3128, [⟨25141, 0, 2⟩, ⟨25142, 0, 3⟩, ⟨25143, 0, 4⟩, ⟨25144, 2, 5⟩, ⟨25145, 0, 6⟩, ⟨25146, 0, 7⟩, ⟨25147, 0, 8⟩, ⟨25148, 2, 8⟩], 0, 0⟩
private def cache38 : PlanCache := ⟨[⟨50000000,0,-92518799,true⟩, ⟨-100000000,0,226980539,true⟩, ⟨73730600000000,139012725000000,-383431032579843,false⟩, ⟨0,25000000,-40259831,false⟩, ⟨-962250000000,510362500000,1260594469063,false⟩, ⟨-25000000,0,54135033,false⟩, ⟨-19661500000000,-37070060000000,102358096190959,false⟩, ⟨0,-10000000,16421969,false⟩, ⟨721690625000,-382771875000,-894031922721,false⟩, ⟨20000000,0,-42171387,false⟩, ⟨20000000,0,-42171387,false⟩, ⟨-25000000,0,54135033,false⟩, ⟨0,25000000,-40259831,false⟩, ⟨0,-10000000,16421969,false⟩, ⟨0,0,1,true⟩], [(⟨25141, 0, 2⟩,⟨73730600000000,139012725000000,-383430607093193,false⟩), (⟨25142, 0, 3⟩,⟨0,25000000,-40259781,false⟩), (⟨25143, 0, 4⟩,⟨-60140625000,31897656250,78787338393,false⟩), (⟨25144, 2, 5⟩,⟨-25000000,0,54135083,false⟩), (⟨25145, 0, 6⟩,⟨-19661500000000,-37070060000000,102358209654079,false⟩), (⟨25146, 0, 7⟩,⟨0,-10000000,16421989,false⟩), (⟨25147, 0, 8⟩,⟨180422656250,-95692968750,-223507428449,false⟩), (⟨25148, 2, 8⟩,⟨20000000,0,-42171347,false⟩)], ⟨-50000000,0,92518799,false⟩⟩
private theorem angle38_exact : poseAngle 1415 = 38 := by
  decide +kernel
private theorem radius38_exact : poseRadius 1415 = radius38 := by
  unfold poseRadius; rw [angle38_exact]; rfl
private theorem cache38_exact : cache38.Exact plan38 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache38.inputs = cutRows 1415
    simp only [cutRows,lowerCut,upperCut,radius38_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache38.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache38.supports) (by decide +kernel)
  · change cache38.closing = upper (leftHi + (poseRadius 1415).radius) false
    rw [radius38_exact]
    decide +kernel
private theorem shape38 : plan38.Shape := by decide +kernel
private theorem numeric38 : cache38.Numeric plan38 := by
  decide +kernel
private theorem plan38_checked : plan38.Check :=
  cache38.toCheck plan38 cache38_exact shape38 numeric38

def plan39 : DirectPlan := ⟨1416, some 3130, [⟨25149, 0, 2⟩, ⟨25150, 0, 3⟩, ⟨25151, 0, 4⟩, ⟨25152, 2, 5⟩, ⟨25153, 0, 6⟩, ⟨25154, 0, 7⟩, ⟨25155, 0, 8⟩, ⟨25156, 2, 8⟩], 0, 0⟩
private def cache39 : PlanCache := ⟨[⟨625000,0,-1161553,true⟩, ⟨-100000000,0,226169657,true⟩, ⟨110806100000000,220934900000000,-593558900799423,false⟩, ⟨0,4000000,-6429993,false⟩, ⟨-186732200000000,93652300000000,251220779745843,false⟩, ⟨-50000000,0,108046571,false⟩, ⟨-55403050000000,-110467450000000,299361429102057,false⟩, ⟨0,-10000000,16483347,false⟩, ⟨46683050000000,-23413075000000,-60223408740609,false⟩, ⟨2500000,0,-5268443,false⟩, ⟨2500000,0,-5268443,false⟩, ⟨-50000000,0,108046571,false⟩, ⟨0,4000000,-6429993,false⟩, ⟨0,-10000000,16483347,false⟩, ⟨0,0,1,true⟩], [(⟨25149, 0, 2⟩,⟨110806100000000,220934900000000,-593558237317423,false⟩), (⟨25150, 0, 3⟩,⟨0,800000,-1285997,false⟩), (⟨25151, 0, 4⟩,⟨-186732200000000,93652300000000,251221340514843,false⟩), (⟨25152, 2, 5⟩,⟨-50000000,0,108046671,false⟩), (⟨25153, 0, 6⟩,⟨-55403050000000,-110467450000000,299361760843057,false⟩), (⟨25154, 0, 7⟩,⟨0,-10000000,16483367,false⟩), (⟨25155, 0, 8⟩,⟨46683050000000,-23413075000000,-60223268548359,false⟩), (⟨25156, 2, 8⟩,⟨1250000,0,-2634219,false⟩)], ⟨-625000,0,1161553,false⟩⟩
private theorem angle39_exact : poseAngle 1416 = 39 := by
  decide +kernel
private theorem radius39_exact : poseRadius 1416 = radius39 := by
  unfold poseRadius; rw [angle39_exact]; rfl
private theorem cache39_exact : cache39.Exact plan39 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache39.inputs = cutRows 1416
    simp only [cutRows,lowerCut,upperCut,radius39_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache39.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache39.supports) (by decide +kernel)
  · change cache39.closing = upper (leftHi + (poseRadius 1416).radius) false
    rw [radius39_exact]
    decide +kernel
private theorem shape39 : plan39.Shape := by decide +kernel
private theorem numeric39 : cache39.Numeric plan39 := by
  decide +kernel
private theorem plan39_checked : plan39.Check :=
  cache39.toCheck plan39 cache39_exact shape39 numeric39

def plan40 : DirectPlan := ⟨1417, some 3132, [⟨25157, 0, 2⟩, ⟨25158, 0, 3⟩, ⟨25159, 0, 4⟩, ⟨25160, 2, 5⟩, ⟨25161, 0, 6⟩, ⟨25162, 0, 7⟩, ⟨25163, 0, 8⟩, ⟨25164, 2, 8⟩], 0, 0⟩
private def cache40 : PlanCache := ⟨[⟨25000000,0,-46674371,true⟩, ⟨-100000000,0,225320653,true⟩, ⟨152326400000000,321555500000000,-841759121970923,false⟩, ⟨0,100000000,-160441977,false⟩, ⟨-69401440000000,32876660000000,95712313096291,false⟩, ⟨-100000000,0,215559101,false⟩, ⟨-19040800000000,-40194450000000,106927804673333,false⟩, ⟨0,-50000000,82717757,false⟩, ⟨4337590000000,-2054790000000,-5811231256889,false⟩, ⟨12500000,0,-26337439,false⟩, ⟨12500000,0,-26337439,false⟩, ⟨-100000000,0,215559101,false⟩, ⟨0,100000000,-160441977,false⟩, ⟨0,-50000000,82717757,false⟩, ⟨0,0,1,true⟩], [(⟨25157, 0, 2⟩,⟨152326400000000,321555500000000,-841758174207123,false⟩), (⟨25158, 0, 3⟩,⟨0,100000000,-160441777,false⟩), (⟨25159, 0, 4⟩,⟨-69401440000000,32876660000000,95712517652491,false⟩), (⟨25160, 2, 5⟩,⟨-100000000,0,215559301,false⟩), (⟨25161, 0, 6⟩,⟨-19040800000000,-40194450000000,106927923143833,false⟩), (⟨25162, 0, 7⟩,⟨0,-50000000,82717857,false⟩), (⟨25163, 0, 8⟩,⟨4337590000000,-2054790000000,-5811218472129,false⟩), (⟨25164, 2, 8⟩,⟨6250000,0,-13168707,false⟩)], ⟨-25000000,0,46674371,false⟩⟩
private theorem angle40_exact : poseAngle 1417 = 40 := by
  decide +kernel
private theorem radius40_exact : poseRadius 1417 = radius40 := by
  unfold poseRadius; rw [angle40_exact]; rfl
private theorem cache40_exact : cache40.Exact plan40 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache40.inputs = cutRows 1417
    simp only [cutRows,lowerCut,upperCut,radius40_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache40.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache40.supports) (by decide +kernel)
  · change cache40.closing = upper (leftHi + (poseRadius 1417).radius) false
    rw [radius40_exact]
    decide +kernel
private theorem shape40 : plan40.Shape := by decide +kernel
private theorem numeric40 : cache40.Numeric plan40 := by
  decide +kernel
private theorem plan40_checked : plan40.Check :=
  cache40.toCheck plan40 cache40_exact shape40 numeric40

def plan41 : DirectPlan := ⟨1418, some 3134, [⟨25165, 0, 2⟩, ⟨25166, 0, 3⟩, ⟨25167, 0, 4⟩, ⟨25168, 2, 5⟩, ⟨25169, 0, 6⟩, ⟨25170, 0, 7⟩, ⟨25171, 0, 8⟩, ⟨25172, 2, 8⟩], 0, 0⟩
private def cache41 : PlanCache := ⟨[⟨10000000,0,-18758013,true⟩, ⟨-100000000,0,224438007,true⟩, ⟨8737050000000,19551850000000,-49888883966331,false⟩, ⟨0,100000000,-160116549,false⟩, ⟨-251754850000000,112500600000000,355334601894671,false⟩, ⟨-50000000,0,107471851,false⟩, ⟨-21842625000000,-48879650000000,127674991571113,false⟩, ⟨0,-6250000,10376597,false⟩, ⟨503509700000000,-225001100000000,-698857507610483,false⟩, ⟨781250,0,-1646393,false⟩, ⟨781250,0,-1646393,false⟩, ⟨-50000000,0,107471851,false⟩, ⟨0,100000000,-160116549,false⟩, ⟨0,-6250000,10376597,false⟩, ⟨0,0,1,true⟩], [(⟨25165, 0, 2⟩,⟨8737050000000,19551850000000,-49888827388531,false⟩), (⟨25166, 0, 3⟩,⟨0,100000000,-160116349,false⟩), (⟨25167, 0, 4⟩,⟨-251754850000000,112500600000000,355335330405571,false⟩), (⟨25168, 2, 5⟩,⟨-50000000,0,107471951,false⟩), (⟨25169, 0, 6⟩,⟨-21842625000000,-48879650000000,127675133015663,false⟩), (⟨25170, 0, 7⟩,⟨0,-12500000,20753219,false⟩), (⟨25171, 0, 8⟩,⟨503509700000000,-225001100000000,-698856050588883,false⟩), (⟨25172, 2, 8⟩,⟨12500000,0,-26342263,false⟩)], ⟨-10000000,0,18758013,false⟩⟩
private theorem angle41_exact : poseAngle 1418 = 41 := by
  decide +kernel
private theorem radius41_exact : poseRadius 1418 = radius41 := by
  unfold poseRadius; rw [angle41_exact]; rfl
private theorem cache41_exact : cache41.Exact plan41 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache41.inputs = cutRows 1418
    simp only [cutRows,lowerCut,upperCut,radius41_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache41.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache41.supports) (by decide +kernel)
  · change cache41.closing = upper (leftHi + (poseRadius 1418).radius) false
    rw [radius41_exact]
    decide +kernel
private theorem shape41 : plan41.Shape := by decide +kernel
private theorem numeric41 : cache41.Numeric plan41 := by
  decide +kernel
private theorem plan41_checked : plan41.Check :=
  cache41.toCheck plan41 cache41_exact shape41 numeric41

def plan42 : DirectPlan := ⟨1419, some 3136, [⟨25173, 0, 2⟩, ⟨25174, 0, 3⟩, ⟨25175, 0, 4⟩, ⟨25176, 0, 5⟩, ⟨25177, 2, 6⟩, ⟨25178, 0, 7⟩, ⟨25179, 0, 8⟩, ⟨25180, 0, 9⟩, ⟨25181, 2, 9⟩], 0, 0⟩
private def cache42 : PlanCache := ⟨[⟨20000000,0,-37698411,true⟩, ⟨-50000000,0,111763041,true⟩, ⟨75032500000,178262500000,-443505209229,false⟩, ⟨0,12500000,-19971787,false⟩, ⟨-278926500000000,737324900000000,-588148543609039,false⟩, ⟨-155292600000000,65364100000000,233623266528859,false⟩, ⟨-100000000,0,219518851,false⟩, ⟨-4144540000000,-9846620000000,25257993211181,false⟩, ⟨0,-25000000,41650853,false⟩, ⟨27328325000000,-11502762500000,-39212225519287,false⟩, ⟨20000000,0,-42170003,false⟩, ⟨20000000,0,-42170003,false⟩, ⟨-100000000,0,219518851,false⟩, ⟨0,12500000,-19971787,false⟩, ⟨0,-25000000,41650853,false⟩, ⟨0,0,1,true⟩], [(⟨25173, 0, 2⟩,⟨75032500000,178262500000,-443504702639,false⟩), (⟨25174, 0, 3⟩,⟨0,6250000,-9985881,false⟩), (⟨25175, 0, 4⟩,⟨-278926500000000,737324900000000,-588146511106239,false⟩), (⟨25176, 0, 5⟩,⟨-155292600000000,65364100000000,233623707842259,false⟩), (⟨25177, 2, 6⟩,⟨-100000000,0,219519051,false⟩), (⟨25178, 0, 7⟩,⟨-4144540000000,-9846620000000,25258021193501,false⟩), (⟨25179, 0, 8⟩,⟨0,-25000000,41650903,false⟩), (⟨25180, 0, 9⟩,⟨3416040625000,-1437845312500,-4901518482139,false⟩), (⟨25181, 2, 9⟩,⟨20000000,0,-42169963,false⟩)], ⟨-20000000,0,37698411,false⟩⟩
private theorem angle42_exact : poseAngle 1419 = 42 := by
  decide +kernel
private theorem radius42_exact : poseRadius 1419 = radius42 := by
  unfold poseRadius; rw [angle42_exact]; rfl
private theorem cache42_exact : cache42.Exact plan42 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache42.inputs = cutRows 1419
    simp only [cutRows,lowerCut,upperCut,radius42_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache42.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache42.supports) (by decide +kernel)
  · change cache42.closing = upper (leftHi + (poseRadius 1419).radius) false
    rw [radius42_exact]
    decide +kernel
private theorem shape42 : plan42.Shape := by decide +kernel
private theorem numeric42 : cache42.Numeric plan42 := by
  decide +kernel
private theorem plan42_checked : plan42.Check :=
  cache42.toCheck plan42 cache42_exact shape42 numeric42

def plan43 : DirectPlan := ⟨1420, some 3138, [⟨25182, 0, 2⟩, ⟨25183, 0, 3⟩, ⟨25184, 0, 4⟩, ⟨25185, 2, 5⟩, ⟨25186, 0, 6⟩, ⟨25187, 0, 7⟩, ⟨25188, 0, 8⟩, ⟨25189, 2, 8⟩], 0, 0⟩
private def cache43 : PlanCache := ⟨[⟨50000000,0,-94714513,true⟩, ⟨-100000000,0,222589111,true⟩, ⟨103481750000000,261457200000000,-648924352851403,false⟩, ⟨0,25000000,-40462931,false⟩, ⟨-324744500000000,128530100000000,500421204637371,false⟩, ⟨-6250000,0,13715077,false⟩, ⟨-258704375000,-653643000000,1646864542787,false⟩, ⟨0,-20000000,33433801,false⟩, ⟨32474450000000,-12853010000000,-48077883208321,false⟩, ⟨50000000,0,-106463293,false⟩, ⟨50000000,0,-106463293,false⟩, ⟨-6250000,0,13715077,false⟩, ⟨0,25000000,-40462931,false⟩, ⟨0,-20000000,33433801,false⟩, ⟨0,0,1,true⟩], [(⟨25182, 0, 2⟩,⟨103481750000000,261457200000000,-648923622973503,false⟩), (⟨25183, 0, 3⟩,⟨0,25000000,-40462881,false⟩), (⟨25184, 0, 4⟩,⟨-324744500000000,128530100000000,500422111186571,false⟩), (⟨25185, 2, 5⟩,⟨-12500000,0,27430179,false⟩), (⟨25186, 0, 6⟩,⟨-1034817500000,-2614572000000,6587465469927,false⟩), (⟨25187, 0, 7⟩,⟨0,-20000000,33433841,false⟩), (⟨25188, 0, 8⟩,⟨32474450000000,-12853010000000,-48077792553401,false⟩), (⟨25189, 2, 8⟩,⟨50000000,0,-106463193,false⟩)], ⟨-50000000,0,94714513,false⟩⟩
private theorem angle43_exact : poseAngle 1420 = 43 := by
  decide +kernel
private theorem radius43_exact : poseRadius 1420 = radius43 := by
  unfold poseRadius; rw [angle43_exact]; rfl
private theorem cache43_exact : cache43.Exact plan43 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache43.inputs = cutRows 1420
    simp only [cutRows,lowerCut,upperCut,radius43_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache43.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache43.supports) (by decide +kernel)
  · change cache43.closing = upper (leftHi + (poseRadius 1420).radius) false
    rw [radius43_exact]
    decide +kernel
private theorem shape43 : plan43.Shape := by decide +kernel
private theorem numeric43 : cache43.Numeric plan43 := by
  decide +kernel
private theorem plan43_checked : plan43.Check :=
  cache43.toCheck plan43 cache43_exact shape43 numeric43

def plan44 : DirectPlan := ⟨1421, some 3140, [⟨25190, 0, 2⟩, ⟨25191, 0, 3⟩, ⟨25192, 0, 4⟩, ⟨25193, 2, 5⟩, ⟨25194, 0, 6⟩, ⟨25195, 0, 7⟩, ⟨25196, 0, 8⟩, ⟨25197, 2, 8⟩], 0, 0⟩
private def cache44 : PlanCache := ⟨[⟨50000000,0,-95193481,true⟩, ⟨-4000000,0,8865247,true⟩, ⟨84382850000000,227174700000000,-549602489758941,false⟩, ⟨0,100000000,-161134051,false⟩, ⟨-490041100000000,182023200000000,772620289978803,false⟩, ⟨-100000000,0,219337017,false⟩, ⟨-42191450000000,-113587350000000,281135841642177,false⟩, ⟨0,-100000000,167722321,false⟩, ⟨30627575000000,-11376450000000,-46705139803137,false⟩, ⟨10000000,0,-21297309,false⟩, ⟨10000000,0,-21297309,false⟩, ⟨-100000000,0,219337017,false⟩, ⟨0,100000000,-161134051,false⟩, ⟨0,-100000000,167722321,false⟩, ⟨0,0,1,true⟩], [(⟨25190, 0, 2⟩,⟨84382850000000,227174700000000,-549601866643841,false⟩), (⟨25191, 0, 3⟩,⟨0,100000000,-161133851,false⟩), (⟨25192, 0, 4⟩,⟨-490041100000000,182023200000000,772621634107403,false⟩), (⟨25193, 2, 5⟩,⟨-100000000,0,219337217,false⟩), (⟨25194, 0, 6⟩,⟨-42191450000000,-113587350000000,281136153199777,false⟩), (⟨25195, 0, 7⟩,⟨0,-100000000,167722521,false⟩), (⟨25196, 0, 8⟩,⟨30627575000000,-11376450000000,-46705055795087,false⟩), (⟨25197, 2, 8⟩,⟨10000000,0,-21297289,false⟩)], ⟨-50000000,0,95193481,false⟩⟩
private theorem angle44_exact : poseAngle 1421 = 44 := by
  decide +kernel
private theorem radius44_exact : poseRadius 1421 = radius44 := by
  unfold poseRadius; rw [angle44_exact]; rfl
private theorem cache44_exact : cache44.Exact plan44 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache44.inputs = cutRows 1421
    simp only [cutRows,lowerCut,upperCut,radius44_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache44.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache44.supports) (by decide +kernel)
  · change cache44.closing = upper (leftHi + (poseRadius 1421).radius) false
    rw [radius44_exact]
    decide +kernel
private theorem shape44 : plan44.Shape := by decide +kernel
private theorem numeric44 : cache44.Numeric plan44 := by
  decide +kernel
private theorem plan44_checked : plan44.Check :=
  cache44.toCheck plan44 cache44_exact shape44 numeric44

def plan45 : DirectPlan := ⟨1422, some 3142, [⟨25198, 0, 2⟩, ⟨25199, 0, 3⟩, ⟨25200, 0, 4⟩, ⟨25201, 2, 5⟩, ⟨25202, 0, 6⟩, ⟨25203, 0, 7⟩, ⟨25204, 0, 8⟩, ⟨25205, 2, 8⟩], 0, 0⟩
private def cache45 : PlanCache := ⟨[⟨5000000,0,-9568097,true⟩, ⟨-100000000,0,220656197,true⟩, ⟨8375900000000,24080593750000,-56799821829123,false⟩, ⟨0,6250000,-10025891,false⟩, ⟨-65088140000000,22639470000000,104888816300617,false⟩, ⟨-10000000,0,21920939,false⟩, ⟨-67007200000000,-192644700000000,468454909024217,false⟩, ⟨0,-20000000,33652683,false⟩, ⟨65088140000000,-22639480000000,-102077444602171,false⟩, ⟨100000000,0,-213092347,false⟩, ⟨100000000,0,-213092347,false⟩, ⟨-10000000,0,21920939,false⟩, ⟨0,6250000,-10025891,false⟩, ⟨0,-20000000,33652683,false⟩, ⟨0,0,1,true⟩], [(⟨25198, 0, 2⟩,⟨16751800000000,48161187500000,-113599513832271,false⟩), (⟨25199, 0, 3⟩,⟨0,12500000,-20051757,false⟩), (⟨25200, 0, 4⟩,⟨-65088140000000,22639470000000,104888991755837,false⟩), (⟨25201, 2, 5⟩,⟨-10000000,0,21920959,false⟩), (⟨25202, 0, 6⟩,⟨-67007200000000,-192644700000000,468455428328017,false⟩), (⟨25203, 0, 7⟩,⟨0,-20000000,33652723,false⟩), (⟨25204, 0, 8⟩,⟨65088140000000,-22639480000000,-102077269146931,false⟩), (⟨25205, 2, 8⟩,⟨100000000,0,-213092147,false⟩)], ⟨-5000000,0,9568097,false⟩⟩
private theorem angle45_exact : poseAngle 1422 = 45 := by
  decide +kernel
private theorem radius45_exact : poseRadius 1422 = radius45 := by
  unfold poseRadius; rw [angle45_exact]; rfl
private theorem cache45_exact : cache45.Exact plan45 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache45.inputs = cutRows 1422
    simp only [cutRows,lowerCut,upperCut,radius45_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache45.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache45.supports) (by decide +kernel)
  · change cache45.closing = upper (leftHi + (poseRadius 1422).radius) false
    rw [radius45_exact]
    decide +kernel
private theorem shape45 : plan45.Shape := by decide +kernel
private theorem numeric45 : cache45.Numeric plan45 := by
  decide +kernel
private theorem plan45_checked : plan45.Check :=
  cache45.toCheck plan45 cache45_exact shape45 numeric45

def plan46 : DirectPlan := ⟨1423, some 3144, [⟨25206, 0, 2⟩, ⟨25207, 0, 3⟩, ⟨25208, 0, 4⟩, ⟨25209, 2, 5⟩, ⟨25210, 0, 6⟩, ⟨25211, 0, 7⟩, ⟨25212, 0, 8⟩, ⟨25213, 2, 8⟩], 0, 0⟩
private def cache46 : PlanCache := ⟨[⟨10000000,0,-19235021,true⟩, ⟨-100000000,0,219667927,true⟩, ⟨183280000000,564127500000,-1297577630349,false⟩, ⟨0,12500000,-19961971,false⟩, ⟨-161401380000000,52437820000000,265595307231187,false⟩, ⟨-50000000,0,109530679,false⟩, ⟨-25659175000000,-78977875000000,188707388990689,false⟩, ⟨0,-20000000,33758481,false⟩, ⟨403503400000000,-131094500000000,-649894520766703,false⟩, ⟨12500000,0,-26660019,false⟩, ⟨12500000,0,-26660019,false⟩, ⟨-50000000,0,109530679,false⟩, ⟨0,12500000,-19961971,false⟩, ⟨0,-20000000,33758481,false⟩, ⟨0,0,1,true⟩], [(⟨25206, 0, 2⟩,⟨91640000000,282063750000,-648788067767,false⟩), (⟨25207, 0, 3⟩,⟨0,6250000,-9980973,false⟩), (⟨25208, 0, 4⟩,⟨-161401380000000,52437820000000,265595734909587,false⟩), (⟨25209, 2, 5⟩,⟨-50000000,0,109530779,false⟩), (⟨25210, 0, 6⟩,⟨-25659175000000,-78977875000000,188707598264789,false⟩), (⟨25211, 0, 7⟩,⟨0,-20000000,33758521,false⟩), (⟨25212, 0, 8⟩,⟨403503400000000,-131094500000000,-649893451570903,false⟩), (⟨25213, 2, 8⟩,⟨6250000,0,-13329997,false⟩)], ⟨-10000000,0,19235021,false⟩⟩
private theorem angle46_exact : poseAngle 1423 = 46 := by
  decide +kernel
private theorem radius46_exact : poseRadius 1423 = radius46 := by
  unfold poseRadius; rw [angle46_exact]; rfl
private theorem cache46_exact : cache46.Exact plan46 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache46.inputs = cutRows 1423
    simp only [cutRows,lowerCut,upperCut,radius46_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache46.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache46.supports) (by decide +kernel)
  · change cache46.closing = upper (leftHi + (poseRadius 1423).radius) false
    rw [radius46_exact]
    decide +kernel
private theorem shape46 : plan46.Shape := by decide +kernel
private theorem numeric46 : cache46.Numeric plan46 := by
  decide +kernel
private theorem plan46_checked : plan46.Check :=
  cache46.toCheck plan46 cache46_exact shape46 numeric46

def plan47 : DirectPlan := ⟨1424, some 3146, [⟨25214, 0, 2⟩, ⟨25215, 0, 3⟩, ⟨25216, 0, 4⟩, ⟨25217, 1, 2⟩, ⟨25218, 0, 6⟩, ⟨25219, 0, 7⟩, ⟨25220, 0, 8⟩, ⟨25221, 2, 8⟩], 0, 0⟩
private def cache47 : PlanCache := ⟨[⟨100000000,0,-193348199,true⟩, ⟨-50000000,0,109334969,true⟩, ⟨18638175000000,61595450000000,-138183254257503,false⟩, ⟨0,100000000,-158981739,false⟩, ⟨-958199000000000,289941900000000,1608720008969049,false⟩, ⟨-400000,0,875583,false⟩, ⟨-7455270000000,-24638180000000,57850353669499,false⟩, ⟨0,-100000000,169309457,false⟩, ⟨958199000000000,-289941900000000,-1582947625619207,false⟩, ⟨12500000,0,-26691539,false⟩, ⟨12500000,0,-26691539,false⟩, ⟨-400000,0,875583,false⟩, ⟨0,100000000,-158981739,false⟩, ⟨0,-100000000,169309457,false⟩, ⟨0,0,1,true⟩], [(⟨25214, 0, 2⟩,⟨18638175000000,61595450000000,-138183093790253,false⟩), (⟨25215, 0, 3⟩,⟨0,100000000,-158981539,false⟩), (⟨25216, 0, 4⟩,⟨-294513200000000,89116900000000,494458876208001,false⟩), (⟨25217, 1, 2⟩,⟨-50000000,0,109335019,false⟩), (⟨25218, 0, 6⟩,⟨-33858400000000,-111895300000000,262730005610209,false⟩), (⟨25219, 0, 7⟩,⟨0,-100000000,169309657,false⟩), (⟨25220, 0, 8⟩,⟨958199000000000,-289941900000000,-1582945129337407,false⟩), (⟨25221, 2, 8⟩,⟨6250000,0,-13345757,false⟩)], ⟨-100000000,0,193348199,false⟩⟩
private theorem angle47_exact : poseAngle 1424 = 47 := by
  decide +kernel
private theorem radius47_exact : poseRadius 1424 = radius47 := by
  unfold poseRadius; rw [angle47_exact]; rfl
private theorem cache47_exact : cache47.Exact plan47 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache47.inputs = cutRows 1424
    simp only [cutRows,lowerCut,upperCut,radius47_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache47.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache47.supports) (by decide +kernel)
  · change cache47.closing = upper (leftHi + (poseRadius 1424).radius) false
    rw [radius47_exact]
    decide +kernel
private theorem shape47 : plan47.Shape := by decide +kernel
private theorem numeric47 : cache47.Numeric plan47 := by
  decide +kernel
private theorem plan47_checked : plan47.Check :=
  cache47.toCheck plan47 cache47_exact shape47 numeric47

def plan48 : DirectPlan := ⟨1425, some 3148, [⟨25223, 0, 2⟩, ⟨25224, 0, 3⟩, ⟨25225, 0, 4⟩, ⟨25226, 1, 2⟩, ⟨25227, 0, 6⟩, ⟨25228, 0, 7⟩, ⟨25229, 0, 8⟩, ⟨25230, 2, 8⟩], 0, 0⟩
private def cache48 : PlanCache := ⟨[⟨50000000,0,-97176259,true⟩, ⟨-100000000,0,217665619,true⟩, ⟨49676700000000,176856500000000,-387029249342573,false⟩, ⟨0,20000000,-31655009,false⟩, ⟨-44171092000000,12407112000000,75601451054119,false⟩, ⟨-100000000,0,218715223,false⟩, ⟨-6209587500000,-22107062500000,51012553432097,false⟩, ⟨0,-50000000,84907393,false⟩, ⟨1104277300000000,-310177800000000,-1868962710515753,false⟩, ⟨100000000,0,-213844679,false⟩, ⟨100000000,0,-213844679,false⟩, ⟨-100000000,0,218715223,false⟩, ⟨0,20000000,-31655009,false⟩, ⟨0,-50000000,84907393,false⟩, ⟨0,0,1,true⟩], [(⟨25223, 0, 2⟩,⟨49676700000000,176856500000000,-387028796276173,false⟩), (⟨25224, 0, 3⟩,⟨0,20000000,-31654969,false⟩), (⟨25225, 0, 4⟩,⟨-73056760000000,20520740000000,125041173727049,false⟩), (⟨25226, 1, 2⟩,⟨-100000000,0,217665719,false⟩), (⟨25227, 0, 6⟩,⟨-2019180000000,-7188610000000,16587884632459,false⟩), (⟨25228, 0, 7⟩,⟨0,-50000000,84907493,false⟩), (⟨25229, 0, 8⟩,⟨1104277300000000,-310177800000000,-1868959881605553,false⟩), (⟨25230, 2, 8⟩,⟨100000000,0,-213844479,false⟩)], ⟨-50000000,0,97176259,false⟩⟩
private theorem angle48_exact : poseAngle 1425 = 48 := by
  decide +kernel
private theorem radius48_exact : poseRadius 1425 = radius48 := by
  unfold poseRadius; rw [angle48_exact]; rfl
private theorem cache48_exact : cache48.Exact plan48 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache48.inputs = cutRows 1425
    simp only [cutRows,lowerCut,upperCut,radius48_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache48.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache48.supports) (by decide +kernel)
  · change cache48.closing = upper (leftHi + (poseRadius 1425).radius) false
    rw [radius48_exact]
    decide +kernel
private theorem shape48 : plan48.Shape := by decide +kernel
private theorem numeric48 : cache48.Numeric plan48 := by
  decide +kernel
private theorem plan48_checked : plan48.Check :=
  cache48.toCheck plan48 cache48_exact shape48 numeric48

def plan49 : DirectPlan := ⟨1426, some 3150, [⟨25232, 0, 2⟩, ⟨25233, 0, 3⟩, ⟨25234, 0, 4⟩, ⟨25235, 1, 2⟩, ⟨25236, 1, 8⟩, ⟨25237, 0, 8⟩, ⟨25238, 2, 8⟩], 0, 0⟩
private def cache49 : PlanCache := ⟨[⟨25000000,0,-48839991,true⟩, ⟨-100000000,0,216658173,true⟩, ⟨697945000000,2687027500000,-5736763937969,false⟩, ⟨0,50000000,-78789151,false⟩, ⟨-311274050000000,80852150000000,542730767054873,false⟩, ⟨-50000000,0,109261129,false⟩, ⟨-27917800000000,-107481100000000,243756146250039,false⟩, ⟨0,-100000000,170308643,false⟩, ⟨622548100000000,-161704300000000,-1078317299472677,false⟩, ⟨2500000,0,-5355329,false⟩, ⟨2500000,0,-5355329,false⟩, ⟨-50000000,0,109261129,false⟩, ⟨0,50000000,-78789151,false⟩, ⟨0,-100000000,170308643,false⟩, ⟨0,0,1,true⟩], [(⟨25232, 0, 2⟩,⟨87243125000,335878437500,-717094646003,false⟩), (⟨25233, 0, 3⟩,⟨0,50000000,-78789051,false⟩), (⟨25234, 0, 4⟩,⟨-263700200000000,68495050000000,459782667786793,false⟩), (⟨25235, 1, 2⟩,⟨-100000000,0,216658273,false⟩), (⟨25236, 1, 8⟩,⟨0,-100000000,167271363,false⟩), (⟨25237, 0, 8⟩,⟨941348200000000,-244511300000000,-1630509486141167,false⟩), (⟨25238, 2, 8⟩,⟨625000,0,-1338831,false⟩)], ⟨-25000000,0,48839991,false⟩⟩
private theorem angle49_exact : poseAngle 1426 = 49 := by
  decide +kernel
private theorem radius49_exact : poseRadius 1426 = radius49 := by
  unfold poseRadius; rw [angle49_exact]; rfl
private theorem cache49_exact : cache49.Exact plan49 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache49.inputs = cutRows 1426
    simp only [cutRows,lowerCut,upperCut,radius49_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache49.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache49.supports) (by decide +kernel)
  · change cache49.closing = upper (leftHi + (poseRadius 1426).radius) false
    rw [radius49_exact]
    decide +kernel
private theorem shape49 : plan49.Shape := by decide +kernel
private theorem numeric49 : cache49.Numeric plan49 := by
  decide +kernel
private theorem plan49_checked : plan49.Check :=
  cache49.toCheck plan49 cache49_exact shape49 numeric49

def plan50 : DirectPlan := ⟨1427, some 3152, [⟨25240, 0, 2⟩, ⟨25241, 0, 3⟩, ⟨25242, 0, 4⟩, ⟨25243, 1, 2⟩, ⟨25244, 1, 8⟩, ⟨25245, 0, 8⟩, ⟨25246, 2, 8⟩], 0, 0⟩
private def cache50 : PlanCache := ⟨[⟨4000000,0,-7854701,true⟩, ⟨-25000000,0,53912653,true⟩, ⟨208650000000,872525000000,-1817572614121,false⟩, ⟨0,25000000,-39223469,false⟩, ⟨-1380542700000000,330132100000000,2450456170456327,false⟩, ⟨-10000000,0,21831917,false⟩, ⟨-208650000000,-872525000000,1944918795481,false⟩, ⟨0,-10000000,17079131,false⟩, ⟨172567837500000,-41266512500000,-305606199454907,false⟩, ⟨100000000,0,-214633737,false⟩, ⟨100000000,0,-214633737,false⟩, ⟨-10000000,0,21831917,false⟩, ⟨0,25000000,-39223469,false⟩, ⟨0,-10000000,17079131,false⟩, ⟨0,0,1,true⟩], [(⟨25240, 0, 2⟩,⟨208650000000,872525000000,-1817570451771,false⟩), (⟨25241, 0, 3⟩,⟨0,25000000,-39223419,false⟩), (⟨25242, 0, 4⟩,⟨-264566300000000,63266300000000,469604472832299,false⟩), (⟨25243, 1, 2⟩,⟨-12500000,0,26956339,false⟩), (⟨25244, 1, 8⟩,⟨0,-50000000,80619429,false⟩), (⟨25245, 0, 8⟩,⟨68044400000,-16271600000,-120501954969,false⟩), (⟨25246, 2, 8⟩,⟨100000000,0,-214633537,false⟩)], ⟨-4000000,0,7854701,false⟩⟩
private theorem angle50_exact : poseAngle 1427 = 50 := by
  decide +kernel
private theorem radius50_exact : poseRadius 1427 = radius50 := by
  unfold poseRadius; rw [angle50_exact]; rfl
private theorem cache50_exact : cache50.Exact plan50 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache50.inputs = cutRows 1427
    simp only [cutRows,lowerCut,upperCut,radius50_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache50.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache50.supports) (by decide +kernel)
  · change cache50.closing = upper (leftHi + (poseRadius 1427).radius) false
    rw [radius50_exact]
    decide +kernel
private theorem shape50 : plan50.Shape := by decide +kernel
private theorem numeric50 : cache50.Numeric plan50 := by
  decide +kernel
private theorem plan50_checked : plan50.Check :=
  cache50.toCheck plan50 cache50_exact shape50 numeric50

def plan51 : DirectPlan := ⟨1428, none, [], 2, 5⟩
private def cache51 : PlanCache := ⟨[⟨100000000,0,-202270343,true⟩, ⟨-50000000,0,104873897,true⟩, ⟨13340000000,106740000000,-183268751599,false⟩, ⟨0,50000000,-74465091,false⟩, ⟨-2436425000000,304450000000,3984875780923,false⟩, ⟨-50000000,0,91088181,false⟩, ⟨-333450000000,-2668450000000,4584200475569,false⟩, ⟨0,-100000000,149034509,false⟩, ⟨9745600000000,-1217900000000,-15933867532041,false⟩, ⟨100000000,0,-182110613,false⟩, ⟨100000000,0,-182110613,false⟩, ⟨-50000000,0,91088181,false⟩, ⟨0,50000000,-74465091,false⟩, ⟨0,-100000000,149034509,false⟩, ⟨0,0,1,true⟩], [], ⟨-100000000,0,202270343,false⟩⟩
private theorem angle51_exact : poseAngle 1428 = 56 := by
  decide +kernel
private theorem radius51_exact : poseRadius 1428 = radius56 := by
  unfold poseRadius; rw [angle51_exact]; rfl
private theorem cache51_exact : cache51.Exact plan51 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache51.inputs = cutRows 1428
    simp only [cutRows,lowerCut,upperCut,radius51_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache51.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache51.supports) (by decide +kernel)
  · change cache51.closing = upper (leftHi + (poseRadius 1428).radius) false
    rw [radius51_exact]
    decide +kernel
private theorem shape51 : plan51.Shape := by decide +kernel
private theorem numeric51 : cache51.Numeric plan51 := by
  decide +kernel
private theorem plan51_checked : plan51.Check :=
  cache51.toCheck plan51 cache51_exact shape51 numeric51

def plan52 : DirectPlan := ⟨1429, none, [], 1, 2⟩
private def cache52 : PlanCache := ⟨[⟨2500000,0,-5210979,true⟩, ⟨-100000000,0,203578977,true⟩, ⟨2487950000000,317204750000000,-480195432197927,false⟩, ⟨103393750000,30682606250000,-46186515273669,false⟩, ⟨0,50000000,-74902179,false⟩, ⟨-26045500000000,204300000000,55776820286391,false⟩, ⟨-10000000,0,21532857,false⟩, ⟨-6056825000000,-772232975000000,1171893596706269,false⟩, ⟨0,-100000000,150307287,false⟩, ⟨3085450000000,-24200000000,-5654400304771,false⟩, ⟨50000000,0,-92218073,false⟩, ⟨50000000,0,-92218073,false⟩, ⟨-10000000,0,21532857,false⟩, ⟨0,50000000,-74902179,false⟩, ⟨0,-100000000,150307287,false⟩, ⟨0,0,1,true⟩], [], ⟨-2500000,0,5210979,false⟩⟩
private theorem angle52_exact : poseAngle 1429 = 63 := by
  decide +kernel
private theorem radius52_exact : poseRadius 1429 = radius63 := by
  unfold poseRadius; rw [angle52_exact]; rfl
private theorem cache52_exact : cache52.Exact plan52 := by
  unfold PlanCache.Exact
  refine ⟨?_, ?_, ?_, ?_⟩
  · change cache52.inputs = cutRows 1429
    simp only [cutRows,lowerCut,upperCut,radius52_exact]
    decide +kernel
  · decide +kernel
  · exact @of_decide_eq_true
      (∀ entry ∈ cache52.supports, rows entry.1.target = entry.2)
      (List.decidableBAll _ cache52.supports) (by decide +kernel)
  · change cache52.closing = upper (leftHi + (poseRadius 1429).radius) false
    rw [radius52_exact]
    decide +kernel
private theorem shape52 : plan52.Shape := by decide +kernel
private theorem numeric52 : cache52.Numeric plan52 := by
  decide +kernel
private theorem plan52_checked : plan52.Check :=
  cache52.toCheck plan52 cache52_exact shape52 numeric52

def plans : List DirectPlan := [plan00, plan01, plan02, plan03, plan04, plan05, plan06, plan07, plan08, plan09, plan10, plan11, plan12, plan13, plan14, plan15, plan16, plan17, plan18, plan19, plan20, plan21, plan22, plan23, plan24, plan25, plan26, plan27, plan28, plan29, plan30, plan31, plan32, plan33, plan34, plan35, plan36, plan37, plan38, plan39, plan40, plan41, plan42, plan43, plan44, plan45, plan46, plan47, plan48, plan49, plan50, plan51, plan52]

theorem plans_checked : ∀ plan ∈ plans, plan.Check := by
  intro plan member
  simp only [plans,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact plan00_checked
  · exact plan01_checked
  · exact plan02_checked
  · exact plan03_checked
  · exact plan04_checked
  · exact plan05_checked
  · exact plan06_checked
  · exact plan07_checked
  · exact plan08_checked
  · exact plan09_checked
  · exact plan10_checked
  · exact plan11_checked
  · exact plan12_checked
  · exact plan13_checked
  · exact plan14_checked
  · exact plan15_checked
  · exact plan16_checked
  · exact plan17_checked
  · exact plan18_checked
  · exact plan19_checked
  · exact plan20_checked
  · exact plan21_checked
  · exact plan22_checked
  · exact plan23_checked
  · exact plan24_checked
  · exact plan25_checked
  · exact plan26_checked
  · exact plan27_checked
  · exact plan28_checked
  · exact plan29_checked
  · exact plan30_checked
  · exact plan31_checked
  · exact plan32_checked
  · exact plan33_checked
  · exact plan34_checked
  · exact plan35_checked
  · exact plan36_checked
  · exact plan37_checked
  · exact plan38_checked
  · exact plan39_checked
  · exact plan40_checked
  · exact plan41_checked
  · exact plan42_checked
  · exact plan43_checked
  · exact plan44_checked
  · exact plan45_checked
  · exact plan46_checked
  · exact plan47_checked
  · exact plan48_checked
  · exact plan49_checked
  · exact plan50_checked
  · exact plan51_checked
  · exact plan52_checked
theorem plans_covered : DirectCoverCheck continuousScout898Domain5_0Ids
    continuousScout898Domain5_11Ids plans := by decide +kernel

#print axioms plans_checked
end N12Compact.C898Chord.Fused
