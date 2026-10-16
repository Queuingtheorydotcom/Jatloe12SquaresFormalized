import Compact.Bridge.AngleSection
import S12.AngleData64
import S12.AngleData128

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.Preservation.Chords.Radii
open S12 S12Pilot
open AngleSection
noncomputable section

def radius0 : Radius := ⟨(4223/4097),(24207499/50000000)⟩
theorem radius0_checked : radius0.Check angle64_0 := by
  norm_num [radius0,Radius.Check,angle64_0,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius1 : Radius := ⟨(1087/1025),(46792671/100000000)⟩
theorem radius1_checked : radius1.Check angle64_1 := by
  norm_num [radius1,Radius.Check,angle64_1,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius2 : Radius := ⟨(4471/4105),(902891/2000000)⟩
theorem radius2_checked : radius2.Check angle64_2 := by
  norm_num [radius2,Radius.Check,angle64_2,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius3 : Radius := ⟨(287/257),(43482111/100000000)⟩
theorem radius3_checked : radius3.Check angle64_3 := by
  norm_num [radius3,Radius.Check,angle64_3,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius4 : Radius := ⟨(4711/4121),(41816673/100000000)⟩
theorem radius4_checked : radius4.Check angle64_4 := by
  norm_num [radius4,Radius.Check,angle64_4,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius5 : Radius := ⟨(1207/1033),(20079651/50000000)⟩
theorem radius5_checked : radius5.Check angle64_5 := by
  norm_num [radius5,Radius.Check,angle64_5,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius6 : Radius := ⟨(4943/4145),(1540829/4000000)⟩
theorem radius6_checked : radius6.Check angle64_6 := by
  norm_num [radius6,Radius.Check,angle64_6,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius7 : Radius := ⟨(79/65),(18455621/50000000)⟩
theorem radius7_checked : radius7.Check angle64_7 := by
  norm_num [radius7,Radius.Check,angle64_7,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius8 : Radius := ⟨(5167/4177),(706813/2000000)⟩
theorem radius8_checked : radius8.Check angle64_8 := by
  norm_num [radius8,Radius.Check,angle64_8,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius9 : Radius := ⟨(1319/1049),(33818171/100000000)⟩
theorem radius9_checked : radius9.Check angle64_9 := by
  norm_num [radius9,Radius.Check,angle64_9,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius10 : Radius := ⟨(5383/4217),(8088099/25000000)⟩
theorem radius10_checked : radius10.Check angle64_10 := by
  norm_num [radius10,Radius.Check,angle64_10,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius11 : Radius := ⟨(343/265),(7737807/25000000)⟩
theorem radius11_checked : radius11.Check angle64_11 := by
  norm_num [radius11,Radius.Check,angle64_11,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius12 : Radius := ⟨(5591/4265),(370273/1250000)⟩
theorem radius12_checked : radius12.Check angle64_12 := by
  norm_num [radius12,Radius.Check,angle64_12,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius13 : Radius := ⟨(1423/1073),(3546331/12500000)⟩
theorem radius13_checked : radius13.Check angle64_13 := by
  norm_num [radius13,Radius.Check,angle64_13,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius14 : Radius := ⟨(5791/4321),(27203279/100000000)⟩
theorem radius14_checked : radius14.Check angle64_14 := by
  norm_num [radius14,Radius.Check,angle64_14,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius15 : Radius := ⟨(23/17),(26124567/100000000)⟩
theorem radius15_checked : radius15.Check angle64_15 := by
  norm_num [radius15,Radius.Check,angle64_15,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius16 : Radius := ⟨(5983/4385),(12569271/50000000)⟩
theorem radius16_checked : radius16.Check angle64_16 := by
  norm_num [radius16,Radius.Check,angle64_16,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius17 : Radius := ⟨(1519/1105),(12124219/50000000)⟩
theorem radius17_checked : radius17.Check angle64_17 := by
  norm_num [radius17,Radius.Check,angle64_17,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius18 : Radius := ⟨(6167/4457),(23456707/100000000)⟩
theorem radius18_checked : radius18.Check angle64_18 := by
  norm_num [radius18,Radius.Check,angle64_18,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius19 : Radius := ⟨(391/281),(4553007/20000000)⟩
theorem radius19_checked : radius19.Check angle64_19 := by
  norm_num [radius19,Radius.Check,angle64_19,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius20 : Radius := ⟨(6343/4537),(2771797/12500000)⟩
theorem radius20_checked : radius20.Check angle64_20 := by
  norm_num [radius20,Radius.Check,angle64_20,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius21 : Radius := ⟨(1607/1145),(21684979/100000000)⟩
theorem radius21_checked : radius21.Check angle64_21 := by
  norm_num [radius21,Radius.Check,angle64_21,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius22 : Radius := ⟨(6511/4625),(2129643/10000000)⟩
theorem radius22_checked : radius22.Check angle64_22 := by
  norm_num [radius22,Radius.Check,angle64_22,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius23 : Radius := ⟨(103/73),(21007693/100000000)⟩
theorem radius23_checked : radius23.Check angle64_23 := by
  norm_num [radius23,Radius.Check,angle64_23,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius24 : Radius := ⟨(6671/4721),(20817159/100000000)⟩
theorem radius24_checked : radius24.Check angle64_24 := by
  norm_num [radius24,Radius.Check,angle64_24,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius25 : Radius := ⟨(1687/1193),(20722691/100000000)⟩
theorem radius25_checked : radius25.Check angle64_25 := by
  norm_num [radius25,Radius.Check,angle64_25,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius26 : Radius := ⟨(707107/500000),(10355319/50000000)⟩
theorem radius26_checked : radius26.Check angle64_26 := by
  norm_num [radius26,Radius.Check,angle64_26,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius27 : Radius := ⟨(6823/4825),(828867/4000000)⟩
theorem radius27_checked : radius27.Check angle64_27 := by
  norm_num [radius27,Radius.Check,angle64_27,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius28 : Radius := ⟨(431/305),(325173/1562500)⟩
theorem radius28_checked : radius28.Check angle64_28 := by
  norm_num [radius28,Radius.Check,angle64_28,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius29 : Radius := ⟨(6967/4937),(2098747/10000000)⟩
theorem radius29_checked : radius29.Check angle64_29 := by
  norm_num [radius29,Radius.Check,angle64_29,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius30 : Radius := ⟨(1759/1249),(21247133/100000000)⟩
theorem radius30_checked : radius30.Check angle64_30 := by
  norm_num [radius30,Radius.Check,angle64_30,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius31 : Radius := ⟨(7103/5057),(10793027/50000000)⟩
theorem radius31_checked : radius31.Check angle64_31 := by
  norm_num [radius31,Radius.Check,angle64_31,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius32 : Radius := ⟨(7/5),(11/50)⟩
theorem radius32_checked : radius32.Check angle64_32 := by
  norm_num [radius32,Radius.Check,angle64_32,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius33 : Radius := ⟨(7231/5185),(22484559/100000000)⟩
theorem radius33_checked : radius33.Check angle64_33 := by
  norm_num [radius33,Radius.Check,angle64_33,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius34 : Radius := ⟨(1823/1313),(23035187/100000000)⟩
theorem radius34_checked : radius34.Check angle64_34 := by
  norm_num [radius34,Radius.Check,angle64_34,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius35 : Radius := ⟨(7351/5321),(23647249/100000000)⟩
theorem radius35_checked : radius35.Check angle64_35 := by
  norm_num [radius35,Radius.Check,angle64_35,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius36 : Radius := ⟨(463/337),(12158027/50000000)⟩
theorem radius36_checked : radius36.Check angle64_36 := by
  norm_num [radius36,Radius.Check,angle64_36,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius37 : Radius := ⟨(7463/5465),(5007379/20000000)⟩
theorem radius37_checked : radius37.Check angle64_37 := by
  norm_num [radius37,Radius.Check,angle64_37,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius38 : Radius := ⟨(1879/1385),(645127/2500000)⟩
theorem radius38_checked : radius38.Check angle64_38 := by
  norm_num [radius38,Radius.Check,angle64_38,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius39 : Radius := ⟨(7567/5617),(13307981/50000000)⟩
theorem radius39_checked : radius39.Check angle64_39 := by
  norm_num [radius39,Radius.Check,angle64_39,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius40 : Radius := ⟨(119/89),(13732483/50000000)⟩
theorem radius40_checked : radius40.Check angle64_40 := by
  norm_num [radius40,Radius.Check,angle64_40,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius41 : Radius := ⟨(7663/5777),(7086903/25000000)⟩
theorem radius41_checked : radius41.Check angle64_41 := by
  norm_num [radius41,Radius.Check,angle64_41,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius42 : Radius := ⟨(1927/1465),(29259537/100000000)⟩
theorem radius42_checked : radius42.Check angle64_42 := by
  norm_num [radius42,Radius.Check,angle64_42,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius43 : Radius := ⟨(7751/5945),(7549127/25000000)⟩
theorem radius43_checked : radius43.Check angle64_43 := by
  norm_num [radius43,Radius.Check,angle64_43,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius44 : Radius := ⟨(487/377),(7788611/25000000)⟩
theorem radius44_checked : radius44.Check angle64_44 := by
  norm_num [radius44,Radius.Check,angle64_44,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius45 : Radius := ⟨(7831/6121),(16064711/50000000)⟩
theorem radius45_checked : radius45.Check angle64_45 := by
  norm_num [radius45,Radius.Check,angle64_45,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius46 : Radius := ⟨(1967/1553),(8279423/25000000)⟩
theorem radius46_checked : radius46.Check angle64_46 := by
  norm_num [radius46,Radius.Check,angle64_46,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius47 : Radius := ⟨(7903/6305),(34115681/100000000)⟩
theorem radius47_checked : radius47.Check angle64_47 := by
  norm_num [radius47,Radius.Check,angle64_47,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius48 : Radius := ⟨(31/25),(439/1250)⟩
theorem radius48_checked : radius48.Check angle64_48 := by
  norm_num [radius48,Radius.Check,angle64_48,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius49 : Radius := ⟨(7967/6497),(18063723/50000000)⟩
theorem radius49_checked : radius49.Check angle64_49 := by
  norm_num [radius49,Radius.Check,angle64_49,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius50 : Radius := ⟨(1999/1649),(37135007/100000000)⟩
theorem radius50_checked : radius50.Check angle64_50 := by
  norm_num [radius50,Radius.Check,angle64_50,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius51 : Radius := ⟨(8023/6697),(19069931/50000000)⟩
theorem radius51_checked : radius51.Check angle64_51 := by
  norm_num [radius51,Radius.Check,angle64_51,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius52 : Radius := ⟨(503/425),(39139377/100000000)⟩
theorem radius52_checked : radius52.Check angle64_52 := by
  norm_num [radius52,Radius.Check,angle64_52,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius53 : Radius := ⟨(8071/6905),(1254097/3125000)⟩
theorem radius53_checked : radius53.Check angle64_53 := by
  norm_num [radius53,Radius.Check,angle64_53,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius54 : Radius := ⟨(2023/1753),(20556391/50000000)⟩
theorem radius54_checked : radius54.Check angle64_54 := by
  norm_num [radius54,Radius.Check,angle64_54,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius55 : Radius := ⟨(8111/7121),(1683293/4000000)⟩
theorem radius55_checked : radius55.Check angle64_55 := by
  norm_num [radius55,Radius.Check,angle64_55,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius56 : Radius := ⟨(127/113),(1721513/4000000)⟩
theorem radius56_checked : radius56.Check angle64_56 := by
  norm_num [radius56,Radius.Check,angle64_56,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius57 : Radius := ⟨(8143/7345),(21988771/50000000)⟩
theorem radius57_checked : radius57.Check angle64_57 := by
  norm_num [radius57,Radius.Check,angle64_57,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius58 : Radius := ⟨(2039/1865),(22449949/50000000)⟩
theorem radius58_checked : radius58.Check angle64_58 := by
  norm_num [radius58,Radius.Check,angle64_58,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius59 : Radius := ⟨(8167/7577),(45803473/100000000)⟩
theorem radius59_checked : radius59.Check angle64_59 := by
  norm_num [radius59,Radius.Check,angle64_59,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius60 : Radius := ⟨(511/481),(9337399/20000000)⟩
theorem radius60_checked : radius60.Check angle64_60 := by
  norm_num [radius60,Radius.Check,angle64_60,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius61 : Radius := ⟨(8183/7817),(47549337/100000000)⟩
theorem radius61_checked : radius61.Check angle64_61 := by
  norm_num [radius61,Radius.Check,angle64_61,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius62 : Radius := ⟨(2047/1985),(12097377/25000000)⟩
theorem radius62_checked : radius62.Check angle64_62 := by
  norm_num [radius62,Radius.Check,angle64_62,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius63 : Radius := ⟨(8191/8065),(24603321/50000000)⟩
theorem radius63_checked : radius63.Check angle64_63 := by
  norm_num [radius63,Radius.Check,angle64_63,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius64 : Radius := ⟨(16639/16385),(9842577/20000000)⟩
theorem radius64_checked : radius64.Check angle128_0 := by
  norm_num [radius64,Radius.Check,angle128_0,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius65 : Radius := ⟨(4223/4097),(24207499/50000000)⟩
theorem radius65_checked : radius65.Check angle128_1 := by
  norm_num [radius65,Radius.Check,angle128_1,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius66 : Radius := ⟨(17143/16393),(47607779/100000000)⟩
theorem radius66_checked : radius66.Check angle128_2 := by
  norm_num [radius66,Radius.Check,angle128_2,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius67 : Radius := ⟨(1087/1025),(46792671/100000000)⟩
theorem radius67_checked : radius67.Check angle128_3 := by
  norm_num [radius67,Radius.Check,angle128_3,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius68 : Radius := ⟨(17639/16409),(9194223/20000000)⟩
theorem radius68_checked : radius68.Check angle128_4 := by
  norm_num [radius68,Radius.Check,angle128_4,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius69 : Radius := ⟨(4471/4105),(902891/2000000)⟩
theorem radius69_checked : radius69.Check angle128_5 := by
  norm_num [radius69,Radius.Check,angle128_5,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius70 : Radius := ⟨(18127/16433),(5539301/12500000)⟩
theorem radius70_checked : radius70.Check angle128_6 := by
  norm_num [radius70,Radius.Check,angle128_6,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius71 : Radius := ⟨(287/257),(43482111/100000000)⟩
theorem radius71_checked : radius71.Check angle128_7 := by
  norm_num [radius71,Radius.Check,angle128_7,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius72 : Radius := ⟨(18607/16465),(10662267/25000000)⟩
theorem radius72_checked : radius72.Check angle128_8 := by
  norm_num [radius72,Radius.Check,angle128_8,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius73 : Radius := ⟨(4711/4121),(41816673/100000000)⟩
theorem radius73_checked : radius73.Check angle128_9 := by
  norm_num [radius73,Radius.Check,angle128_9,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius74 : Radius := ⟨(19079/16505),(409863/1000000)⟩
theorem radius74_checked : radius74.Check angle128_10 := by
  norm_num [radius74,Radius.Check,angle128_10,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius75 : Radius := ⟨(1207/1033),(20079651/50000000)⟩
theorem radius75_checked : radius75.Check angle128_11 := by
  norm_num [radius75,Radius.Check,angle128_11,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius76 : Radius := ⟨(19543/16553),(3933701/10000000)⟩
theorem radius76_checked : radius76.Check angle128_12 := by
  norm_num [radius76,Radius.Check,angle128_12,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius77 : Radius := ⟨(4943/4145),(1540829/4000000)⟩
theorem radius77_checked : radius77.Check angle128_13 := by
  norm_num [radius77,Radius.Check,angle128_13,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius78 : Radius := ⟨(19999/16609),(18855861/50000000)⟩
theorem radius78_checked : radius78.Check angle128_14 := by
  norm_num [radius78,Radius.Check,angle128_14,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius79 : Radius := ⟨(79/65),(18455621/50000000)⟩
theorem radius79_checked : radius79.Check angle128_15 := by
  norm_num [radius79,Radius.Check,angle128_15,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius80 : Radius := ⟨(20447/16673),(18060247/50000000)⟩
theorem radius80_checked : radius80.Check angle128_16 := by
  norm_num [radius80,Radius.Check,angle128_16,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius81 : Radius := ⟨(5167/4177),(706813/2000000)⟩
theorem radius81_checked : radius81.Check angle128_17 := by
  norm_num [radius81,Radius.Check,angle128_17,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius82 : Radius := ⟨(20887/16745),(8643211/25000000)⟩
theorem radius82_checked : radius82.Check angle128_18 := by
  norm_num [radius82,Radius.Check,angle128_18,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius83 : Radius := ⟨(1319/1049),(33818171/100000000)⟩
theorem radius83_checked : radius83.Check angle128_19 := by
  norm_num [radius83,Radius.Check,angle128_19,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius84 : Radius := ⟨(21319/16825),(6615537/20000000)⟩
theorem radius84_checked : radius84.Check angle128_20 := by
  norm_num [radius84,Radius.Check,angle128_20,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius85 : Radius := ⟨(5383/4217),(8088099/25000000)⟩
theorem radius85_checked : radius85.Check angle128_21 := by
  norm_num [radius85,Radius.Check,angle128_21,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius86 : Radius := ⟨(21743/16913),(3164327/10000000)⟩
theorem radius86_checked : radius86.Check angle128_22 := by
  norm_num [radius86,Radius.Check,angle128_22,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius87 : Radius := ⟨(343/265),(7737807/25000000)⟩
theorem radius87_checked : radius87.Check angle128_23 := by
  norm_num [radius87,Radius.Check,angle128_23,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius88 : Radius := ⟨(22159/17009),(15138571/50000000)⟩
theorem radius88_checked : radius88.Check angle128_24 := by
  norm_num [radius88,Radius.Check,angle128_24,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius89 : Radius := ⟨(5591/4265),(370273/1250000)⟩
theorem radius89_checked : radius89.Check angle128_25 := by
  norm_num [radius89,Radius.Check,angle128_25,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius90 : Radius := ⟨(22567/17113),(28986099/100000000)⟩
theorem radius90_checked : radius90.Check angle128_26 := by
  norm_num [radius90,Radius.Check,angle128_26,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius91 : Radius := ⟨(1423/1073),(3546331/12500000)⟩
theorem radius91_checked : radius91.Check angle128_27 := by
  norm_num [radius91,Radius.Check,angle128_27,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius92 : Radius := ⟨(22967/17225),(5555233/20000000)⟩
theorem radius92_checked : radius92.Check angle128_28 := by
  norm_num [radius92,Radius.Check,angle128_28,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius93 : Radius := ⟨(5791/4321),(27203279/100000000)⟩
theorem radius93_checked : radius93.Check angle128_29 := by
  norm_num [radius93,Radius.Check,angle128_29,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius94 : Radius := ⟨(23359/17345),(2665257/10000000)⟩
theorem radius94_checked : radius94.Check angle128_30 := by
  norm_num [radius94,Radius.Check,angle128_30,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius95 : Radius := ⟨(23/17),(26124567/100000000)⟩
theorem radius95_checked : radius95.Check angle128_31 := by
  norm_num [radius95,Radius.Check,angle128_31,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius96 : Radius := ⟨(23743/17473),(6404937/25000000)⟩
theorem radius96_checked : radius96.Check angle128_32 := by
  norm_num [radius96,Radius.Check,angle128_32,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius97 : Radius := ⟨(5983/4385),(12569271/50000000)⟩
theorem radius97_checked : radius97.Check angle128_33 := by
  norm_num [radius97,Radius.Check,angle128_33,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius98 : Radius := ⟨(24119/17609),(24681329/100000000)⟩
theorem radius98_checked : radius98.Check angle128_34 := by
  norm_num [radius98,Radius.Check,angle128_34,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius99 : Radius := ⟨(1519/1105),(12124219/50000000)⟩
theorem radius99_checked : radius99.Check angle128_35 := by
  norm_num [radius99,Radius.Check,angle128_35,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius100 : Radius := ⟨(24487/17753),(23840153/100000000)⟩
theorem radius100_checked : radius100.Check angle128_36 := by
  norm_num [radius100,Radius.Check,angle128_36,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius101 : Radius := ⟨(6167/4457),(23456707/100000000)⟩
theorem radius101_checked : radius101.Check angle128_37 := by
  norm_num [radius101,Radius.Check,angle128_37,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius102 : Radius := ⟨(24847/17905),(23098287/100000000)⟩
theorem radius102_checked : radius102.Check angle128_38 := by
  norm_num [radius102,Radius.Check,angle128_38,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius103 : Radius := ⟨(391/281),(4553007/20000000)⟩
theorem radius103_checked : radius103.Check angle128_39 := by
  norm_num [radius103,Radius.Check,angle128_39,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius104 : Radius := ⟨(25199/18065),(2807131/12500000)⟩
theorem radius104_checked : radius104.Check angle128_40 := by
  norm_num [radius104,Radius.Check,angle128_40,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius105 : Radius := ⟨(6343/4537),(2771797/12500000)⟩
theorem radius105_checked : radius105.Check angle128_41 := by
  norm_num [radius105,Radius.Check,angle128_41,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius106 : Radius := ⟨(25543/18233),(2191703/10000000)⟩
theorem radius106_checked : radius106.Check angle128_42 := by
  norm_num [radius106,Radius.Check,angle128_42,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius107 : Radius := ⟨(1607/1145),(21684979/100000000)⟩
theorem radius107_checked : radius107.Check angle128_43 := by
  norm_num [radius107,Radius.Check,angle128_43,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius108 : Radius := ⟨(25879/18409),(21478149/100000000)⟩
theorem radius108_checked : radius108.Check angle128_44 := by
  norm_num [radius108,Radius.Check,angle128_44,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius109 : Radius := ⟨(6511/4625),(2129643/10000000)⟩
theorem radius109_checked : radius109.Check angle128_45 := by
  norm_num [radius109,Radius.Check,angle128_45,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius110 : Radius := ⟨(26207/18593),(21139673/100000000)⟩
theorem radius110_checked : radius110.Check angle128_46 := by
  norm_num [radius110,Radius.Check,angle128_46,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius111 : Radius := ⟨(103/73),(21007693/100000000)⟩
theorem radius111_checked : radius111.Check angle128_47 := by
  norm_num [radius111,Radius.Check,angle128_47,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius112 : Radius := ⟨(26527/18785),(20900273/100000000)⟩
theorem radius112_checked : radius112.Check angle128_48 := by
  norm_num [radius112,Radius.Check,angle128_48,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius113 : Radius := ⟨(6671/4721),(20817159/100000000)⟩
theorem radius113_checked : radius113.Check angle128_49 := by
  norm_num [radius113,Radius.Check,angle128_49,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius114 : Radius := ⟨(26839/18985),(2075807/10000000)⟩
theorem radius114_checked : radius114.Check angle128_50 := by
  norm_num [radius114,Radius.Check,angle128_50,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius115 : Radius := ⟨(1687/1193),(20722691/100000000)⟩
theorem radius115_checked : radius115.Check angle128_51 := by
  norm_num [radius115,Radius.Check,angle128_51,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius116 : Radius := ⟨(27143/19193),(10355341/50000000)⟩
theorem radius116_checked : radius116.Check angle128_52 := by
  norm_num [radius116,Radius.Check,angle128_52,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius117 : Radius := ⟨(707107/500000),(10355319/50000000)⟩
theorem radius117_checked : radius117.Check angle128_53 := by
  norm_num [radius117,Radius.Check,angle128_53,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius118 : Radius := ⟨(6823/4825),(828867/4000000)⟩
theorem radius118_checked : radius118.Check angle128_54 := by
  norm_num [radius118,Radius.Check,angle128_54,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius119 : Radius := ⟨(27439/19409),(20755277/100000000)⟩
theorem radius119_checked : radius119.Check angle128_55 := by
  norm_num [radius119,Radius.Check,angle128_55,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius120 : Radius := ⟨(431/305),(325173/1562500)⟩
theorem radius120_checked : radius120.Check angle128_56 := by
  norm_num [radius120,Radius.Check,angle128_56,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius121 : Radius := ⟨(27727/19633),(10444311/50000000)⟩
theorem radius121_checked : radius121.Check angle128_57 := by
  norm_num [radius121,Radius.Check,angle128_57,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius122 : Radius := ⟨(6967/4937),(2098747/10000000)⟩
theorem radius122_checked : radius122.Check angle128_58 := by
  norm_num [radius122,Radius.Check,angle128_58,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius123 : Radius := ⟨(28007/19865),(10553569/50000000)⟩
theorem radius123_checked : radius123.Check angle128_59 := by
  norm_num [radius123,Radius.Check,angle128_59,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius124 : Radius := ⟨(1759/1249),(21247133/100000000)⟩
theorem radius124_checked : radius124.Check angle128_60 := by
  norm_num [radius124,Radius.Check,angle128_60,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius125 : Radius := ⟨(28279/20105),(10703473/50000000)⟩
theorem radius125_checked : radius125.Check angle128_61 := by
  norm_num [radius125,Radius.Check,angle128_61,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius126 : Radius := ⟨(7103/5057),(10793027/50000000)⟩
theorem radius126_checked : radius126.Check angle128_62 := by
  norm_num [radius126,Radius.Check,angle128_62,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius127 : Radius := ⟨(28543/20353),(21783921/100000000)⟩
theorem radius127_checked : radius127.Check angle128_63 := by
  norm_num [radius127,Radius.Check,angle128_63,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius128 : Radius := ⟨(7/5),(11/50)⟩
theorem radius128_checked : radius128.Check angle128_64 := by
  norm_num [radius128,Radius.Check,angle128_64,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius129 : Radius := ⟨(28799/20609),(11116867/50000000)⟩
theorem radius129_checked : radius129.Check angle128_65 := by
  norm_num [radius129,Radius.Check,angle128_65,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius130 : Radius := ⟨(7231/5185),(22484559/100000000)⟩
theorem radius130_checked : radius130.Check angle128_66 := by
  norm_num [radius130,Radius.Check,angle128_66,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius131 : Radius := ⟨(29047/20873),(22751903/100000000)⟩
theorem radius131_checked : radius131.Check angle128_67 := by
  norm_num [radius131,Radius.Check,angle128_67,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius132 : Radius := ⟨(1823/1313),(23035187/100000000)⟩
theorem radius132_checked : radius132.Check angle128_68 := by
  norm_num [radius132,Radius.Check,angle128_68,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius133 : Radius := ⟨(29287/21145),(2916729/12500000)⟩
theorem radius133_checked : radius133.Check angle128_69 := by
  norm_num [radius133,Radius.Check,angle128_69,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius134 : Radius := ⟨(7351/5321),(23647249/100000000)⟩
theorem radius134_checked : radius134.Check angle128_70 := by
  norm_num [radius134,Radius.Check,angle128_70,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius135 : Radius := ⟨(29519/21425),(23974853/100000000)⟩
theorem radius135_checked : radius135.Check angle128_71 := by
  norm_num [radius135,Radius.Check,angle128_71,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius136 : Radius := ⟨(463/337),(12158027/50000000)⟩
theorem radius136_checked : radius136.Check angle128_72 := by
  norm_num [radius136,Radius.Check,angle128_72,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius137 : Radius := ⟨(29743/21713),(3083783/12500000)⟩
theorem radius137_checked : radius137.Check angle128_73 := by
  norm_num [radius137,Radius.Check,angle128_73,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius138 : Radius := ⟨(7463/5465),(5007379/20000000)⟩
theorem radius138_checked : radius138.Check angle128_74 := by
  norm_num [radius138,Radius.Check,angle128_74,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius139 : Radius := ⟨(29959/22009),(25415361/100000000)⟩
theorem radius139_checked : radius139.Check angle128_75 := by
  norm_num [radius139,Radius.Check,angle128_75,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius140 : Radius := ⟨(1879/1385),(645127/2500000)⟩
theorem radius140_checked : radius140.Check angle128_76 := by
  norm_num [radius140,Radius.Check,angle128_76,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius141 : Radius := ⟨(30167/22313),(818921/3125000)⟩
theorem radius141_checked : radius141.Check angle128_77 := by
  norm_num [radius141,Radius.Check,angle128_77,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius142 : Radius := ⟨(7567/5617),(13307981/50000000)⟩
theorem radius142_checked : radius142.Check angle128_78 := by
  norm_num [radius142,Radius.Check,angle128_78,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius143 : Radius := ⟨(30367/22625),(27035981/100000000)⟩
theorem radius143_checked : radius143.Check angle128_79 := by
  norm_num [radius143,Radius.Check,angle128_79,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius144 : Radius := ⟨(119/89),(13732483/50000000)⟩
theorem radius144_checked : radius144.Check angle128_80 := by
  norm_num [radius144,Radius.Check,angle128_80,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius145 : Radius := ⟨(30559/22945),(697559/2500000)⟩
theorem radius145_checked : radius145.Check angle128_81 := by
  norm_num [radius145,Radius.Check,angle128_81,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius146 : Radius := ⟨(7663/5777),(7086903/25000000)⟩
theorem radius146_checked : radius146.Check angle128_82 := by
  norm_num [radius146,Radius.Check,angle128_82,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius147 : Radius := ⟨(30743/23273),(14400091/50000000)⟩
theorem radius147_checked : radius147.Check angle128_83 := by
  norm_num [radius147,Radius.Check,angle128_83,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius148 : Radius := ⟨(1927/1465),(29259537/100000000)⟩
theorem radius148_checked : radius148.Check angle128_84 := by
  norm_num [radius148,Radius.Check,angle128_84,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius149 : Radius := ⟨(30919/23609),(594503/2000000)⟩
theorem radius149_checked : radius149.Check angle128_85 := by
  norm_num [radius149,Radius.Check,angle128_85,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius150 : Radius := ⟨(7751/5945),(7549127/25000000)⟩
theorem radius150_checked : radius150.Check angle128_86 := by
  norm_num [radius150,Radius.Check,angle128_86,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius151 : Radius := ⟨(31087/23953),(1917069/6250000)⟩
theorem radius151_checked : radius151.Check angle128_87 := by
  norm_num [radius151,Radius.Check,angle128_87,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius152 : Radius := ⟨(487/377),(7788611/25000000)⟩
theorem radius152_checked : radius152.Check angle128_88 := by
  norm_num [radius152,Radius.Check,angle128_88,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius153 : Radius := ⟨(31247/24305),(31640041/100000000)⟩
theorem radius153_checked : radius153.Check angle128_89 := by
  norm_num [radius153,Radius.Check,angle128_89,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius154 : Radius := ⟨(7831/6121),(16064711/50000000)⟩
theorem radius154_checked : radius154.Check angle128_90 := by
  norm_num [radius154,Radius.Check,angle128_90,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius155 : Radius := ⟨(31399/24665),(8155531/25000000)⟩
theorem radius155_checked : radius155.Check angle128_91 := by
  norm_num [radius155,Radius.Check,angle128_91,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius156 : Radius := ⟨(1967/1553),(8279423/25000000)⟩
theorem radius156_checked : radius156.Check angle128_92 := by
  norm_num [radius156,Radius.Check,angle128_92,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius157 : Radius := ⟨(31543/25033),(4201961/12500000)⟩
theorem radius157_checked : radius157.Check angle128_93 := by
  norm_num [radius157,Radius.Check,angle128_93,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius158 : Radius := ⟨(7903/6305),(34115681/100000000)⟩
theorem radius158_checked : radius158.Check angle128_94 := by
  norm_num [radius158,Radius.Check,angle128_94,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius159 : Radius := ⟨(31679/25409),(17308627/50000000)⟩
theorem radius159_checked : radius159.Check angle128_95 := by
  norm_num [radius159,Radius.Check,angle128_95,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius160 : Radius := ⟨(31/25),(439/1250)⟩
theorem radius160_checked : radius160.Check angle128_96 := by
  norm_num [radius160,Radius.Check,angle128_96,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius161 : Radius := ⟨(31807/25793),(8905881/25000000)⟩
theorem radius161_checked : radius161.Check angle128_97 := by
  norm_num [radius161,Radius.Check,angle128_97,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius162 : Radius := ⟨(7967/6497),(18063723/50000000)⟩
theorem radius162_checked : radius162.Check angle128_98 := by
  norm_num [radius162,Radius.Check,angle128_98,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius163 : Radius := ⟨(31927/26185),(36631393/100000000)⟩
theorem radius163_checked : radius163.Check angle128_99 := by
  norm_num [radius163,Radius.Check,angle128_99,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius164 : Radius := ⟨(1999/1649),(37135007/100000000)⟩
theorem radius164_checked : radius164.Check angle128_100 := by
  norm_num [radius164,Radius.Check,angle128_100,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius165 : Radius := ⟨(32039/26585),(18818971/50000000)⟩
theorem radius165_checked : radius165.Check angle128_101 := by
  norm_num [radius165,Radius.Check,angle128_101,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius166 : Radius := ⟨(8023/6697),(19069931/50000000)⟩
theorem radius166_checked : radius166.Check angle128_102 := by
  norm_num [radius166,Radius.Check,angle128_102,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius167 : Radius := ⟨(32143/26993),(9660111/25000000)⟩
theorem radius167_checked : radius167.Check angle128_103 := by
  norm_num [radius167,Radius.Check,angle128_103,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius168 : Radius := ⟨(503/425),(39139377/100000000)⟩
theorem radius168_checked : radius168.Check angle128_104 := by
  norm_num [radius168,Radius.Check,angle128_104,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius169 : Radius := ⟨(32239/27409),(990909/2500000)⟩
theorem radius169_checked : radius169.Check angle128_105 := by
  norm_num [radius169,Radius.Check,angle128_105,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius170 : Radius := ⟨(8071/6905),(1254097/3125000)⟩
theorem radius170_checked : radius170.Check angle128_106 := by
  norm_num [radius170,Radius.Check,angle128_106,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius171 : Radius := ⟨(32327/27833),(20311667/50000000)⟩
theorem radius171_checked : radius171.Check angle128_107 := by
  norm_num [radius171,Radius.Check,angle128_107,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius172 : Radius := ⟨(2023/1753),(20556391/50000000)⟩
theorem radius172_checked : radius172.Check angle128_108 := by
  norm_num [radius172,Radius.Check,angle128_108,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius173 : Radius := ⟨(32407/28265),(20799597/50000000)⟩
theorem radius173_checked : radius173.Check angle128_109 := by
  norm_num [radius173,Radius.Check,angle128_109,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius174 : Radius := ⟨(8111/7121),(1683293/4000000)⟩
theorem radius174_checked : radius174.Check angle128_110 := by
  norm_num [radius174,Radius.Check,angle128_110,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius175 : Radius := ⟨(32479/28705),(42561943/100000000)⟩
theorem radius175_checked : radius175.Check angle128_111 := by
  norm_num [radius175,Radius.Check,angle128_111,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius176 : Radius := ⟨(127/113),(1721513/4000000)⟩
theorem radius176_checked : radius176.Check angle128_112 := by
  norm_num [radius176,Radius.Check,angle128_112,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius177 : Radius := ⟨(32543/29153),(43509759/100000000)⟩
theorem radius177_checked : radius177.Check angle128_113 := by
  norm_num [radius177,Radius.Check,angle128_113,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius178 : Radius := ⟨(8143/7345),(21988771/50000000)⟩
theorem radius178_checked : radius178.Check angle128_114 := by
  norm_num [radius178,Radius.Check,angle128_114,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius179 : Radius := ⟨(32599/29609),(44440983/100000000)⟩
theorem radius179_checked : radius179.Check angle128_115 := by
  norm_num [radius179,Radius.Check,angle128_115,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius180 : Radius := ⟨(2039/1865),(22449949/50000000)⟩
theorem radius180_checked : radius180.Check angle128_116 := by
  norm_num [radius180,Radius.Check,angle128_116,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius181 : Radius := ⟨(32647/30073),(11338529/25000000)⟩
theorem radius181_checked : radius181.Check angle128_117 := by
  norm_num [radius181,Radius.Check,angle128_117,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius182 : Radius := ⟨(8167/7577),(45803473/100000000)⟩
theorem radius182_checked : radius182.Check angle128_118 := by
  norm_num [radius182,Radius.Check,angle128_118,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius183 : Radius := ⟨(32687/30545),(23123907/50000000)⟩
theorem radius183_checked : radius183.Check angle128_119 := by
  norm_num [radius183,Radius.Check,angle128_119,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius184 : Radius := ⟨(511/481),(9337399/20000000)⟩
theorem radius184_checked : radius184.Check angle128_120 := by
  norm_num [radius184,Radius.Check,angle128_120,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius185 : Radius := ⟨(32719/31025),(47120879/100000000)⟩
theorem radius185_checked : radius185.Check angle128_121 := by
  norm_num [radius185,Radius.Check,angle128_121,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius186 : Radius := ⟨(8183/7817),(47549337/100000000)⟩
theorem radius186_checked : radius186.Check angle128_122 := by
  norm_num [radius186,Radius.Check,angle128_122,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius187 : Radius := ⟨(32743/31513),(47972251/100000000)⟩
theorem radius187_checked : radius187.Check angle128_123 := by
  norm_num [radius187,Radius.Check,angle128_123,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius188 : Radius := ⟨(2047/1985),(12097377/25000000)⟩
theorem radius188_checked : radius188.Check angle128_124 := by
  norm_num [radius188,Radius.Check,angle128_124,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius189 : Radius := ⟨(32759/32009),(12200251/25000000)⟩
theorem radius189_checked : radius189.Check angle128_125 := by
  norm_num [radius189,Radius.Check,angle128_125,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius190 : Radius := ⟨(8191/8065),(24603321/50000000)⟩
theorem radius190_checked : radius190.Check angle128_126 := by
  norm_num [radius190,Radius.Check,angle128_126,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]

def radius191 : Radius := ⟨(32767/32513),(9921267/20000000)⟩
theorem radius191_checked : radius191.Check angle128_127 := by
  norm_num [radius191,Radius.Check,angle128_127,supportQuadratic,
    Quadratic.CheckOn,Quadratic.evalRat]


end
end N12Compact.Preservation.Chords.Radii
