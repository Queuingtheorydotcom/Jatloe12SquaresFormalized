import Compact.Core.FiniteKernelDecision
import Compact.Completion.OtherCases.C705716.RowIdentity
import Compact.Completion.OtherCases.DomainCache
import Compact.Cases.C979.EntryQueries
import Compact.Cases.C701.EntryQueries
import Compact.Cases.C717.EntryQueries
import Compact.HistoricalOwnership.Queries000
import Compact.HistoricalOwnership.Queries001
import Compact.HistoricalOwnership.Queries013
import Compact.HistoricalOwnership.Queries025
import Compact.HistoricalOwnership.Queries043

/-! Compact genuine original entrances for C705 and C716. The component
domains reuse independently checked local refutations, with each authentic
F/G upper budget checked again. The three-marker owner has both compulsory
auxiliaries by exact convexity. Three sound refinement sweeps yield the
original unique full labels, without assuming an old catalogue exhaustive. -/

namespace N12Compact.Completion.OtherCases.C705716
open S12 S12Pilot
open N12Compact.Completion.OtherCases.DomainTransport
set_option Elab.async false
noncomputable section

private def combinedQueries12 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query438_certified,
   N12Compact.HistoricalOwnership.Queries.query8_certified,
   N12Compact.HistoricalOwnership.Queries.query1386_certified]

private def combinedQueries192 : List {q : LocalQuery // q.Check} :=
  [N12Compact.HistoricalOwnership.Queries.query821_certified,
   N12Compact.HistoricalOwnership.Queries.query61_certified,
   N12Compact.HistoricalOwnership.Queries.query1406_certified]

private def combinedQueries256 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 535),
   (certified_query% 546),
   (certified_query% 553),
   (certified_query% 560),
   (certified_query% 568),
   (certified_query% 517),
   (certified_query% 522),
   (certified_query% 527),
   (certified_query% 547),
   (certified_query% 554),
   (certified_query% 561),
   (certified_query% 569),
   (certified_query% 536),
   (certified_query% 548),
   (certified_query% 555),
   (certified_query% 562),
   (certified_query% 570),
   (certified_query% 537),
   (certified_query% 549),
   (certified_query% 556),
   (certified_query% 563),
   (certified_query% 571),
   (certified_query% 538),
   (certified_query% 539),
   (certified_query% 518),
   (certified_query% 523),
   (certified_query% 528),
   (certified_query% 533),
   (certified_query% 540),
   (certified_query% 550),
   (certified_query% 564),
   (certified_query% 541),
   (certified_query% 557),
   (certified_query% 519),
   (certified_query% 524),
   (certified_query% 529),
   (certified_query% 542),
   (certified_query% 551),
   (certified_query% 558),
   (certified_query% 565),
   (certified_query% 572),
   (certified_query% 520),
   (certified_query% 525),
   (certified_query% 530),
   (certified_query% 543),
   (certified_query% 552),
   (certified_query% 566),
   (certified_query% 521),
   (certified_query% 526),
   (certified_query% 531),
   (certified_query% 532),
   (certified_query% 534),
   (certified_query% 544),
   (certified_query% 545),
   (certified_query% 559),
   (certified_query% 567),
   (certified_query% 573)]

private def combinedQueries512 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 717),
   (certified_query% 670),
   (certified_query% 682),
   (certified_query% 690),
   (certified_query% 691),
   (certified_query% 698),
   (certified_query% 704),
   (certified_query% 705),
   (certified_query% 710),
   (certified_query% 715),
   (certified_query% 718),
   (certified_query% 671),
   (certified_query% 675),
   (certified_query% 683),
   (certified_query% 706),
   (certified_query% 711),
   (certified_query% 719),
   (certified_query% 676),
   (certified_query% 684),
   (certified_query% 692),
   (certified_query% 699),
   (certified_query% 720),
   (certified_query% 693),
   (certified_query% 721),
   (certified_query% 677),
   (certified_query% 685),
   (certified_query% 694),
   (certified_query% 700),
   (certified_query% 722),
   (certified_query% 723),
   (certified_query% 672),
   (certified_query% 678),
   (certified_query% 686),
   (certified_query% 695),
   (certified_query% 701),
   (certified_query% 707),
   (certified_query% 712),
   (certified_query% 724),
   (certified_query% 679),
   (certified_query% 687),
   (certified_query% 696),
   (certified_query% 702),
   (certified_query% 725),
   (certified_query% 673),
   (certified_query% 680),
   (certified_query% 688),
   (certified_query% 708),
   (certified_query% 713),
   (certified_query% 716),
   (certified_query% 726),
   (certified_query% 674),
   (certified_query% 681),
   (certified_query% 689),
   (certified_query% 697),
   (certified_query% 703),
   (certified_query% 709),
   (certified_query% 714)]

private def combinedQueries4096 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1090),
   (certified_query% 1092),
   (certified_query% 1096),
   (certified_query% 1104),
   (certified_query% 1088),
   (certified_query% 1093),
   (certified_query% 1097),
   (certified_query% 1101),
   (certified_query% 1098),
   (certified_query% 1091),
   (certified_query% 1094),
   (certified_query% 1099),
   (certified_query% 1102),
   (certified_query% 1105),
   (certified_query% 1089),
   (certified_query% 1095),
   (certified_query% 1100),
   (certified_query% 1103),
   (certified_query% 1106)]

private def combinedQueries8192 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1253),
   (certified_query% 1258),
   (certified_query% 1244),
   (certified_query% 1248),
   (certified_query% 1254),
   (certified_query% 1257),
   (certified_query% 1259),
   (certified_query% 1249),
   (certified_query% 1255),
   (certified_query% 1260),
   (certified_query% 1245),
   (certified_query% 1250),
   (certified_query% 1246),
   (certified_query% 1251),
   (certified_query% 1256),
   (certified_query% 1261),
   (certified_query% 1247),
   (certified_query% 1252),
   (certified_query% 1262)]

private def combinedQueries16384 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1393),
   (certified_query% 1403),
   (certified_query% 1405),
   (certified_query% 1408),
   (certified_query% 1394),
   (certified_query% 1400),
   (certified_query% 1404),
   (certified_query% 1406),
   (certified_query% 1409),
   (certified_query% 1395),
   (certified_query% 1398),
   (certified_query% 1401),
   (certified_query% 1410),
   (certified_query% 1396),
   (certified_query% 1399),
   (certified_query% 1402),
   (certified_query% 1407),
   (certified_query% 1411),
   (certified_query% 1397)]

private def combinedQueries32768 : List {q : LocalQuery // q.Check} :=
  [(certified_query% 1644),
   (certified_query% 1649),
   (certified_query% 1635),
   (certified_query% 1639),
   (certified_query% 1645),
   (certified_query% 1648),
   (certified_query% 1650),
   (certified_query% 1640),
   (certified_query% 1646),
   (certified_query% 1651),
   (certified_query% 1636),
   (certified_query% 1641),
   (certified_query% 1637),
   (certified_query% 1642),
   (certified_query% 1647),
   (certified_query% 1652),
   (certified_query% 1638),
   (certified_query% 1643),
   (certified_query% 1653)]

private def product1 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_0_0 2) (restrictUpper single979_0_1 2)
    (restrictUpper_checked single979_0_0 case979Family (family b) 0
      single979_0_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_0_1 case979Family (family b) 1
      single979_0_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain1 (b : Bool) : CertifiedDomain (family b) := product1 b

private def product2 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_1_0 2) (restrictUpper single979_1_1 2)
    (restrictUpper_checked single979_1_0 case979Family (family b) 0
      single979_1_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_1_1 case979Family (family b) 1
      single979_1_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain2 (b : Bool) : CertifiedDomain (family b) := product2 b

private def product12 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_2_0 1) (restrictUpper single979_2_1 1)
    (restrictUpper_checked single979_2_0 case979Family (family b) 0
      single979_2_0_checked 1 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_2_1 case979Family (family b) 1
      single979_2_1_checked 1 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain12 (b : Bool) : CertifiedDomain (family b) :=
  trim (product12 b) combinedQueries12 (by cases b <;> decide +kernel)

private def product16 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single701_3_0 2) (restrictUpper single717_3_1 2)
    (restrictUpper_checked single701_3_0 case701Family (family b) 0
      single701_3_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single717_3_1 case717Family (family b) 1
      single717_3_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain16 (b : Bool) : CertifiedDomain (family b) := product16 b

private def product32 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single701_4_0 2) (restrictUpper single717_4_1 2)
    (restrictUpper_checked single701_4_0 case701Family (family b) 0
      single701_4_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single717_4_1 case717Family (family b) 1
      single717_4_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain32 (b : Bool) : CertifiedDomain (family b) := product32 b

private def product192 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_4_0 1) (restrictUpper single979_4_1 1)
    (restrictUpper_checked single979_4_0 case979Family (family b) 0
      single979_4_0_checked 1 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_4_1 case979Family (family b) 1
      single979_4_1_checked 1 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain192 (b : Bool) : CertifiedDomain (family b) :=
  trim (product192 b) combinedQueries192 (by cases b <;> decide +kernel)

private def product256 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_5_0 2) (restrictUpper single979_5_1 2)
    (restrictUpper_checked single979_5_0 case979Family (family b) 0
      single979_5_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_5_1 case979Family (family b) 1
      single979_5_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain256 (b : Bool) : CertifiedDomain (family b) :=
  trim (product256 b) combinedQueries256 (by cases b <;> decide +kernel)

private def product512 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_6_0 2) (restrictUpper single979_6_1 2)
    (restrictUpper_checked single979_6_0 case979Family (family b) 0
      single979_6_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_6_1 case979Family (family b) 1
      single979_6_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain512 (b : Bool) : CertifiedDomain (family b) :=
  trim (product512 b) combinedQueries512 (by cases b <;> decide +kernel)

private def product4096 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_8_0 2) (restrictUpper single979_8_1 2)
    (restrictUpper_checked single979_8_0 case979Family (family b) 0
      single979_8_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_8_1 case979Family (family b) 1
      single979_8_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain4096 (b : Bool) : CertifiedDomain (family b) :=
  trim (product4096 b) combinedQueries4096 (by cases b <;> decide +kernel)

private def product8192 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_9_0 2) (restrictUpper single979_9_1 2)
    (restrictUpper_checked single979_9_0 case979Family (family b) 0
      single979_9_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_9_1 case979Family (family b) 1
      single979_9_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain8192 (b : Bool) : CertifiedDomain (family b) :=
  trim (product8192 b) combinedQueries8192 (by cases b <;> decide +kernel)

private def product16384 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_10_0 2) (restrictUpper single979_10_1 2)
    (restrictUpper_checked single979_10_0 case979Family (family b) 0
      single979_10_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_10_1 case979Family (family b) 1
      single979_10_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain16384 (b : Bool) : CertifiedDomain (family b) :=
  trim (product16384 b) combinedQueries16384 (by cases b <;> decide +kernel)

private def product32768 (b : Bool) : CertifiedDomain (family b) :=
  .ofDirectProduct _ (restrictUpper single979_11_0 2) (restrictUpper single979_11_1 2)
    (restrictUpper_checked single979_11_0 case979Family (family b) 0
      single979_11_0_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (restrictUpper_checked single979_11_1 case979Family (family b) 1
      single979_11_1_checked 2 (by decide +kernel) (by cases b <;> decide +kernel))
    (by decide +kernel)

private def domain32768 (b : Bool) : CertifiedDomain (family b) :=
  trim (product32768 b) combinedQueries32768 (by cases b <;> decide +kernel)

private def mergedFPoint (b : Bool) : TriangleCertificate :=
  if b then ⟨(47/20,47/20),(33/20,33/20),(33/20,47/20),(2,113/50),9/44,13/35⟩
  else ⟨(33/20,47/20),(47/20,33/20),(47/20,47/20),(2,113/50),9/44,13/35⟩

private def mergedGPoint (b : Bool) : TriangleCertificate :=
  if b then ⟨(47/20,47/20),(33/20,33/20),(33/20,47/20),(87/50,2),35/44,13/35⟩
  else ⟨(33/20,47/20),(47/20,33/20),(47/20,47/20),(113/50,2),35/44,13/35⟩

private def mergedF (b : Bool) :
    N12Compact.OwnerBudget.HalfDomain (family b) (ownerCode b 7) 0 :=
  hullSingleton (family b) (ownerCode b 7) 0 5 (by decide +kernel)
    (by cases b <;> decide +kernel) (mergedFPoint b)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

private def mergedG (b : Bool) :
    N12Compact.OwnerBudget.HalfDomain (family b) (ownerCode b 7) 1 :=
  hullSingleton (family b) (ownerCode b 7) 1 (if b then 3 else 6)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) (mergedGPoint b)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)

private def merged (b : Bool) : CertifiedDomain (family b) :=
  N12Compact.OwnerBudget.product (family b) (ownerCode b 7) (mergedF b) (mergedG b)

private def central (b : Bool) : CertifiedDomain (family b) :=
  if b then domain512 b else domain256 b


def initial0 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain1 b) 1 [{2,12},{2,10,12}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial1 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain2 b) 2 [{0,10},{0,2,10}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial2 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain12 b) 12 [∅,{18},{6},{6,15},{6,18},{8,18}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial3 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain16 b) 16 [{7,17},{7,17,19}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial4 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain32 b) 32 [{9,19},{7,9,19}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial5 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain192 b) 192 [∅,{11},{1,11},{3},{3,11},{3,14}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

private def initial6Allowed (b : Bool) : List (Finset Nat) :=
  if b then [{4,15},{4,12,15},{4,13,15},{4,16},{4,12,16},{4,13,16},{4,15,16},{4,18},{4,15,18},{4,16,18},{2,4,12,15},{4,5,16},{4,5,12,16},{4,5,13,16},{4,5,15,16},{4,5,16,18},{6,15},{6,16},{6,15,16},{6,18},{6,15,18},{6,16,18},{4,6,15},{4,6,12,15},{4,6,13,15},{4,6,16},{4,6,13,16},{4,6,15,16},{4,6,18},{4,6,15,18},{4,6,16,18},{8,15},{8,16},{8,15,16},{8,18},{8,15,18},{8,16,18},{4,8,15},{4,8,12,15},{4,8,13,15},{4,8,16},{4,8,12,16},{4,8,13,16},{4,8,15,16},{4,8,18},{4,8,15,18},{4,8,16,18},{5,8,16},{5,8,15,16},{5,8,16,18},{6,8,15},{6,8,16},{6,8,15,16},{6,8,18},{6,8,15,18},{6,8,16,18},{4,9,16},{4,9,12,16},{4,9,13,16},{4,9,15,16},{8,9,16},{8,9,15,16},{8,9,16,18},{8,9,16,19}] else [{0,10},{0,12},{0,10,12},{0,13},{0,10,13},{0,12,13},{0,1,13},{0,1,10,13},{0,1,11,13},{0,1,12,13},{2,10},{2,12},{2,10,12},{2,13},{2,10,13},{2,12,13},{0,2,10},{0,2,12},{0,2,10,12},{0,2,13},{0,2,10,13},{0,2,12,13},{4,10},{4,12},{4,10,12},{4,13},{4,10,13},{4,12,13},{4,12,15},{4,13,15},{4,12,16},{4,13,16},{0,4,10},{0,4,12},{0,4,10,12},{0,4,13},{0,4,10,13},{0,4,12,13},{0,4,12,15},{0,4,13,15},{0,4,12,16},{0,4,13,16},{1,4,13},{1,4,12,13},{1,4,13,15},{1,4,13,16},{2,4,10},{2,4,12},{2,4,10,12},{2,4,13},{2,4,10,13},{2,4,12,13},{2,4,12,15},{2,4,12,16},{2,4,13,16},{0,5,13},{0,5,10,13},{0,5,12,13},{4,5,13},{4,5,10,13},{4,5,12,13},{4,5,13,15},{4,5,13,16},{4,6,12,15}]

private def initial6_false_input : List (Finset Nat) := (product256 false).allowed

private def initial6_false_keep (owned : Finset Nat) : Bool :=
  decide (∀ query ∈ combinedQueries256, owned ≠ query.val.owned)

private def initial6_false_claim (index : Fin 121) : Prop :=
  let owned := initial6_false_input.getD index.val ∅
  initial6_false_keep owned = true → owned ∈ initial6Allowed false

private instance : DecidablePred initial6_false_claim := fun index => by
  unfold initial6_false_claim
  infer_instance

private theorem initial6_false_length : initial6_false_input.length = 121 := by decide +kernel

private theorem initial6_false_block0 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 0 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block1 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 1 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block2 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 2 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block3 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 3 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block4 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 4 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block5 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 5 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block6 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 6 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block7 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 7 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block8 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 8 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block9 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 9 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block10 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 10 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block11 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 11 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block12 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 12 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block13 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 13 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block14 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 14 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_block15 :
    N12Compact.FiniteCheckChunks.Check initial6_false_claim 15 := by
  intro offset valid
  dsimp only [initial6_false_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_false_checked : ∀ index : Fin 121, initial6_false_claim index :=
  N12Compact.FiniteCheckChunks.sound initial6_false_claim (count := 16) (by decide) (by
    intro block
    fin_cases block
    · exact initial6_false_block0
    · exact initial6_false_block1
    · exact initial6_false_block2
    · exact initial6_false_block3
    · exact initial6_false_block4
    · exact initial6_false_block5
    · exact initial6_false_block6
    · exact initial6_false_block7
    · exact initial6_false_block8
    · exact initial6_false_block9
    · exact initial6_false_block10
    · exact initial6_false_block11
    · exact initial6_false_block12
    · exact initial6_false_block13
    · exact initial6_false_block14
    · exact initial6_false_block15
  )

private theorem initial6_false_included :
    ∀ owned ∈ (domain256 false).allowed, owned ∈ initial6Allowed false := by
  change ∀ owned ∈ initial6_false_input.filter initial6_false_keep, owned ∈ initial6Allowed false
  exact filter_subset_of_indexed initial6_false_input (initial6Allowed false) initial6_false_keep ∅
    initial6_false_length initial6_false_checked

private def initial6_true_input : List (Finset Nat) := (product512 true).allowed

private def initial6_true_keep (owned : Finset Nat) : Bool :=
  decide (∀ query ∈ combinedQueries512, owned ≠ query.val.owned)

private def initial6_true_claim (index : Fin 121) : Prop :=
  let owned := initial6_true_input.getD index.val ∅
  initial6_true_keep owned = true → owned ∈ initial6Allowed true

private instance : DecidablePred initial6_true_claim := fun index => by
  unfold initial6_true_claim
  infer_instance

private theorem initial6_true_length : initial6_true_input.length = 121 := by decide +kernel

private theorem initial6_true_block0 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 0 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block1 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 1 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block2 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 2 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block3 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 3 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block4 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 4 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block5 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 5 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block6 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 6 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block7 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 7 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block8 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 8 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block9 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 9 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block10 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 10 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block11 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 11 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block12 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 12 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block13 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 13 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block14 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 14 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_block15 :
    N12Compact.FiniteCheckChunks.Check initial6_true_claim 15 := by
  intro offset valid
  dsimp only [initial6_true_claim]
  fin_cases offset
  all_goals try norm_num at valid
  all_goals try clear valid
  all_goals decide +kernel

private theorem initial6_true_checked : ∀ index : Fin 121, initial6_true_claim index :=
  N12Compact.FiniteCheckChunks.sound initial6_true_claim (count := 16) (by decide) (by
    intro block
    fin_cases block
    · exact initial6_true_block0
    · exact initial6_true_block1
    · exact initial6_true_block2
    · exact initial6_true_block3
    · exact initial6_true_block4
    · exact initial6_true_block5
    · exact initial6_true_block6
    · exact initial6_true_block7
    · exact initial6_true_block8
    · exact initial6_true_block9
    · exact initial6_true_block10
    · exact initial6_true_block11
    · exact initial6_true_block12
    · exact initial6_true_block13
    · exact initial6_true_block14
    · exact initial6_true_block15
  )

private theorem initial6_true_included :
    ∀ owned ∈ (domain512 true).allowed, owned ∈ initial6Allowed true := by
  change ∀ owned ∈ initial6_true_input.filter initial6_true_keep, owned ∈ initial6Allowed true
  exact filter_subset_of_indexed initial6_true_input (initial6Allowed true) initial6_true_keep ∅
    initial6_true_length initial6_true_checked

def initial6 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (central b) (if b then 512 else 256) (initial6Allowed b)
    (by cases b <;> decide +kernel) (by
      cases b
      · exact initial6_false_included
      · exact initial6_true_included),
    by cases b <;> decide +kernel⟩

def initial7 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (merged b) (if b then 3328 else 3584) (if b then [{5,13}] else [{5,16}])
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial8 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain4096 b) 4096 [{0,10},{0,10,13},{1,11},{1,11,13},{0,1,10},{0,1,11},{0,1,10,11},{0,1,10,13},{0,1,11,13},{0,2,10},{1,3,11}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial9 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain8192 b) 8192 [{2,12},{2,10,12},{2,12,15},{2,4,12},{2,4,12,15},{6,15},{6,12,15},{6,15,18},{2,6,12,15},{4,6,15},{4,6,12,15}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial10 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain16384 b) 16384 [{8,18},{8,16,18},{6,8,18},{9,19},{9,16,19},{7,9,19},{8,9,18},{8,9,16,18},{8,9,19},{8,9,16,19},{8,9,18,19}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initial11 (b : Bool) : NamedDomain (family b) :=
  ⟨cache (domain32768 b) 32768 [{3,14},{3,11,14},{3,14,17},{3,5,14},{3,5,14,17},{7,17},{7,14,17},{7,17,19},{3,7,14,17},{5,7,17},{5,7,14,17}]
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel),
    by cases b <;> decide +kernel⟩

def initialNamed (b : Bool) : List (NamedDomain (family b)) :=
  [initial0 b,initial1 b,initial2 b,initial3 b,initial4 b,initial5 b,initial6 b,initial7 b,initial8 b,initial9 b,initial10 b,initial11 b]

end
end N12Compact.Completion.OtherCases.C705716
