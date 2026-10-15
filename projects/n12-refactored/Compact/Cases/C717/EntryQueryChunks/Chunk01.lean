import Compact.Core.FiniteKernelDecision
import Compact.Bridge.SharedLocalQueries
import Compact.Cases.C717.EntryQueryBase
import Compact.HistoricalOwnership.Queries004
import Compact.HistoricalOwnership.Queries005
import Compact.HistoricalOwnership.Queries006
import Compact.HistoricalOwnership.Queries007
import Compact.HistoricalOwnership.Queries008
import Compact.HistoricalOwnership.Queries009
import Compact.HistoricalOwnership.Queries010
import Compact.HistoricalOwnership.Queries011
import Compact.HistoricalOwnership.Queries012
import Compact.HistoricalOwnership.Queries013
import Compact.HistoricalOwnership.Queries014
import Compact.HistoricalOwnership.Queries015
import Compact.HistoricalOwnership.Queries016
import Compact.HistoricalOwnership.Queries017
import Compact.HistoricalOwnership.Queries018
import Compact.HistoricalOwnership.Queries019
import Compact.HistoricalOwnership.Queries020
import Compact.HistoricalOwnership.Queries021
import Compact.HistoricalOwnership.Queries022
import Compact.HistoricalOwnership.Queries023
import Compact.HistoricalOwnership.Queries024
import Compact.HistoricalOwnership.Queries025
import Compact.HistoricalOwnership.Queries026
import Compact.HistoricalOwnership.Queries027
import Compact.HistoricalOwnership.Queries028
import Compact.HistoricalOwnership.Queries029
import Compact.HistoricalOwnership.Queries030
import Compact.HistoricalOwnership.Queries031
import Compact.HistoricalOwnership.Queries032
import Compact.HistoricalOwnership.Queries033
import Compact.HistoricalOwnership.Queries034
import Compact.HistoricalOwnership.Queries035
import Compact.HistoricalOwnership.Queries036
import Compact.HistoricalOwnership.Queries037
import Compact.HistoricalOwnership.Queries038
import Compact.HistoricalOwnership.Queries039
import Compact.HistoricalOwnership.Queries040
import Compact.HistoricalOwnership.Queries041
import Compact.HistoricalOwnership.Queries042
import Compact.HistoricalOwnership.Queries043
import Compact.Bridge.SmallOwnerDomainThree

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single717_6_0 : DirectSingleDomain := ⟨768,1,1,[{4}],[(certified_query% 744),(certified_query% 745),(certified_query% 746),(certified_query% 747),(certified_query% 748),(certified_query% 749),(certified_query% 750),(certified_query% 751),(certified_query% 752)]⟩
private def single717_6_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(768,0,{0}),(768,0,{1}),(768,0,{2}),(768,0,{3}),(768,0,{5}),(768,0,{6}),(768,0,{7}),(768,0,{8}),(768,0,{9})]
theorem single717_6_0_checked : single717_6_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_6_0 case717Family 0
    single717_6_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_6_1 : DirectSingleDomain := ⟨768,0,2,[∅,{0},{2},{0,2},{3},{0,3},{2,3},{5},{0,5},{2,5},{3,5},{6},{0,6},{2,6},{3,6},{5,6},{8},{0,8},{2,8},{3,8},{5,8},{6,8}],[N12Compact.HistoricalOwnership.Queries.query823_certified,N12Compact.HistoricalOwnership.Queries.query824_certified,N12Compact.HistoricalOwnership.Queries.query825_certified,N12Compact.HistoricalOwnership.Queries.query826_certified,N12Compact.HistoricalOwnership.Queries.query827_certified,N12Compact.HistoricalOwnership.Queries.query828_certified,N12Compact.HistoricalOwnership.Queries.query829_certified,N12Compact.HistoricalOwnership.Queries.query830_certified,N12Compact.HistoricalOwnership.Queries.query831_certified,N12Compact.HistoricalOwnership.Queries.query832_certified,N12Compact.HistoricalOwnership.Queries.query833_certified,N12Compact.HistoricalOwnership.Queries.query834_certified,N12Compact.HistoricalOwnership.Queries.query835_certified,N12Compact.HistoricalOwnership.Queries.query836_certified,N12Compact.HistoricalOwnership.Queries.query837_certified,N12Compact.HistoricalOwnership.Queries.query838_certified,N12Compact.HistoricalOwnership.Queries.query839_certified,N12Compact.HistoricalOwnership.Queries.query840_certified,N12Compact.HistoricalOwnership.Queries.query841_certified,N12Compact.HistoricalOwnership.Queries.query842_certified,N12Compact.HistoricalOwnership.Queries.query843_certified,N12Compact.HistoricalOwnership.Queries.query844_certified,N12Compact.HistoricalOwnership.Queries.query845_certified,N12Compact.HistoricalOwnership.Queries.query846_certified,N12Compact.HistoricalOwnership.Queries.query847_certified,N12Compact.HistoricalOwnership.Queries.query848_certified,N12Compact.HistoricalOwnership.Queries.query849_certified,N12Compact.HistoricalOwnership.Queries.query850_certified,N12Compact.HistoricalOwnership.Queries.query851_certified,N12Compact.HistoricalOwnership.Queries.query852_certified,N12Compact.HistoricalOwnership.Queries.query853_certified,N12Compact.HistoricalOwnership.Queries.query854_certified,N12Compact.HistoricalOwnership.Queries.query855_certified,N12Compact.HistoricalOwnership.Queries.query856_certified]⟩
private def single717_6_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(768,1,{1}),(768,1,{0,1}),(768,1,{1,2}),(768,1,{1,3}),(768,1,{4}),(768,1,{0,4}),(768,1,{1,4}),(768,1,{2,4}),(768,1,{3,4}),(768,1,{1,5}),(768,1,{4,5}),(768,1,{1,6}),(768,1,{4,6}),(768,1,{7}),(768,1,{0,7}),(768,1,{1,7}),(768,1,{2,7}),(768,1,{3,7}),(768,1,{4,7}),(768,1,{5,7}),(768,1,{6,7}),(768,1,{1,8}),(768,1,{4,8}),(768,1,{7,8}),(768,1,{9}),(768,1,{0,9}),(768,1,{1,9}),(768,1,{2,9}),(768,1,{3,9}),(768,1,{4,9}),(768,1,{5,9}),(768,1,{6,9}),(768,1,{7,9}),(768,1,{8,9})]
theorem single717_6_1_checked : single717_6_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomain.checked single717_6_1 case717Family 1
    single717_6_1Signatures (by rfl) (by decide) (by decide +kernel)

def single717_7_0 : DirectSingleDomain := ⟨3072,1,1,[{5}],[N12Compact.HistoricalOwnership.Queries.query857_certified,N12Compact.HistoricalOwnership.Queries.query858_certified,N12Compact.HistoricalOwnership.Queries.query859_certified,N12Compact.HistoricalOwnership.Queries.query860_certified,N12Compact.HistoricalOwnership.Queries.query861_certified,N12Compact.HistoricalOwnership.Queries.query862_certified,N12Compact.HistoricalOwnership.Queries.query863_certified,N12Compact.HistoricalOwnership.Queries.query864_certified,N12Compact.HistoricalOwnership.Queries.query865_certified]⟩
private def single717_7_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(3072,0,{0}),(3072,0,{1}),(3072,0,{2}),(3072,0,{3}),(3072,0,{4}),(3072,0,{6}),(3072,0,{7}),(3072,0,{8}),(3072,0,{9})]
theorem single717_7_0_checked : single717_7_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_7_0 case717Family 0
    single717_7_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_7_1 : DirectSingleDomain := ⟨3072,0,2,[∅,{1},{3},{1,3},{4},{1,4},{3,4},{6},{1,6},{3,6},{4,6},{7},{1,7},{3,7},{4,7},{6,7},{9},{1,9},{3,9},{4,9},{6,9},{7,9}],[N12Compact.HistoricalOwnership.Queries.query866_certified,N12Compact.HistoricalOwnership.Queries.query867_certified,N12Compact.HistoricalOwnership.Queries.query868_certified,N12Compact.HistoricalOwnership.Queries.query869_certified,N12Compact.HistoricalOwnership.Queries.query870_certified,N12Compact.HistoricalOwnership.Queries.query871_certified,N12Compact.HistoricalOwnership.Queries.query872_certified,N12Compact.HistoricalOwnership.Queries.query873_certified,N12Compact.HistoricalOwnership.Queries.query874_certified,N12Compact.HistoricalOwnership.Queries.query875_certified,N12Compact.HistoricalOwnership.Queries.query876_certified,N12Compact.HistoricalOwnership.Queries.query877_certified,N12Compact.HistoricalOwnership.Queries.query878_certified,N12Compact.HistoricalOwnership.Queries.query879_certified,N12Compact.HistoricalOwnership.Queries.query880_certified,N12Compact.HistoricalOwnership.Queries.query881_certified,N12Compact.HistoricalOwnership.Queries.query882_certified,N12Compact.HistoricalOwnership.Queries.query883_certified,N12Compact.HistoricalOwnership.Queries.query884_certified,N12Compact.HistoricalOwnership.Queries.query885_certified,N12Compact.HistoricalOwnership.Queries.query886_certified,N12Compact.HistoricalOwnership.Queries.query887_certified,N12Compact.HistoricalOwnership.Queries.query888_certified,N12Compact.HistoricalOwnership.Queries.query889_certified,N12Compact.HistoricalOwnership.Queries.query890_certified,N12Compact.HistoricalOwnership.Queries.query891_certified,N12Compact.HistoricalOwnership.Queries.query892_certified,N12Compact.HistoricalOwnership.Queries.query893_certified,N12Compact.HistoricalOwnership.Queries.query894_certified,N12Compact.HistoricalOwnership.Queries.query895_certified,N12Compact.HistoricalOwnership.Queries.query896_certified,N12Compact.HistoricalOwnership.Queries.query897_certified,N12Compact.HistoricalOwnership.Queries.query898_certified,N12Compact.HistoricalOwnership.Queries.query899_certified]⟩
private def single717_7_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(3072,1,{0}),(3072,1,{0,1}),(3072,1,{2}),(3072,1,{0,2}),(3072,1,{1,2}),(3072,1,{0,3}),(3072,1,{2,3}),(3072,1,{0,4}),(3072,1,{2,4}),(3072,1,{5}),(3072,1,{0,5}),(3072,1,{1,5}),(3072,1,{2,5}),(3072,1,{3,5}),(3072,1,{4,5}),(3072,1,{0,6}),(3072,1,{2,6}),(3072,1,{5,6}),(3072,1,{0,7}),(3072,1,{2,7}),(3072,1,{5,7}),(3072,1,{8}),(3072,1,{0,8}),(3072,1,{1,8}),(3072,1,{2,8}),(3072,1,{3,8}),(3072,1,{4,8}),(3072,1,{5,8}),(3072,1,{6,8}),(3072,1,{7,8}),(3072,1,{0,9}),(3072,1,{2,9}),(3072,1,{5,9}),(3072,1,{8,9})]
theorem single717_7_1_checked : single717_7_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomain.checked single717_7_1 case717Family 1
    single717_7_1Signatures (by rfl) (by decide) (by decide +kernel)

def single717_8_0 : DirectSingleDomain := ⟨4096,1,1,[{0},{1}],[(certified_query% 989),(certified_query% 991),(certified_query% 994),(certified_query% 999),(certified_query% 1005),(certified_query% 1012),(certified_query% 1020),(certified_query% 1029)]⟩
private def single717_8_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(4096,0,{2}),(4096,0,{3}),(4096,0,{4}),(4096,0,{5}),(4096,0,{6}),(4096,0,{7}),(4096,0,{8}),(4096,0,{9})]
theorem single717_8_0_checked : single717_8_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_8_0 case717Family 0
    single717_8_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_8_1 : DirectSingleDomain := ⟨4096,1,3,[{0},{1},{0,1},{3},{0,3},{1,3},{0,1,3}],[(certified_query% 1039),(certified_query% 1040),(certified_query% 1041),N12Compact.HistoricalOwnership.Queries.query900_certified,(certified_query% 1042),N12Compact.HistoricalOwnership.Queries.query901_certified,N12Compact.HistoricalOwnership.Queries.query902_certified,(certified_query% 1043),(certified_query% 1044),(certified_query% 1045),N12Compact.HistoricalOwnership.Queries.query903_certified,(certified_query% 1046),N12Compact.HistoricalOwnership.Queries.query904_certified,N12Compact.HistoricalOwnership.Queries.query905_certified,(certified_query% 1047),N12Compact.HistoricalOwnership.Queries.query906_certified,N12Compact.HistoricalOwnership.Queries.query907_certified,N12Compact.HistoricalOwnership.Queries.query908_certified,(certified_query% 1048),(certified_query% 1049),(certified_query% 1050),N12Compact.HistoricalOwnership.Queries.query909_certified,(certified_query% 1051),N12Compact.HistoricalOwnership.Queries.query910_certified,N12Compact.HistoricalOwnership.Queries.query911_certified,(certified_query% 1052),N12Compact.HistoricalOwnership.Queries.query912_certified,N12Compact.HistoricalOwnership.Queries.query913_certified,N12Compact.HistoricalOwnership.Queries.query914_certified,(certified_query% 1053),N12Compact.HistoricalOwnership.Queries.query915_certified,N12Compact.HistoricalOwnership.Queries.query916_certified,N12Compact.HistoricalOwnership.Queries.query917_certified,N12Compact.HistoricalOwnership.Queries.query918_certified,(certified_query% 1054),(certified_query% 1055),(certified_query% 1056),N12Compact.HistoricalOwnership.Queries.query919_certified,(certified_query% 1057),N12Compact.HistoricalOwnership.Queries.query920_certified,N12Compact.HistoricalOwnership.Queries.query921_certified,(certified_query% 1058),N12Compact.HistoricalOwnership.Queries.query922_certified,N12Compact.HistoricalOwnership.Queries.query923_certified,N12Compact.HistoricalOwnership.Queries.query924_certified,(certified_query% 1059),N12Compact.HistoricalOwnership.Queries.query925_certified,N12Compact.HistoricalOwnership.Queries.query926_certified,N12Compact.HistoricalOwnership.Queries.query927_certified,N12Compact.HistoricalOwnership.Queries.query928_certified,(certified_query% 1060),N12Compact.HistoricalOwnership.Queries.query929_certified,N12Compact.HistoricalOwnership.Queries.query930_certified,N12Compact.HistoricalOwnership.Queries.query931_certified,N12Compact.HistoricalOwnership.Queries.query932_certified,N12Compact.HistoricalOwnership.Queries.query933_certified,(certified_query% 1061),(certified_query% 1062),(certified_query% 1063),N12Compact.HistoricalOwnership.Queries.query934_certified,(certified_query% 1064),N12Compact.HistoricalOwnership.Queries.query935_certified,N12Compact.HistoricalOwnership.Queries.query936_certified,(certified_query% 1065),N12Compact.HistoricalOwnership.Queries.query937_certified,N12Compact.HistoricalOwnership.Queries.query938_certified,N12Compact.HistoricalOwnership.Queries.query939_certified,(certified_query% 1066),N12Compact.HistoricalOwnership.Queries.query940_certified,N12Compact.HistoricalOwnership.Queries.query941_certified,N12Compact.HistoricalOwnership.Queries.query942_certified,N12Compact.HistoricalOwnership.Queries.query943_certified,(certified_query% 1067),N12Compact.HistoricalOwnership.Queries.query944_certified,N12Compact.HistoricalOwnership.Queries.query945_certified,N12Compact.HistoricalOwnership.Queries.query946_certified,N12Compact.HistoricalOwnership.Queries.query947_certified,N12Compact.HistoricalOwnership.Queries.query948_certified,(certified_query% 1068),N12Compact.HistoricalOwnership.Queries.query949_certified,N12Compact.HistoricalOwnership.Queries.query950_certified,N12Compact.HistoricalOwnership.Queries.query951_certified,N12Compact.HistoricalOwnership.Queries.query952_certified,N12Compact.HistoricalOwnership.Queries.query953_certified,N12Compact.HistoricalOwnership.Queries.query954_certified,(certified_query% 1069),(certified_query% 1070),(certified_query% 1071),N12Compact.HistoricalOwnership.Queries.query955_certified,(certified_query% 1072),N12Compact.HistoricalOwnership.Queries.query956_certified,N12Compact.HistoricalOwnership.Queries.query957_certified,(certified_query% 1073),N12Compact.HistoricalOwnership.Queries.query958_certified,N12Compact.HistoricalOwnership.Queries.query959_certified,N12Compact.HistoricalOwnership.Queries.query960_certified,(certified_query% 1074),N12Compact.HistoricalOwnership.Queries.query961_certified,N12Compact.HistoricalOwnership.Queries.query962_certified,N12Compact.HistoricalOwnership.Queries.query963_certified,N12Compact.HistoricalOwnership.Queries.query964_certified,(certified_query% 1075),N12Compact.HistoricalOwnership.Queries.query965_certified,N12Compact.HistoricalOwnership.Queries.query966_certified,N12Compact.HistoricalOwnership.Queries.query967_certified,N12Compact.HistoricalOwnership.Queries.query968_certified,N12Compact.HistoricalOwnership.Queries.query969_certified,(certified_query% 1076),N12Compact.HistoricalOwnership.Queries.query970_certified,N12Compact.HistoricalOwnership.Queries.query971_certified,N12Compact.HistoricalOwnership.Queries.query972_certified,N12Compact.HistoricalOwnership.Queries.query973_certified,N12Compact.HistoricalOwnership.Queries.query974_certified,N12Compact.HistoricalOwnership.Queries.query975_certified,(certified_query% 1077),N12Compact.HistoricalOwnership.Queries.query976_certified,N12Compact.HistoricalOwnership.Queries.query977_certified,N12Compact.HistoricalOwnership.Queries.query978_certified,N12Compact.HistoricalOwnership.Queries.query979_certified,N12Compact.HistoricalOwnership.Queries.query980_certified,N12Compact.HistoricalOwnership.Queries.query981_certified,N12Compact.HistoricalOwnership.Queries.query982_certified,(certified_query% 1078),(certified_query% 1079),(certified_query% 1080),N12Compact.HistoricalOwnership.Queries.query983_certified,(certified_query% 1081),N12Compact.HistoricalOwnership.Queries.query984_certified,N12Compact.HistoricalOwnership.Queries.query985_certified,(certified_query% 1082),N12Compact.HistoricalOwnership.Queries.query986_certified,N12Compact.HistoricalOwnership.Queries.query987_certified,N12Compact.HistoricalOwnership.Queries.query988_certified,(certified_query% 1083),N12Compact.HistoricalOwnership.Queries.query989_certified,N12Compact.HistoricalOwnership.Queries.query990_certified,N12Compact.HistoricalOwnership.Queries.query991_certified,N12Compact.HistoricalOwnership.Queries.query992_certified,(certified_query% 1084),N12Compact.HistoricalOwnership.Queries.query993_certified,N12Compact.HistoricalOwnership.Queries.query994_certified,N12Compact.HistoricalOwnership.Queries.query995_certified,N12Compact.HistoricalOwnership.Queries.query996_certified,N12Compact.HistoricalOwnership.Queries.query997_certified,(certified_query% 1085),N12Compact.HistoricalOwnership.Queries.query998_certified,N12Compact.HistoricalOwnership.Queries.query999_certified,N12Compact.HistoricalOwnership.Queries.query1000_certified,N12Compact.HistoricalOwnership.Queries.query1001_certified,N12Compact.HistoricalOwnership.Queries.query1002_certified,N12Compact.HistoricalOwnership.Queries.query1003_certified,(certified_query% 1086),N12Compact.HistoricalOwnership.Queries.query1004_certified,N12Compact.HistoricalOwnership.Queries.query1005_certified,N12Compact.HistoricalOwnership.Queries.query1006_certified,N12Compact.HistoricalOwnership.Queries.query1007_certified,N12Compact.HistoricalOwnership.Queries.query1008_certified,N12Compact.HistoricalOwnership.Queries.query1009_certified,N12Compact.HistoricalOwnership.Queries.query1010_certified,(certified_query% 1087),N12Compact.HistoricalOwnership.Queries.query1011_certified,N12Compact.HistoricalOwnership.Queries.query1012_certified,N12Compact.HistoricalOwnership.Queries.query1013_certified,N12Compact.HistoricalOwnership.Queries.query1014_certified,N12Compact.HistoricalOwnership.Queries.query1015_certified,N12Compact.HistoricalOwnership.Queries.query1016_certified,N12Compact.HistoricalOwnership.Queries.query1017_certified,N12Compact.HistoricalOwnership.Queries.query1018_certified]⟩
private def single717_8_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(4096,1,{2}),(4096,1,{0,2}),(4096,1,{1,2}),(4096,1,{0,1,2}),(4096,1,{2,3}),(4096,1,{0,2,3}),(4096,1,{1,2,3}),(4096,1,{4}),(4096,1,{0,4}),(4096,1,{1,4}),(4096,1,{0,1,4}),(4096,1,{2,4}),(4096,1,{0,2,4}),(4096,1,{1,2,4}),(4096,1,{3,4}),(4096,1,{0,3,4}),(4096,1,{1,3,4}),(4096,1,{2,3,4}),(4096,1,{5}),(4096,1,{0,5}),(4096,1,{1,5}),(4096,1,{0,1,5}),(4096,1,{2,5}),(4096,1,{0,2,5}),(4096,1,{1,2,5}),(4096,1,{3,5}),(4096,1,{0,3,5}),(4096,1,{1,3,5}),(4096,1,{2,3,5}),(4096,1,{4,5}),(4096,1,{0,4,5}),(4096,1,{1,4,5}),(4096,1,{2,4,5}),(4096,1,{3,4,5}),(4096,1,{6}),(4096,1,{0,6}),(4096,1,{1,6}),(4096,1,{0,1,6}),(4096,1,{2,6}),(4096,1,{0,2,6}),(4096,1,{1,2,6}),(4096,1,{3,6}),(4096,1,{0,3,6}),(4096,1,{1,3,6}),(4096,1,{2,3,6}),(4096,1,{4,6}),(4096,1,{0,4,6}),(4096,1,{1,4,6}),(4096,1,{2,4,6}),(4096,1,{3,4,6}),(4096,1,{5,6}),(4096,1,{0,5,6}),(4096,1,{1,5,6}),(4096,1,{2,5,6}),(4096,1,{3,5,6}),(4096,1,{4,5,6}),(4096,1,{7}),(4096,1,{0,7}),(4096,1,{1,7}),(4096,1,{0,1,7}),(4096,1,{2,7}),(4096,1,{0,2,7}),(4096,1,{1,2,7}),(4096,1,{3,7}),(4096,1,{0,3,7}),(4096,1,{1,3,7}),(4096,1,{2,3,7}),(4096,1,{4,7}),(4096,1,{0,4,7}),(4096,1,{1,4,7}),(4096,1,{2,4,7}),(4096,1,{3,4,7}),(4096,1,{5,7}),(4096,1,{0,5,7}),(4096,1,{1,5,7}),(4096,1,{2,5,7}),(4096,1,{3,5,7}),(4096,1,{4,5,7}),(4096,1,{6,7}),(4096,1,{0,6,7}),(4096,1,{1,6,7}),(4096,1,{2,6,7}),(4096,1,{3,6,7}),(4096,1,{4,6,7}),(4096,1,{5,6,7}),(4096,1,{8}),(4096,1,{0,8}),(4096,1,{1,8}),(4096,1,{0,1,8}),(4096,1,{2,8}),(4096,1,{0,2,8}),(4096,1,{1,2,8}),(4096,1,{3,8}),(4096,1,{0,3,8}),(4096,1,{1,3,8}),(4096,1,{2,3,8}),(4096,1,{4,8}),(4096,1,{0,4,8}),(4096,1,{1,4,8}),(4096,1,{2,4,8}),(4096,1,{3,4,8}),(4096,1,{5,8}),(4096,1,{0,5,8}),(4096,1,{1,5,8}),(4096,1,{2,5,8}),(4096,1,{3,5,8}),(4096,1,{4,5,8}),(4096,1,{6,8}),(4096,1,{0,6,8}),(4096,1,{1,6,8}),(4096,1,{2,6,8}),(4096,1,{3,6,8}),(4096,1,{4,6,8}),(4096,1,{5,6,8}),(4096,1,{7,8}),(4096,1,{0,7,8}),(4096,1,{1,7,8}),(4096,1,{2,7,8}),(4096,1,{3,7,8}),(4096,1,{4,7,8}),(4096,1,{5,7,8}),(4096,1,{6,7,8}),(4096,1,{9}),(4096,1,{0,9}),(4096,1,{1,9}),(4096,1,{0,1,9}),(4096,1,{2,9}),(4096,1,{0,2,9}),(4096,1,{1,2,9}),(4096,1,{3,9}),(4096,1,{0,3,9}),(4096,1,{1,3,9}),(4096,1,{2,3,9}),(4096,1,{4,9}),(4096,1,{0,4,9}),(4096,1,{1,4,9}),(4096,1,{2,4,9}),(4096,1,{3,4,9}),(4096,1,{5,9}),(4096,1,{0,5,9}),(4096,1,{1,5,9}),(4096,1,{2,5,9}),(4096,1,{3,5,9}),(4096,1,{4,5,9}),(4096,1,{6,9}),(4096,1,{0,6,9}),(4096,1,{1,6,9}),(4096,1,{2,6,9}),(4096,1,{3,6,9}),(4096,1,{4,6,9}),(4096,1,{5,6,9}),(4096,1,{7,9}),(4096,1,{0,7,9}),(4096,1,{1,7,9}),(4096,1,{2,7,9}),(4096,1,{3,7,9}),(4096,1,{4,7,9}),(4096,1,{5,7,9}),(4096,1,{6,7,9}),(4096,1,{8,9}),(4096,1,{0,8,9}),(4096,1,{1,8,9}),(4096,1,{2,8,9}),(4096,1,{3,8,9}),(4096,1,{4,8,9}),(4096,1,{5,8,9}),(4096,1,{6,8,9}),(4096,1,{7,8,9})]
private theorem single717_8_1_queries_exact :
    single717_8_1Signatures = single717_8_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_8_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{0},{1},{0,1},{3},{0,3},{1,3},{0,1,3}] : List (Finset Nat)) ∨ (4096,1,owned) ∈ single717_8_1Signatures

private instance : DecidablePred single717_8_1_owned_claim := fun index => by
  unfold single717_8_1_owned_claim
  infer_instance

private theorem single717_8_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_8_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_8_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_8_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_8_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_8_1 case717Family 1 single717_8_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨4096,1,3,[{0},{1},{0,1},{3},{0,3},{1,3},{0,1,3}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_8_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_8_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_8_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_8_1_owned_block0
      · exact single717_8_1_owned_block1
      · exact single717_8_1_owned_block2
      · exact single717_8_1_owned_block3
      · exact single717_8_1_owned_block4
      · exact single717_8_1_owned_block5
      · exact single717_8_1_owned_block6
      · exact single717_8_1_owned_block7
      · exact single717_8_1_owned_block8
      · exact single717_8_1_owned_block9
      · exact single717_8_1_owned_block10
      · exact single717_8_1_owned_block11
      · exact single717_8_1_owned_block12
      · exact single717_8_1_owned_block13
      · exact single717_8_1_owned_block14
      · exact single717_8_1_owned_block15
      · exact single717_8_1_owned_block16
      · exact single717_8_1_owned_block17
      · exact single717_8_1_owned_block18
      · exact single717_8_1_owned_block19
      · exact single717_8_1_owned_block20
      · exact single717_8_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_8_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_8_1_checked : single717_8_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_8_1 case717Family 1
    single717_8_1Signatures single717_8_1_queries_exact (by decide) single717_8_1_metadata

def single717_9_0 : DirectSingleDomain := ⟨8192,1,1,[{2},{4},{6}],[(certified_query% 1145),(certified_query% 1146),(certified_query% 1150),(certified_query% 1157),(certified_query% 1167),(certified_query% 1175),(certified_query% 1184)]⟩
private def single717_9_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(8192,0,{0}),(8192,0,{1}),(8192,0,{3}),(8192,0,{5}),(8192,0,{7}),(8192,0,{8}),(8192,0,{9})]
theorem single717_9_0_checked : single717_9_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_9_0 case717Family 0
    single717_9_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_9_1 : DirectSingleDomain := ⟨8192,1,3,[{2},{0,2},{5},{2,5},{0,2,5},{5,8},{2,5,8}],[(certified_query% 1194),(certified_query% 1195),(certified_query% 1196),(certified_query% 1197),N12Compact.HistoricalOwnership.Queries.query1021_certified,(certified_query% 1198),(certified_query% 1199),(certified_query% 1200),N12Compact.HistoricalOwnership.Queries.query1022_certified,(certified_query% 1201),N12Compact.HistoricalOwnership.Queries.query1023_certified,N12Compact.HistoricalOwnership.Queries.query1024_certified,(certified_query% 1202),(certified_query% 1203),(certified_query% 1204),N12Compact.HistoricalOwnership.Queries.query1025_certified,(certified_query% 1205),N12Compact.HistoricalOwnership.Queries.query1026_certified,N12Compact.HistoricalOwnership.Queries.query1027_certified,(certified_query% 1206),N12Compact.HistoricalOwnership.Queries.query1028_certified,N12Compact.HistoricalOwnership.Queries.query1029_certified,N12Compact.HistoricalOwnership.Queries.query1030_certified,(certified_query% 1207),(certified_query% 1208),N12Compact.HistoricalOwnership.Queries.query1031_certified,N12Compact.HistoricalOwnership.Queries.query1032_certified,(certified_query% 1209),N12Compact.HistoricalOwnership.Queries.query1033_certified,N12Compact.HistoricalOwnership.Queries.query1034_certified,N12Compact.HistoricalOwnership.Queries.query1035_certified,(certified_query% 1210),N12Compact.HistoricalOwnership.Queries.query1036_certified,N12Compact.HistoricalOwnership.Queries.query1037_certified,N12Compact.HistoricalOwnership.Queries.query1038_certified,N12Compact.HistoricalOwnership.Queries.query1039_certified,(certified_query% 1211),(certified_query% 1212),(certified_query% 1213),N12Compact.HistoricalOwnership.Queries.query1040_certified,(certified_query% 1214),N12Compact.HistoricalOwnership.Queries.query1041_certified,N12Compact.HistoricalOwnership.Queries.query1042_certified,(certified_query% 1215),N12Compact.HistoricalOwnership.Queries.query1043_certified,N12Compact.HistoricalOwnership.Queries.query1044_certified,N12Compact.HistoricalOwnership.Queries.query1045_certified,(certified_query% 1216),N12Compact.HistoricalOwnership.Queries.query1046_certified,N12Compact.HistoricalOwnership.Queries.query1047_certified,N12Compact.HistoricalOwnership.Queries.query1048_certified,N12Compact.HistoricalOwnership.Queries.query1049_certified,(certified_query% 1217),N12Compact.HistoricalOwnership.Queries.query1050_certified,N12Compact.HistoricalOwnership.Queries.query1051_certified,N12Compact.HistoricalOwnership.Queries.query1052_certified,N12Compact.HistoricalOwnership.Queries.query1053_certified,N12Compact.HistoricalOwnership.Queries.query1054_certified,(certified_query% 1218),(certified_query% 1219),(certified_query% 1220),N12Compact.HistoricalOwnership.Queries.query1055_certified,(certified_query% 1221),N12Compact.HistoricalOwnership.Queries.query1056_certified,N12Compact.HistoricalOwnership.Queries.query1057_certified,(certified_query% 1222),N12Compact.HistoricalOwnership.Queries.query1058_certified,N12Compact.HistoricalOwnership.Queries.query1059_certified,N12Compact.HistoricalOwnership.Queries.query1060_certified,(certified_query% 1223),N12Compact.HistoricalOwnership.Queries.query1061_certified,N12Compact.HistoricalOwnership.Queries.query1062_certified,N12Compact.HistoricalOwnership.Queries.query1063_certified,N12Compact.HistoricalOwnership.Queries.query1064_certified,(certified_query% 1224),N12Compact.HistoricalOwnership.Queries.query1065_certified,N12Compact.HistoricalOwnership.Queries.query1066_certified,N12Compact.HistoricalOwnership.Queries.query1067_certified,N12Compact.HistoricalOwnership.Queries.query1068_certified,N12Compact.HistoricalOwnership.Queries.query1069_certified,(certified_query% 1225),N12Compact.HistoricalOwnership.Queries.query1070_certified,N12Compact.HistoricalOwnership.Queries.query1071_certified,N12Compact.HistoricalOwnership.Queries.query1072_certified,N12Compact.HistoricalOwnership.Queries.query1073_certified,N12Compact.HistoricalOwnership.Queries.query1074_certified,N12Compact.HistoricalOwnership.Queries.query1075_certified,(certified_query% 1226),(certified_query% 1227),(certified_query% 1228),N12Compact.HistoricalOwnership.Queries.query1076_certified,(certified_query% 1229),N12Compact.HistoricalOwnership.Queries.query1077_certified,N12Compact.HistoricalOwnership.Queries.query1078_certified,(certified_query% 1230),N12Compact.HistoricalOwnership.Queries.query1079_certified,N12Compact.HistoricalOwnership.Queries.query1080_certified,N12Compact.HistoricalOwnership.Queries.query1081_certified,(certified_query% 1231),N12Compact.HistoricalOwnership.Queries.query1082_certified,N12Compact.HistoricalOwnership.Queries.query1083_certified,N12Compact.HistoricalOwnership.Queries.query1084_certified,N12Compact.HistoricalOwnership.Queries.query1085_certified,N12Compact.HistoricalOwnership.Queries.query1086_certified,N12Compact.HistoricalOwnership.Queries.query1087_certified,N12Compact.HistoricalOwnership.Queries.query1088_certified,N12Compact.HistoricalOwnership.Queries.query1089_certified,(certified_query% 1232),N12Compact.HistoricalOwnership.Queries.query1090_certified,N12Compact.HistoricalOwnership.Queries.query1091_certified,N12Compact.HistoricalOwnership.Queries.query1092_certified,N12Compact.HistoricalOwnership.Queries.query1093_certified,N12Compact.HistoricalOwnership.Queries.query1094_certified,N12Compact.HistoricalOwnership.Queries.query1095_certified,(certified_query% 1233),N12Compact.HistoricalOwnership.Queries.query1096_certified,N12Compact.HistoricalOwnership.Queries.query1097_certified,N12Compact.HistoricalOwnership.Queries.query1098_certified,N12Compact.HistoricalOwnership.Queries.query1099_certified,N12Compact.HistoricalOwnership.Queries.query1100_certified,N12Compact.HistoricalOwnership.Queries.query1101_certified,N12Compact.HistoricalOwnership.Queries.query1102_certified,(certified_query% 1234),(certified_query% 1235),(certified_query% 1236),N12Compact.HistoricalOwnership.Queries.query1103_certified,(certified_query% 1237),N12Compact.HistoricalOwnership.Queries.query1104_certified,N12Compact.HistoricalOwnership.Queries.query1105_certified,(certified_query% 1238),N12Compact.HistoricalOwnership.Queries.query1106_certified,N12Compact.HistoricalOwnership.Queries.query1107_certified,N12Compact.HistoricalOwnership.Queries.query1108_certified,(certified_query% 1239),N12Compact.HistoricalOwnership.Queries.query1109_certified,N12Compact.HistoricalOwnership.Queries.query1110_certified,N12Compact.HistoricalOwnership.Queries.query1111_certified,N12Compact.HistoricalOwnership.Queries.query1112_certified,(certified_query% 1240),N12Compact.HistoricalOwnership.Queries.query1113_certified,N12Compact.HistoricalOwnership.Queries.query1114_certified,N12Compact.HistoricalOwnership.Queries.query1115_certified,N12Compact.HistoricalOwnership.Queries.query1116_certified,N12Compact.HistoricalOwnership.Queries.query1117_certified,(certified_query% 1241),N12Compact.HistoricalOwnership.Queries.query1118_certified,N12Compact.HistoricalOwnership.Queries.query1119_certified,N12Compact.HistoricalOwnership.Queries.query1120_certified,N12Compact.HistoricalOwnership.Queries.query1121_certified,N12Compact.HistoricalOwnership.Queries.query1122_certified,N12Compact.HistoricalOwnership.Queries.query1123_certified,(certified_query% 1242),N12Compact.HistoricalOwnership.Queries.query1124_certified,N12Compact.HistoricalOwnership.Queries.query1125_certified,N12Compact.HistoricalOwnership.Queries.query1126_certified,N12Compact.HistoricalOwnership.Queries.query1127_certified,N12Compact.HistoricalOwnership.Queries.query1128_certified,N12Compact.HistoricalOwnership.Queries.query1129_certified,N12Compact.HistoricalOwnership.Queries.query1130_certified,(certified_query% 1243),N12Compact.HistoricalOwnership.Queries.query1131_certified,N12Compact.HistoricalOwnership.Queries.query1132_certified,N12Compact.HistoricalOwnership.Queries.query1133_certified,N12Compact.HistoricalOwnership.Queries.query1134_certified,N12Compact.HistoricalOwnership.Queries.query1135_certified,N12Compact.HistoricalOwnership.Queries.query1136_certified,N12Compact.HistoricalOwnership.Queries.query1137_certified,N12Compact.HistoricalOwnership.Queries.query1138_certified]⟩
private def single717_9_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(8192,1,{0}),(8192,1,{1}),(8192,1,{0,1}),(8192,1,{1,2}),(8192,1,{0,1,2}),(8192,1,{3}),(8192,1,{0,3}),(8192,1,{1,3}),(8192,1,{0,1,3}),(8192,1,{2,3}),(8192,1,{0,2,3}),(8192,1,{1,2,3}),(8192,1,{4}),(8192,1,{0,4}),(8192,1,{1,4}),(8192,1,{0,1,4}),(8192,1,{2,4}),(8192,1,{0,2,4}),(8192,1,{1,2,4}),(8192,1,{3,4}),(8192,1,{0,3,4}),(8192,1,{1,3,4}),(8192,1,{2,3,4}),(8192,1,{0,5}),(8192,1,{1,5}),(8192,1,{0,1,5}),(8192,1,{1,2,5}),(8192,1,{3,5}),(8192,1,{0,3,5}),(8192,1,{1,3,5}),(8192,1,{2,3,5}),(8192,1,{4,5}),(8192,1,{0,4,5}),(8192,1,{1,4,5}),(8192,1,{2,4,5}),(8192,1,{3,4,5}),(8192,1,{6}),(8192,1,{0,6}),(8192,1,{1,6}),(8192,1,{0,1,6}),(8192,1,{2,6}),(8192,1,{0,2,6}),(8192,1,{1,2,6}),(8192,1,{3,6}),(8192,1,{0,3,6}),(8192,1,{1,3,6}),(8192,1,{2,3,6}),(8192,1,{4,6}),(8192,1,{0,4,6}),(8192,1,{1,4,6}),(8192,1,{2,4,6}),(8192,1,{3,4,6}),(8192,1,{5,6}),(8192,1,{0,5,6}),(8192,1,{1,5,6}),(8192,1,{2,5,6}),(8192,1,{3,5,6}),(8192,1,{4,5,6}),(8192,1,{7}),(8192,1,{0,7}),(8192,1,{1,7}),(8192,1,{0,1,7}),(8192,1,{2,7}),(8192,1,{0,2,7}),(8192,1,{1,2,7}),(8192,1,{3,7}),(8192,1,{0,3,7}),(8192,1,{1,3,7}),(8192,1,{2,3,7}),(8192,1,{4,7}),(8192,1,{0,4,7}),(8192,1,{1,4,7}),(8192,1,{2,4,7}),(8192,1,{3,4,7}),(8192,1,{5,7}),(8192,1,{0,5,7}),(8192,1,{1,5,7}),(8192,1,{2,5,7}),(8192,1,{3,5,7}),(8192,1,{4,5,7}),(8192,1,{6,7}),(8192,1,{0,6,7}),(8192,1,{1,6,7}),(8192,1,{2,6,7}),(8192,1,{3,6,7}),(8192,1,{4,6,7}),(8192,1,{5,6,7}),(8192,1,{8}),(8192,1,{0,8}),(8192,1,{1,8}),(8192,1,{0,1,8}),(8192,1,{2,8}),(8192,1,{0,2,8}),(8192,1,{1,2,8}),(8192,1,{3,8}),(8192,1,{0,3,8}),(8192,1,{1,3,8}),(8192,1,{2,3,8}),(8192,1,{4,8}),(8192,1,{0,4,8}),(8192,1,{1,4,8}),(8192,1,{2,4,8}),(8192,1,{3,4,8}),(8192,1,{0,5,8}),(8192,1,{1,5,8}),(8192,1,{3,5,8}),(8192,1,{4,5,8}),(8192,1,{6,8}),(8192,1,{0,6,8}),(8192,1,{1,6,8}),(8192,1,{2,6,8}),(8192,1,{3,6,8}),(8192,1,{4,6,8}),(8192,1,{5,6,8}),(8192,1,{7,8}),(8192,1,{0,7,8}),(8192,1,{1,7,8}),(8192,1,{2,7,8}),(8192,1,{3,7,8}),(8192,1,{4,7,8}),(8192,1,{5,7,8}),(8192,1,{6,7,8}),(8192,1,{9}),(8192,1,{0,9}),(8192,1,{1,9}),(8192,1,{0,1,9}),(8192,1,{2,9}),(8192,1,{0,2,9}),(8192,1,{1,2,9}),(8192,1,{3,9}),(8192,1,{0,3,9}),(8192,1,{1,3,9}),(8192,1,{2,3,9}),(8192,1,{4,9}),(8192,1,{0,4,9}),(8192,1,{1,4,9}),(8192,1,{2,4,9}),(8192,1,{3,4,9}),(8192,1,{5,9}),(8192,1,{0,5,9}),(8192,1,{1,5,9}),(8192,1,{2,5,9}),(8192,1,{3,5,9}),(8192,1,{4,5,9}),(8192,1,{6,9}),(8192,1,{0,6,9}),(8192,1,{1,6,9}),(8192,1,{2,6,9}),(8192,1,{3,6,9}),(8192,1,{4,6,9}),(8192,1,{5,6,9}),(8192,1,{7,9}),(8192,1,{0,7,9}),(8192,1,{1,7,9}),(8192,1,{2,7,9}),(8192,1,{3,7,9}),(8192,1,{4,7,9}),(8192,1,{5,7,9}),(8192,1,{6,7,9}),(8192,1,{8,9}),(8192,1,{0,8,9}),(8192,1,{1,8,9}),(8192,1,{2,8,9}),(8192,1,{3,8,9}),(8192,1,{4,8,9}),(8192,1,{5,8,9}),(8192,1,{6,8,9}),(8192,1,{7,8,9})]
private theorem single717_9_1_queries_exact :
    single717_9_1Signatures = single717_9_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_9_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{2},{0,2},{5},{2,5},{0,2,5},{5,8},{2,5,8}] : List (Finset Nat)) ∨ (8192,1,owned) ∈ single717_9_1Signatures

private instance : DecidablePred single717_9_1_owned_claim := fun index => by
  unfold single717_9_1_owned_claim
  infer_instance

private theorem single717_9_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_9_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_9_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_9_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_9_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_9_1 case717Family 1 single717_9_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨8192,1,3,[{2},{0,2},{5},{2,5},{0,2,5},{5,8},{2,5,8}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_9_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_9_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_9_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_9_1_owned_block0
      · exact single717_9_1_owned_block1
      · exact single717_9_1_owned_block2
      · exact single717_9_1_owned_block3
      · exact single717_9_1_owned_block4
      · exact single717_9_1_owned_block5
      · exact single717_9_1_owned_block6
      · exact single717_9_1_owned_block7
      · exact single717_9_1_owned_block8
      · exact single717_9_1_owned_block9
      · exact single717_9_1_owned_block10
      · exact single717_9_1_owned_block11
      · exact single717_9_1_owned_block12
      · exact single717_9_1_owned_block13
      · exact single717_9_1_owned_block14
      · exact single717_9_1_owned_block15
      · exact single717_9_1_owned_block16
      · exact single717_9_1_owned_block17
      · exact single717_9_1_owned_block18
      · exact single717_9_1_owned_block19
      · exact single717_9_1_owned_block20
      · exact single717_9_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_9_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_9_1_checked : single717_9_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_9_1 case717Family 1
    single717_9_1Signatures single717_9_1_queries_exact (by decide) single717_9_1_metadata

def single717_10_0 : DirectSingleDomain := ⟨16384,1,1,[{8},{9}],[(certified_query% 1294),(certified_query% 1295),(certified_query% 1297),(certified_query% 1300),(certified_query% 1304),(certified_query% 1309),(certified_query% 1315),(certified_query% 1322)]⟩
private def single717_10_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16384,0,{0}),(16384,0,{1}),(16384,0,{2}),(16384,0,{3}),(16384,0,{4}),(16384,0,{5}),(16384,0,{6}),(16384,0,{7})]
theorem single717_10_0_checked : single717_10_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_10_0 case717Family 0
    single717_10_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_10_1 : DirectSingleDomain := ⟨16384,1,3,[{6},{8},{6,8},{9},{6,9},{8,9},{6,8,9}],[(certified_query% 1344),(certified_query% 1345),(certified_query% 1346),(certified_query% 1347),(certified_query% 1348),(certified_query% 1349),N12Compact.HistoricalOwnership.Queries.query1143_certified,(certified_query% 1350),(certified_query% 1351),(certified_query% 1352),N12Compact.HistoricalOwnership.Queries.query1144_certified,(certified_query% 1353),N12Compact.HistoricalOwnership.Queries.query1145_certified,N12Compact.HistoricalOwnership.Queries.query1146_certified,(certified_query% 1354),(certified_query% 1355),(certified_query% 1356),N12Compact.HistoricalOwnership.Queries.query1147_certified,(certified_query% 1357),N12Compact.HistoricalOwnership.Queries.query1148_certified,N12Compact.HistoricalOwnership.Queries.query1149_certified,(certified_query% 1358),N12Compact.HistoricalOwnership.Queries.query1150_certified,N12Compact.HistoricalOwnership.Queries.query1151_certified,N12Compact.HistoricalOwnership.Queries.query1152_certified,(certified_query% 1359),(certified_query% 1360),(certified_query% 1361),N12Compact.HistoricalOwnership.Queries.query1153_certified,(certified_query% 1362),N12Compact.HistoricalOwnership.Queries.query1154_certified,N12Compact.HistoricalOwnership.Queries.query1155_certified,(certified_query% 1363),N12Compact.HistoricalOwnership.Queries.query1156_certified,N12Compact.HistoricalOwnership.Queries.query1157_certified,N12Compact.HistoricalOwnership.Queries.query1158_certified,(certified_query% 1364),N12Compact.HistoricalOwnership.Queries.query1159_certified,N12Compact.HistoricalOwnership.Queries.query1160_certified,N12Compact.HistoricalOwnership.Queries.query1161_certified,N12Compact.HistoricalOwnership.Queries.query1162_certified,(certified_query% 1365),(certified_query% 1366),N12Compact.HistoricalOwnership.Queries.query1163_certified,(certified_query% 1367),N12Compact.HistoricalOwnership.Queries.query1164_certified,N12Compact.HistoricalOwnership.Queries.query1165_certified,(certified_query% 1368),N12Compact.HistoricalOwnership.Queries.query1166_certified,N12Compact.HistoricalOwnership.Queries.query1167_certified,N12Compact.HistoricalOwnership.Queries.query1168_certified,(certified_query% 1369),N12Compact.HistoricalOwnership.Queries.query1169_certified,N12Compact.HistoricalOwnership.Queries.query1170_certified,N12Compact.HistoricalOwnership.Queries.query1171_certified,N12Compact.HistoricalOwnership.Queries.query1172_certified,(certified_query% 1370),N12Compact.HistoricalOwnership.Queries.query1173_certified,N12Compact.HistoricalOwnership.Queries.query1174_certified,N12Compact.HistoricalOwnership.Queries.query1175_certified,N12Compact.HistoricalOwnership.Queries.query1176_certified,N12Compact.HistoricalOwnership.Queries.query1177_certified,(certified_query% 1371),(certified_query% 1372),(certified_query% 1373),N12Compact.HistoricalOwnership.Queries.query1178_certified,(certified_query% 1374),N12Compact.HistoricalOwnership.Queries.query1179_certified,N12Compact.HistoricalOwnership.Queries.query1180_certified,(certified_query% 1375),N12Compact.HistoricalOwnership.Queries.query1181_certified,N12Compact.HistoricalOwnership.Queries.query1182_certified,N12Compact.HistoricalOwnership.Queries.query1183_certified,(certified_query% 1376),N12Compact.HistoricalOwnership.Queries.query1184_certified,N12Compact.HistoricalOwnership.Queries.query1185_certified,N12Compact.HistoricalOwnership.Queries.query1186_certified,N12Compact.HistoricalOwnership.Queries.query1187_certified,(certified_query% 1377),N12Compact.HistoricalOwnership.Queries.query1188_certified,N12Compact.HistoricalOwnership.Queries.query1189_certified,N12Compact.HistoricalOwnership.Queries.query1190_certified,N12Compact.HistoricalOwnership.Queries.query1191_certified,N12Compact.HistoricalOwnership.Queries.query1192_certified,(certified_query% 1378),N12Compact.HistoricalOwnership.Queries.query1193_certified,N12Compact.HistoricalOwnership.Queries.query1194_certified,N12Compact.HistoricalOwnership.Queries.query1195_certified,N12Compact.HistoricalOwnership.Queries.query1196_certified,N12Compact.HistoricalOwnership.Queries.query1197_certified,N12Compact.HistoricalOwnership.Queries.query1198_certified,(certified_query% 1379),(certified_query% 1380),N12Compact.HistoricalOwnership.Queries.query1199_certified,(certified_query% 1381),N12Compact.HistoricalOwnership.Queries.query1200_certified,N12Compact.HistoricalOwnership.Queries.query1201_certified,(certified_query% 1382),N12Compact.HistoricalOwnership.Queries.query1202_certified,N12Compact.HistoricalOwnership.Queries.query1203_certified,N12Compact.HistoricalOwnership.Queries.query1204_certified,(certified_query% 1383),N12Compact.HistoricalOwnership.Queries.query1205_certified,N12Compact.HistoricalOwnership.Queries.query1206_certified,N12Compact.HistoricalOwnership.Queries.query1207_certified,N12Compact.HistoricalOwnership.Queries.query1208_certified,(certified_query% 1384),N12Compact.HistoricalOwnership.Queries.query1209_certified,N12Compact.HistoricalOwnership.Queries.query1210_certified,N12Compact.HistoricalOwnership.Queries.query1211_certified,N12Compact.HistoricalOwnership.Queries.query1212_certified,N12Compact.HistoricalOwnership.Queries.query1213_certified,N12Compact.HistoricalOwnership.Queries.query1214_certified,N12Compact.HistoricalOwnership.Queries.query1215_certified,N12Compact.HistoricalOwnership.Queries.query1216_certified,N12Compact.HistoricalOwnership.Queries.query1217_certified,N12Compact.HistoricalOwnership.Queries.query1218_certified,N12Compact.HistoricalOwnership.Queries.query1219_certified,(certified_query% 1385),N12Compact.HistoricalOwnership.Queries.query1220_certified,N12Compact.HistoricalOwnership.Queries.query1221_certified,N12Compact.HistoricalOwnership.Queries.query1222_certified,N12Compact.HistoricalOwnership.Queries.query1223_certified,N12Compact.HistoricalOwnership.Queries.query1224_certified,N12Compact.HistoricalOwnership.Queries.query1225_certified,N12Compact.HistoricalOwnership.Queries.query1226_certified,(certified_query% 1386),(certified_query% 1387),N12Compact.HistoricalOwnership.Queries.query1227_certified,(certified_query% 1388),N12Compact.HistoricalOwnership.Queries.query1228_certified,N12Compact.HistoricalOwnership.Queries.query1229_certified,(certified_query% 1389),N12Compact.HistoricalOwnership.Queries.query1230_certified,N12Compact.HistoricalOwnership.Queries.query1231_certified,N12Compact.HistoricalOwnership.Queries.query1232_certified,(certified_query% 1390),N12Compact.HistoricalOwnership.Queries.query1233_certified,N12Compact.HistoricalOwnership.Queries.query1234_certified,N12Compact.HistoricalOwnership.Queries.query1235_certified,N12Compact.HistoricalOwnership.Queries.query1236_certified,(certified_query% 1391),N12Compact.HistoricalOwnership.Queries.query1237_certified,N12Compact.HistoricalOwnership.Queries.query1238_certified,N12Compact.HistoricalOwnership.Queries.query1239_certified,N12Compact.HistoricalOwnership.Queries.query1240_certified,N12Compact.HistoricalOwnership.Queries.query1241_certified,N12Compact.HistoricalOwnership.Queries.query1242_certified,N12Compact.HistoricalOwnership.Queries.query1243_certified,N12Compact.HistoricalOwnership.Queries.query1244_certified,N12Compact.HistoricalOwnership.Queries.query1245_certified,N12Compact.HistoricalOwnership.Queries.query1246_certified,N12Compact.HistoricalOwnership.Queries.query1247_certified,(certified_query% 1392),N12Compact.HistoricalOwnership.Queries.query1248_certified,N12Compact.HistoricalOwnership.Queries.query1249_certified,N12Compact.HistoricalOwnership.Queries.query1250_certified,N12Compact.HistoricalOwnership.Queries.query1251_certified,N12Compact.HistoricalOwnership.Queries.query1252_certified,N12Compact.HistoricalOwnership.Queries.query1253_certified,N12Compact.HistoricalOwnership.Queries.query1254_certified,N12Compact.HistoricalOwnership.Queries.query1255_certified,N12Compact.HistoricalOwnership.Queries.query1256_certified,N12Compact.HistoricalOwnership.Queries.query1257_certified,N12Compact.HistoricalOwnership.Queries.query1258_certified,N12Compact.HistoricalOwnership.Queries.query1259_certified,N12Compact.HistoricalOwnership.Queries.query1260_certified,N12Compact.HistoricalOwnership.Queries.query1261_certified]⟩
private def single717_10_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16384,1,{0}),(16384,1,{1}),(16384,1,{0,1}),(16384,1,{2}),(16384,1,{0,2}),(16384,1,{1,2}),(16384,1,{0,1,2}),(16384,1,{3}),(16384,1,{0,3}),(16384,1,{1,3}),(16384,1,{0,1,3}),(16384,1,{2,3}),(16384,1,{0,2,3}),(16384,1,{1,2,3}),(16384,1,{4}),(16384,1,{0,4}),(16384,1,{1,4}),(16384,1,{0,1,4}),(16384,1,{2,4}),(16384,1,{0,2,4}),(16384,1,{1,2,4}),(16384,1,{3,4}),(16384,1,{0,3,4}),(16384,1,{1,3,4}),(16384,1,{2,3,4}),(16384,1,{5}),(16384,1,{0,5}),(16384,1,{1,5}),(16384,1,{0,1,5}),(16384,1,{2,5}),(16384,1,{0,2,5}),(16384,1,{1,2,5}),(16384,1,{3,5}),(16384,1,{0,3,5}),(16384,1,{1,3,5}),(16384,1,{2,3,5}),(16384,1,{4,5}),(16384,1,{0,4,5}),(16384,1,{1,4,5}),(16384,1,{2,4,5}),(16384,1,{3,4,5}),(16384,1,{0,6}),(16384,1,{1,6}),(16384,1,{0,1,6}),(16384,1,{2,6}),(16384,1,{0,2,6}),(16384,1,{1,2,6}),(16384,1,{3,6}),(16384,1,{0,3,6}),(16384,1,{1,3,6}),(16384,1,{2,3,6}),(16384,1,{4,6}),(16384,1,{0,4,6}),(16384,1,{1,4,6}),(16384,1,{2,4,6}),(16384,1,{3,4,6}),(16384,1,{5,6}),(16384,1,{0,5,6}),(16384,1,{1,5,6}),(16384,1,{2,5,6}),(16384,1,{3,5,6}),(16384,1,{4,5,6}),(16384,1,{7}),(16384,1,{0,7}),(16384,1,{1,7}),(16384,1,{0,1,7}),(16384,1,{2,7}),(16384,1,{0,2,7}),(16384,1,{1,2,7}),(16384,1,{3,7}),(16384,1,{0,3,7}),(16384,1,{1,3,7}),(16384,1,{2,3,7}),(16384,1,{4,7}),(16384,1,{0,4,7}),(16384,1,{1,4,7}),(16384,1,{2,4,7}),(16384,1,{3,4,7}),(16384,1,{5,7}),(16384,1,{0,5,7}),(16384,1,{1,5,7}),(16384,1,{2,5,7}),(16384,1,{3,5,7}),(16384,1,{4,5,7}),(16384,1,{6,7}),(16384,1,{0,6,7}),(16384,1,{1,6,7}),(16384,1,{2,6,7}),(16384,1,{3,6,7}),(16384,1,{4,6,7}),(16384,1,{5,6,7}),(16384,1,{0,8}),(16384,1,{1,8}),(16384,1,{0,1,8}),(16384,1,{2,8}),(16384,1,{0,2,8}),(16384,1,{1,2,8}),(16384,1,{3,8}),(16384,1,{0,3,8}),(16384,1,{1,3,8}),(16384,1,{2,3,8}),(16384,1,{4,8}),(16384,1,{0,4,8}),(16384,1,{1,4,8}),(16384,1,{2,4,8}),(16384,1,{3,4,8}),(16384,1,{5,8}),(16384,1,{0,5,8}),(16384,1,{1,5,8}),(16384,1,{2,5,8}),(16384,1,{3,5,8}),(16384,1,{4,5,8}),(16384,1,{0,6,8}),(16384,1,{1,6,8}),(16384,1,{2,6,8}),(16384,1,{3,6,8}),(16384,1,{4,6,8}),(16384,1,{5,6,8}),(16384,1,{7,8}),(16384,1,{0,7,8}),(16384,1,{1,7,8}),(16384,1,{2,7,8}),(16384,1,{3,7,8}),(16384,1,{4,7,8}),(16384,1,{5,7,8}),(16384,1,{6,7,8}),(16384,1,{0,9}),(16384,1,{1,9}),(16384,1,{0,1,9}),(16384,1,{2,9}),(16384,1,{0,2,9}),(16384,1,{1,2,9}),(16384,1,{3,9}),(16384,1,{0,3,9}),(16384,1,{1,3,9}),(16384,1,{2,3,9}),(16384,1,{4,9}),(16384,1,{0,4,9}),(16384,1,{1,4,9}),(16384,1,{2,4,9}),(16384,1,{3,4,9}),(16384,1,{5,9}),(16384,1,{0,5,9}),(16384,1,{1,5,9}),(16384,1,{2,5,9}),(16384,1,{3,5,9}),(16384,1,{4,5,9}),(16384,1,{0,6,9}),(16384,1,{1,6,9}),(16384,1,{2,6,9}),(16384,1,{3,6,9}),(16384,1,{4,6,9}),(16384,1,{5,6,9}),(16384,1,{7,9}),(16384,1,{0,7,9}),(16384,1,{1,7,9}),(16384,1,{2,7,9}),(16384,1,{3,7,9}),(16384,1,{4,7,9}),(16384,1,{5,7,9}),(16384,1,{6,7,9}),(16384,1,{0,8,9}),(16384,1,{1,8,9}),(16384,1,{2,8,9}),(16384,1,{3,8,9}),(16384,1,{4,8,9}),(16384,1,{5,8,9}),(16384,1,{7,8,9})]
private theorem single717_10_1_queries_exact :
    single717_10_1Signatures = single717_10_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_10_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{6},{8},{6,8},{9},{6,9},{8,9},{6,8,9}] : List (Finset Nat)) ∨ (16384,1,owned) ∈ single717_10_1Signatures

private instance : DecidablePred single717_10_1_owned_claim := fun index => by
  unfold single717_10_1_owned_claim
  infer_instance

private theorem single717_10_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_10_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_10_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_10_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_10_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_10_1 case717Family 1 single717_10_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨16384,1,3,[{6},{8},{6,8},{9},{6,9},{8,9},{6,8,9}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_10_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_10_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_10_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_10_1_owned_block0
      · exact single717_10_1_owned_block1
      · exact single717_10_1_owned_block2
      · exact single717_10_1_owned_block3
      · exact single717_10_1_owned_block4
      · exact single717_10_1_owned_block5
      · exact single717_10_1_owned_block6
      · exact single717_10_1_owned_block7
      · exact single717_10_1_owned_block8
      · exact single717_10_1_owned_block9
      · exact single717_10_1_owned_block10
      · exact single717_10_1_owned_block11
      · exact single717_10_1_owned_block12
      · exact single717_10_1_owned_block13
      · exact single717_10_1_owned_block14
      · exact single717_10_1_owned_block15
      · exact single717_10_1_owned_block16
      · exact single717_10_1_owned_block17
      · exact single717_10_1_owned_block18
      · exact single717_10_1_owned_block19
      · exact single717_10_1_owned_block20
      · exact single717_10_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_10_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_10_1_checked : single717_10_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_10_1 case717Family 1
    single717_10_1Signatures single717_10_1_queries_exact (by decide) single717_10_1_metadata

def single717_11_0 : DirectSingleDomain := ⟨32768,1,1,[{3},{5},{7}],[(certified_query% 1536),(certified_query% 1537),(certified_query% 1539),(certified_query% 1545),(certified_query% 1554),(certified_query% 1566),(certified_query% 1575)]⟩
private def single717_11_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32768,0,{0}),(32768,0,{1}),(32768,0,{2}),(32768,0,{4}),(32768,0,{6}),(32768,0,{8}),(32768,0,{9})]
theorem single717_11_0_checked : single717_11_0.Check case717Family 0 :=
  N12Compact.SmallOwnerDomain.checked single717_11_0 case717Family 0
    single717_11_0Signatures (by rfl) (by decide) (by decide +kernel)

def single717_11_1 : DirectSingleDomain := ⟨32768,1,3,[{4},{1,4},{7},{4,7},{1,4,7},{7,9},{4,7,9}],[(certified_query% 1585),(certified_query% 1586),(certified_query% 1587),(certified_query% 1588),(certified_query% 1589),(certified_query% 1590),N12Compact.HistoricalOwnership.Queries.query1264_certified,(certified_query% 1591),(certified_query% 1592),(certified_query% 1593),N12Compact.HistoricalOwnership.Queries.query1265_certified,(certified_query% 1594),N12Compact.HistoricalOwnership.Queries.query1266_certified,N12Compact.HistoricalOwnership.Queries.query1267_certified,(certified_query% 1595),N12Compact.HistoricalOwnership.Queries.query1268_certified,(certified_query% 1596),N12Compact.HistoricalOwnership.Queries.query1269_certified,N12Compact.HistoricalOwnership.Queries.query1270_certified,(certified_query% 1597),N12Compact.HistoricalOwnership.Queries.query1271_certified,N12Compact.HistoricalOwnership.Queries.query1272_certified,N12Compact.HistoricalOwnership.Queries.query1273_certified,(certified_query% 1598),(certified_query% 1599),(certified_query% 1600),N12Compact.HistoricalOwnership.Queries.query1274_certified,(certified_query% 1601),N12Compact.HistoricalOwnership.Queries.query1275_certified,N12Compact.HistoricalOwnership.Queries.query1276_certified,(certified_query% 1602),N12Compact.HistoricalOwnership.Queries.query1277_certified,N12Compact.HistoricalOwnership.Queries.query1278_certified,N12Compact.HistoricalOwnership.Queries.query1279_certified,(certified_query% 1603),N12Compact.HistoricalOwnership.Queries.query1280_certified,N12Compact.HistoricalOwnership.Queries.query1281_certified,N12Compact.HistoricalOwnership.Queries.query1282_certified,N12Compact.HistoricalOwnership.Queries.query1283_certified,(certified_query% 1604),(certified_query% 1605),(certified_query% 1606),N12Compact.HistoricalOwnership.Queries.query1284_certified,(certified_query% 1607),N12Compact.HistoricalOwnership.Queries.query1285_certified,N12Compact.HistoricalOwnership.Queries.query1286_certified,(certified_query% 1608),N12Compact.HistoricalOwnership.Queries.query1287_certified,N12Compact.HistoricalOwnership.Queries.query1288_certified,N12Compact.HistoricalOwnership.Queries.query1289_certified,(certified_query% 1609),N12Compact.HistoricalOwnership.Queries.query1290_certified,N12Compact.HistoricalOwnership.Queries.query1291_certified,N12Compact.HistoricalOwnership.Queries.query1292_certified,N12Compact.HistoricalOwnership.Queries.query1293_certified,(certified_query% 1610),N12Compact.HistoricalOwnership.Queries.query1294_certified,N12Compact.HistoricalOwnership.Queries.query1295_certified,N12Compact.HistoricalOwnership.Queries.query1296_certified,N12Compact.HistoricalOwnership.Queries.query1297_certified,N12Compact.HistoricalOwnership.Queries.query1298_certified,(certified_query% 1611),(certified_query% 1612),N12Compact.HistoricalOwnership.Queries.query1299_certified,(certified_query% 1613),N12Compact.HistoricalOwnership.Queries.query1300_certified,N12Compact.HistoricalOwnership.Queries.query1301_certified,(certified_query% 1614),N12Compact.HistoricalOwnership.Queries.query1302_certified,N12Compact.HistoricalOwnership.Queries.query1303_certified,N12Compact.HistoricalOwnership.Queries.query1304_certified,N12Compact.HistoricalOwnership.Queries.query1305_certified,N12Compact.HistoricalOwnership.Queries.query1306_certified,N12Compact.HistoricalOwnership.Queries.query1307_certified,(certified_query% 1615),N12Compact.HistoricalOwnership.Queries.query1308_certified,N12Compact.HistoricalOwnership.Queries.query1309_certified,N12Compact.HistoricalOwnership.Queries.query1310_certified,N12Compact.HistoricalOwnership.Queries.query1311_certified,N12Compact.HistoricalOwnership.Queries.query1312_certified,(certified_query% 1616),N12Compact.HistoricalOwnership.Queries.query1313_certified,N12Compact.HistoricalOwnership.Queries.query1314_certified,N12Compact.HistoricalOwnership.Queries.query1315_certified,N12Compact.HistoricalOwnership.Queries.query1316_certified,N12Compact.HistoricalOwnership.Queries.query1317_certified,N12Compact.HistoricalOwnership.Queries.query1318_certified,(certified_query% 1617),(certified_query% 1618),(certified_query% 1619),N12Compact.HistoricalOwnership.Queries.query1319_certified,(certified_query% 1620),N12Compact.HistoricalOwnership.Queries.query1320_certified,N12Compact.HistoricalOwnership.Queries.query1321_certified,(certified_query% 1621),N12Compact.HistoricalOwnership.Queries.query1322_certified,N12Compact.HistoricalOwnership.Queries.query1323_certified,N12Compact.HistoricalOwnership.Queries.query1324_certified,(certified_query% 1622),N12Compact.HistoricalOwnership.Queries.query1325_certified,N12Compact.HistoricalOwnership.Queries.query1326_certified,N12Compact.HistoricalOwnership.Queries.query1327_certified,N12Compact.HistoricalOwnership.Queries.query1328_certified,(certified_query% 1623),N12Compact.HistoricalOwnership.Queries.query1329_certified,N12Compact.HistoricalOwnership.Queries.query1330_certified,N12Compact.HistoricalOwnership.Queries.query1331_certified,N12Compact.HistoricalOwnership.Queries.query1332_certified,N12Compact.HistoricalOwnership.Queries.query1333_certified,(certified_query% 1624),N12Compact.HistoricalOwnership.Queries.query1334_certified,N12Compact.HistoricalOwnership.Queries.query1335_certified,N12Compact.HistoricalOwnership.Queries.query1336_certified,N12Compact.HistoricalOwnership.Queries.query1337_certified,N12Compact.HistoricalOwnership.Queries.query1338_certified,N12Compact.HistoricalOwnership.Queries.query1339_certified,(certified_query% 1625),N12Compact.HistoricalOwnership.Queries.query1340_certified,N12Compact.HistoricalOwnership.Queries.query1341_certified,N12Compact.HistoricalOwnership.Queries.query1342_certified,N12Compact.HistoricalOwnership.Queries.query1343_certified,N12Compact.HistoricalOwnership.Queries.query1344_certified,N12Compact.HistoricalOwnership.Queries.query1345_certified,N12Compact.HistoricalOwnership.Queries.query1346_certified,(certified_query% 1626),(certified_query% 1627),(certified_query% 1628),N12Compact.HistoricalOwnership.Queries.query1347_certified,(certified_query% 1629),N12Compact.HistoricalOwnership.Queries.query1348_certified,N12Compact.HistoricalOwnership.Queries.query1349_certified,(certified_query% 1630),N12Compact.HistoricalOwnership.Queries.query1350_certified,N12Compact.HistoricalOwnership.Queries.query1351_certified,N12Compact.HistoricalOwnership.Queries.query1352_certified,(certified_query% 1631),N12Compact.HistoricalOwnership.Queries.query1353_certified,N12Compact.HistoricalOwnership.Queries.query1354_certified,N12Compact.HistoricalOwnership.Queries.query1355_certified,N12Compact.HistoricalOwnership.Queries.query1356_certified,(certified_query% 1632),N12Compact.HistoricalOwnership.Queries.query1357_certified,N12Compact.HistoricalOwnership.Queries.query1358_certified,N12Compact.HistoricalOwnership.Queries.query1359_certified,N12Compact.HistoricalOwnership.Queries.query1360_certified,N12Compact.HistoricalOwnership.Queries.query1361_certified,(certified_query% 1633),N12Compact.HistoricalOwnership.Queries.query1362_certified,N12Compact.HistoricalOwnership.Queries.query1363_certified,N12Compact.HistoricalOwnership.Queries.query1364_certified,N12Compact.HistoricalOwnership.Queries.query1365_certified,N12Compact.HistoricalOwnership.Queries.query1366_certified,N12Compact.HistoricalOwnership.Queries.query1367_certified,N12Compact.HistoricalOwnership.Queries.query1368_certified,N12Compact.HistoricalOwnership.Queries.query1369_certified,N12Compact.HistoricalOwnership.Queries.query1370_certified,N12Compact.HistoricalOwnership.Queries.query1371_certified,N12Compact.HistoricalOwnership.Queries.query1372_certified,N12Compact.HistoricalOwnership.Queries.query1373_certified,(certified_query% 1634),N12Compact.HistoricalOwnership.Queries.query1374_certified,N12Compact.HistoricalOwnership.Queries.query1375_certified,N12Compact.HistoricalOwnership.Queries.query1376_certified,N12Compact.HistoricalOwnership.Queries.query1377_certified,N12Compact.HistoricalOwnership.Queries.query1378_certified,N12Compact.HistoricalOwnership.Queries.query1379_certified,N12Compact.HistoricalOwnership.Queries.query1380_certified,N12Compact.HistoricalOwnership.Queries.query1381_certified]⟩
private def single717_11_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32768,1,{0}),(32768,1,{1}),(32768,1,{0,1}),(32768,1,{2}),(32768,1,{0,2}),(32768,1,{1,2}),(32768,1,{0,1,2}),(32768,1,{3}),(32768,1,{0,3}),(32768,1,{1,3}),(32768,1,{0,1,3}),(32768,1,{2,3}),(32768,1,{0,2,3}),(32768,1,{1,2,3}),(32768,1,{0,4}),(32768,1,{0,1,4}),(32768,1,{2,4}),(32768,1,{0,2,4}),(32768,1,{1,2,4}),(32768,1,{3,4}),(32768,1,{0,3,4}),(32768,1,{1,3,4}),(32768,1,{2,3,4}),(32768,1,{5}),(32768,1,{0,5}),(32768,1,{1,5}),(32768,1,{0,1,5}),(32768,1,{2,5}),(32768,1,{0,2,5}),(32768,1,{1,2,5}),(32768,1,{3,5}),(32768,1,{0,3,5}),(32768,1,{1,3,5}),(32768,1,{2,3,5}),(32768,1,{4,5}),(32768,1,{0,4,5}),(32768,1,{1,4,5}),(32768,1,{2,4,5}),(32768,1,{3,4,5}),(32768,1,{6}),(32768,1,{0,6}),(32768,1,{1,6}),(32768,1,{0,1,6}),(32768,1,{2,6}),(32768,1,{0,2,6}),(32768,1,{1,2,6}),(32768,1,{3,6}),(32768,1,{0,3,6}),(32768,1,{1,3,6}),(32768,1,{2,3,6}),(32768,1,{4,6}),(32768,1,{0,4,6}),(32768,1,{1,4,6}),(32768,1,{2,4,6}),(32768,1,{3,4,6}),(32768,1,{5,6}),(32768,1,{0,5,6}),(32768,1,{1,5,6}),(32768,1,{2,5,6}),(32768,1,{3,5,6}),(32768,1,{4,5,6}),(32768,1,{0,7}),(32768,1,{1,7}),(32768,1,{0,1,7}),(32768,1,{2,7}),(32768,1,{0,2,7}),(32768,1,{1,2,7}),(32768,1,{3,7}),(32768,1,{0,3,7}),(32768,1,{1,3,7}),(32768,1,{2,3,7}),(32768,1,{0,4,7}),(32768,1,{2,4,7}),(32768,1,{3,4,7}),(32768,1,{5,7}),(32768,1,{0,5,7}),(32768,1,{1,5,7}),(32768,1,{2,5,7}),(32768,1,{3,5,7}),(32768,1,{4,5,7}),(32768,1,{6,7}),(32768,1,{0,6,7}),(32768,1,{1,6,7}),(32768,1,{2,6,7}),(32768,1,{3,6,7}),(32768,1,{4,6,7}),(32768,1,{5,6,7}),(32768,1,{8}),(32768,1,{0,8}),(32768,1,{1,8}),(32768,1,{0,1,8}),(32768,1,{2,8}),(32768,1,{0,2,8}),(32768,1,{1,2,8}),(32768,1,{3,8}),(32768,1,{0,3,8}),(32768,1,{1,3,8}),(32768,1,{2,3,8}),(32768,1,{4,8}),(32768,1,{0,4,8}),(32768,1,{1,4,8}),(32768,1,{2,4,8}),(32768,1,{3,4,8}),(32768,1,{5,8}),(32768,1,{0,5,8}),(32768,1,{1,5,8}),(32768,1,{2,5,8}),(32768,1,{3,5,8}),(32768,1,{4,5,8}),(32768,1,{6,8}),(32768,1,{0,6,8}),(32768,1,{1,6,8}),(32768,1,{2,6,8}),(32768,1,{3,6,8}),(32768,1,{4,6,8}),(32768,1,{5,6,8}),(32768,1,{7,8}),(32768,1,{0,7,8}),(32768,1,{1,7,8}),(32768,1,{2,7,8}),(32768,1,{3,7,8}),(32768,1,{4,7,8}),(32768,1,{5,7,8}),(32768,1,{6,7,8}),(32768,1,{9}),(32768,1,{0,9}),(32768,1,{1,9}),(32768,1,{0,1,9}),(32768,1,{2,9}),(32768,1,{0,2,9}),(32768,1,{1,2,9}),(32768,1,{3,9}),(32768,1,{0,3,9}),(32768,1,{1,3,9}),(32768,1,{2,3,9}),(32768,1,{4,9}),(32768,1,{0,4,9}),(32768,1,{1,4,9}),(32768,1,{2,4,9}),(32768,1,{3,4,9}),(32768,1,{5,9}),(32768,1,{0,5,9}),(32768,1,{1,5,9}),(32768,1,{2,5,9}),(32768,1,{3,5,9}),(32768,1,{4,5,9}),(32768,1,{6,9}),(32768,1,{0,6,9}),(32768,1,{1,6,9}),(32768,1,{2,6,9}),(32768,1,{3,6,9}),(32768,1,{4,6,9}),(32768,1,{5,6,9}),(32768,1,{0,7,9}),(32768,1,{1,7,9}),(32768,1,{2,7,9}),(32768,1,{3,7,9}),(32768,1,{5,7,9}),(32768,1,{6,7,9}),(32768,1,{8,9}),(32768,1,{0,8,9}),(32768,1,{1,8,9}),(32768,1,{2,8,9}),(32768,1,{3,8,9}),(32768,1,{4,8,9}),(32768,1,{5,8,9}),(32768,1,{6,8,9}),(32768,1,{7,8,9})]
private theorem single717_11_1_queries_exact :
    single717_11_1Signatures = single717_11_1.queries.map (fun q => N12Compact.SmallOwnerDomain.signature q.val) := by rfl

private def single717_11_1_owned_claim (index : Fin 176) : Prop :=
  let owned := N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index.val ∅
  1 ≤ owned.card → owned.card ≤ 3 →
    owned ∈ ([{4},{1,4},{7},{4,7},{1,4,7},{7,9},{4,7,9}] : List (Finset Nat)) ∨ (32768,1,owned) ∈ single717_11_1Signatures

private instance : DecidablePred single717_11_1_owned_claim := fun index => by
  unfold single717_11_1_owned_claim
  infer_instance

private theorem single717_11_1_subsets_length :
    N12Compact.SmallOwnerDomainThree.smallSubsetsThree.length = 176 := by decide +kernel

private theorem single717_11_1_owned_block0 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 0 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block1 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 1 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block2 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 2 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block3 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 3 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block4 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 4 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block5 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 5 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block6 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 6 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block7 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 7 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block8 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 8 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block9 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 9 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block10 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 10 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block11 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 11 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block12 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 12 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block13 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 13 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block14 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 14 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block15 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 15 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block16 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 16 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block17 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 17 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block18 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 18 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block19 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 19 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block20 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 20 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_owned_block21 :
    N12Compact.FiniteCheckChunks.Check single717_11_1_owned_claim 21 := by
  intro offset valid
  dsimp only [single717_11_1_owned_claim]
  fin_cases offset
  all_goals clear valid
  all_goals decide +kernel

private theorem single717_11_1_metadata :
    N12Compact.SmallOwnerDomainThree.Check single717_11_1 case717Family 1 single717_11_1Signatures := by
  change N12Compact.SmallOwnerDomainThree.Check (⟨32768,1,3,[{4},{1,4},{7},{4,7},{1,4,7},{7,9},{4,7,9}],[]⟩ : DirectSingleDomain)
    case717Family 1 single717_11_1Signatures
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro owned member low high
  obtain ⟨index, valid, equal⟩ := List.mem_iff_getElem.mp member
  have bound : index < 176 := by simpa only [single717_11_1_subsets_length] using valid
  have indexed := N12Compact.FiniteCheckChunks.sound single717_11_1_owned_claim
    (count := 22) (by decide) (by
      intro block
      fin_cases block
      · exact single717_11_1_owned_block0
      · exact single717_11_1_owned_block1
      · exact single717_11_1_owned_block2
      · exact single717_11_1_owned_block3
      · exact single717_11_1_owned_block4
      · exact single717_11_1_owned_block5
      · exact single717_11_1_owned_block6
      · exact single717_11_1_owned_block7
      · exact single717_11_1_owned_block8
      · exact single717_11_1_owned_block9
      · exact single717_11_1_owned_block10
      · exact single717_11_1_owned_block11
      · exact single717_11_1_owned_block12
      · exact single717_11_1_owned_block13
      · exact single717_11_1_owned_block14
      · exact single717_11_1_owned_block15
      · exact single717_11_1_owned_block16
      · exact single717_11_1_owned_block17
      · exact single717_11_1_owned_block18
      · exact single717_11_1_owned_block19
      · exact single717_11_1_owned_block20
      · exact single717_11_1_owned_block21
    ) (⟨index,bound⟩ : Fin 176)
  have value : N12Compact.SmallOwnerDomainThree.smallSubsetsThree.getD index ∅ = owned := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem valid, Option.getD_some]
    exact equal
  dsimp only [single717_11_1_owned_claim] at indexed
  rw [value] at indexed
  exact indexed low high

theorem single717_11_1_checked : single717_11_1.Check case717Family 1 :=
  N12Compact.SmallOwnerDomainThree.checked single717_11_1 case717Family 1
    single717_11_1Signatures single717_11_1_queries_exact (by decide) single717_11_1_metadata


end
end S12
