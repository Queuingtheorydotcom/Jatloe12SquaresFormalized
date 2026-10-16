import Compact.Bridge.SharedLocalQueries
import Compact.Cases.C701.EntryQueryBase
import Compact.HistoricalOwnership.Queries000
import Compact.HistoricalOwnership.Queries001
import Compact.HistoricalOwnership.Queries002
import Compact.HistoricalOwnership.Queries003
import Compact.HistoricalOwnership.Queries004
import Compact.Bridge.SmallOwnerDomain

namespace S12
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def single701_0_0 : DirectSingleDomain := ⟨1,1,2,[{2}],[(certified_query% 0),(certified_query% 1),(certified_query% 2),(certified_query% 3),(certified_query% 4),(certified_query% 5),(certified_query% 6),(certified_query% 7),(certified_query% 8),(certified_query% 9),(certified_query% 10),(certified_query% 11),(certified_query% 12),(certified_query% 13),(certified_query% 14),(certified_query% 15),(certified_query% 16),(certified_query% 17),(certified_query% 18),(certified_query% 19),(certified_query% 20),(certified_query% 21),(certified_query% 22),(certified_query% 23),(certified_query% 24),(certified_query% 25),(certified_query% 26),(certified_query% 27),(certified_query% 28),(certified_query% 29),(certified_query% 30),(certified_query% 31),(certified_query% 32),(certified_query% 33),(certified_query% 34),(certified_query% 35),(certified_query% 36),(certified_query% 37),(certified_query% 38),(certified_query% 39),(certified_query% 40),(certified_query% 41),(certified_query% 42),(certified_query% 43),(certified_query% 44),(certified_query% 45),(certified_query% 46),(certified_query% 47),(certified_query% 48),(certified_query% 49),(certified_query% 50),(certified_query% 51),(certified_query% 52),(certified_query% 53)]⟩
private def single701_0_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1,0,{0}),(1,0,{1}),(1,0,{0,1}),(1,0,{0,2}),(1,0,{1,2}),(1,0,{3}),(1,0,{0,3}),(1,0,{1,3}),(1,0,{2,3}),(1,0,{4}),(1,0,{0,4}),(1,0,{1,4}),(1,0,{2,4}),(1,0,{3,4}),(1,0,{5}),(1,0,{0,5}),(1,0,{1,5}),(1,0,{2,5}),(1,0,{3,5}),(1,0,{4,5}),(1,0,{6}),(1,0,{0,6}),(1,0,{1,6}),(1,0,{2,6}),(1,0,{3,6}),(1,0,{4,6}),(1,0,{5,6}),(1,0,{7}),(1,0,{0,7}),(1,0,{1,7}),(1,0,{2,7}),(1,0,{3,7}),(1,0,{4,7}),(1,0,{5,7}),(1,0,{6,7}),(1,0,{8}),(1,0,{0,8}),(1,0,{1,8}),(1,0,{2,8}),(1,0,{3,8}),(1,0,{4,8}),(1,0,{5,8}),(1,0,{6,8}),(1,0,{7,8}),(1,0,{9}),(1,0,{0,9}),(1,0,{1,9}),(1,0,{2,9}),(1,0,{3,9}),(1,0,{4,9}),(1,0,{5,9}),(1,0,{6,9}),(1,0,{7,9}),(1,0,{8,9})]
theorem single701_0_0_checked : single701_0_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_0_0 case701Family 0
    single701_0_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_0_1 : DirectSingleDomain := ⟨1,1,1,[{2}],[(certified_query% 54),(certified_query% 55),(certified_query% 58),(certified_query% 62),(certified_query% 67),(certified_query% 73),(certified_query% 80),(certified_query% 88),(certified_query% 97)]⟩
private def single701_0_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1,1,{0}),(1,1,{1}),(1,1,{3}),(1,1,{4}),(1,1,{5}),(1,1,{6}),(1,1,{7}),(1,1,{8}),(1,1,{9})]
theorem single701_0_1_checked : single701_0_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_0_1 case701Family 1
    single701_0_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_1_0 : DirectSingleDomain := ⟨2,1,2,[{0},{0,2}],[(certified_query% 107),(certified_query% 108),(certified_query% 109),(certified_query% 110),(certified_query% 111),(certified_query% 112),(certified_query% 113),(certified_query% 114),(certified_query% 115),(certified_query% 116),(certified_query% 117),(certified_query% 118),(certified_query% 119),(certified_query% 120),(certified_query% 121),(certified_query% 122),(certified_query% 123),(certified_query% 124),(certified_query% 125),(certified_query% 126),(certified_query% 127),(certified_query% 128),(certified_query% 129),(certified_query% 130),(certified_query% 131),(certified_query% 132),(certified_query% 133),(certified_query% 134),(certified_query% 135),(certified_query% 136),(certified_query% 137),(certified_query% 138),(certified_query% 139),(certified_query% 140),(certified_query% 141),(certified_query% 142),(certified_query% 143),(certified_query% 144),(certified_query% 145),(certified_query% 146),(certified_query% 147),(certified_query% 148),(certified_query% 149),(certified_query% 150),(certified_query% 151),(certified_query% 152),(certified_query% 153),(certified_query% 154),(certified_query% 155),(certified_query% 156),(certified_query% 157),(certified_query% 158),(certified_query% 159)]⟩
private def single701_1_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(2,0,{1}),(2,0,{0,1}),(2,0,{2}),(2,0,{1,2}),(2,0,{3}),(2,0,{0,3}),(2,0,{1,3}),(2,0,{2,3}),(2,0,{4}),(2,0,{0,4}),(2,0,{1,4}),(2,0,{2,4}),(2,0,{3,4}),(2,0,{5}),(2,0,{0,5}),(2,0,{1,5}),(2,0,{2,5}),(2,0,{3,5}),(2,0,{4,5}),(2,0,{6}),(2,0,{0,6}),(2,0,{1,6}),(2,0,{2,6}),(2,0,{3,6}),(2,0,{4,6}),(2,0,{5,6}),(2,0,{7}),(2,0,{0,7}),(2,0,{1,7}),(2,0,{2,7}),(2,0,{3,7}),(2,0,{4,7}),(2,0,{5,7}),(2,0,{6,7}),(2,0,{8}),(2,0,{0,8}),(2,0,{1,8}),(2,0,{2,8}),(2,0,{3,8}),(2,0,{4,8}),(2,0,{5,8}),(2,0,{6,8}),(2,0,{7,8}),(2,0,{9}),(2,0,{0,9}),(2,0,{1,9}),(2,0,{2,9}),(2,0,{3,9}),(2,0,{4,9}),(2,0,{5,9}),(2,0,{6,9}),(2,0,{7,9}),(2,0,{8,9})]
theorem single701_1_0_checked : single701_1_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_1_0 case701Family 0
    single701_1_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_1_1 : DirectSingleDomain := ⟨2,1,1,[{0}],[(certified_query% 160),(certified_query% 162),(certified_query% 165),(certified_query% 169),(certified_query% 174),(certified_query% 180),(certified_query% 187),(certified_query% 195),(certified_query% 204)]⟩
private def single701_1_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(2,1,{1}),(2,1,{2}),(2,1,{3}),(2,1,{4}),(2,1,{5}),(2,1,{6}),(2,1,{7}),(2,1,{8}),(2,1,{9})]
theorem single701_1_1_checked : single701_1_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_1_1 case701Family 1
    single701_1_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_2_0 : DirectSingleDomain := ⟨12,0,1,[∅,{6},{8}],[N12Compact.HistoricalOwnership.Queries.query0_certified,N12Compact.HistoricalOwnership.Queries.query1_certified,N12Compact.HistoricalOwnership.Queries.query2_certified,N12Compact.HistoricalOwnership.Queries.query3_certified,N12Compact.HistoricalOwnership.Queries.query4_certified,N12Compact.HistoricalOwnership.Queries.query5_certified,N12Compact.HistoricalOwnership.Queries.query6_certified,N12Compact.HistoricalOwnership.Queries.query7_certified]⟩
private def single701_2_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(12,0,{0}),(12,0,{1}),(12,0,{2}),(12,0,{3}),(12,0,{4}),(12,0,{5}),(12,0,{7}),(12,0,{9})]
theorem single701_2_0_checked : single701_2_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_2_0 case701Family 0
    single701_2_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_2_1 : DirectSingleDomain := ⟨12,0,0,[∅],[]⟩
private def single701_2_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  []
theorem single701_2_1_checked : single701_2_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_2_1 case701Family 1
    single701_2_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_3_0 : DirectSingleDomain := ⟨16,1,2,[{7}],[(certified_query% 339),(certified_query% 340),(certified_query% 341),(certified_query% 342),(certified_query% 343),(certified_query% 344),(certified_query% 345),(certified_query% 346),(certified_query% 347),(certified_query% 348),(certified_query% 349),(certified_query% 350),(certified_query% 351),(certified_query% 352),(certified_query% 353),(certified_query% 354),(certified_query% 355),(certified_query% 356),(certified_query% 357),(certified_query% 358),(certified_query% 359),(certified_query% 360),(certified_query% 361),(certified_query% 362),(certified_query% 363),(certified_query% 364),(certified_query% 365),(certified_query% 366),(certified_query% 367),(certified_query% 368),(certified_query% 369),(certified_query% 370),(certified_query% 371),(certified_query% 372),(certified_query% 373),(certified_query% 374),(certified_query% 375),(certified_query% 376),(certified_query% 377),(certified_query% 378),(certified_query% 379),(certified_query% 380),(certified_query% 381),(certified_query% 382),(certified_query% 383),(certified_query% 384),(certified_query% 385),(certified_query% 386),(certified_query% 387),(certified_query% 388),(certified_query% 389),(certified_query% 390),(certified_query% 391),(certified_query% 392)]⟩
private def single701_3_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16,0,{0}),(16,0,{1}),(16,0,{0,1}),(16,0,{2}),(16,0,{0,2}),(16,0,{1,2}),(16,0,{3}),(16,0,{0,3}),(16,0,{1,3}),(16,0,{2,3}),(16,0,{4}),(16,0,{0,4}),(16,0,{1,4}),(16,0,{2,4}),(16,0,{3,4}),(16,0,{5}),(16,0,{0,5}),(16,0,{1,5}),(16,0,{2,5}),(16,0,{3,5}),(16,0,{4,5}),(16,0,{6}),(16,0,{0,6}),(16,0,{1,6}),(16,0,{2,6}),(16,0,{3,6}),(16,0,{4,6}),(16,0,{5,6}),(16,0,{0,7}),(16,0,{1,7}),(16,0,{2,7}),(16,0,{3,7}),(16,0,{4,7}),(16,0,{5,7}),(16,0,{6,7}),(16,0,{8}),(16,0,{0,8}),(16,0,{1,8}),(16,0,{2,8}),(16,0,{3,8}),(16,0,{4,8}),(16,0,{5,8}),(16,0,{6,8}),(16,0,{7,8}),(16,0,{9}),(16,0,{0,9}),(16,0,{1,9}),(16,0,{2,9}),(16,0,{3,9}),(16,0,{4,9}),(16,0,{5,9}),(16,0,{6,9}),(16,0,{7,9}),(16,0,{8,9})]
theorem single701_3_0_checked : single701_3_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_3_0 case701Family 0
    single701_3_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_3_1 : DirectSingleDomain := ⟨16,1,1,[{7}],[(certified_query% 393),(certified_query% 394),(certified_query% 395),(certified_query% 396),(certified_query% 397),(certified_query% 398),(certified_query% 399),(certified_query% 400),(certified_query% 401)]⟩
private def single701_3_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16,1,{0}),(16,1,{1}),(16,1,{2}),(16,1,{3}),(16,1,{4}),(16,1,{5}),(16,1,{6}),(16,1,{8}),(16,1,{9})]
theorem single701_3_1_checked : single701_3_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_3_1 case701Family 1
    single701_3_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_4_0 : DirectSingleDomain := ⟨32,1,2,[{9},{7,9}],[(certified_query% 402),(certified_query% 403),N12Compact.HistoricalOwnership.Queries.query9_certified,(certified_query% 404),N12Compact.HistoricalOwnership.Queries.query10_certified,N12Compact.HistoricalOwnership.Queries.query11_certified,(certified_query% 405),N12Compact.HistoricalOwnership.Queries.query12_certified,N12Compact.HistoricalOwnership.Queries.query13_certified,N12Compact.HistoricalOwnership.Queries.query14_certified,(certified_query% 406),N12Compact.HistoricalOwnership.Queries.query15_certified,N12Compact.HistoricalOwnership.Queries.query16_certified,N12Compact.HistoricalOwnership.Queries.query17_certified,N12Compact.HistoricalOwnership.Queries.query18_certified,(certified_query% 407),N12Compact.HistoricalOwnership.Queries.query19_certified,N12Compact.HistoricalOwnership.Queries.query20_certified,N12Compact.HistoricalOwnership.Queries.query21_certified,N12Compact.HistoricalOwnership.Queries.query22_certified,N12Compact.HistoricalOwnership.Queries.query23_certified,(certified_query% 408),N12Compact.HistoricalOwnership.Queries.query24_certified,N12Compact.HistoricalOwnership.Queries.query25_certified,N12Compact.HistoricalOwnership.Queries.query26_certified,N12Compact.HistoricalOwnership.Queries.query27_certified,N12Compact.HistoricalOwnership.Queries.query28_certified,N12Compact.HistoricalOwnership.Queries.query29_certified,(certified_query% 409),N12Compact.HistoricalOwnership.Queries.query30_certified,N12Compact.HistoricalOwnership.Queries.query31_certified,N12Compact.HistoricalOwnership.Queries.query32_certified,N12Compact.HistoricalOwnership.Queries.query33_certified,N12Compact.HistoricalOwnership.Queries.query34_certified,N12Compact.HistoricalOwnership.Queries.query35_certified,N12Compact.HistoricalOwnership.Queries.query36_certified,(certified_query% 410),N12Compact.HistoricalOwnership.Queries.query37_certified,N12Compact.HistoricalOwnership.Queries.query38_certified,N12Compact.HistoricalOwnership.Queries.query39_certified,N12Compact.HistoricalOwnership.Queries.query40_certified,N12Compact.HistoricalOwnership.Queries.query41_certified,N12Compact.HistoricalOwnership.Queries.query42_certified,N12Compact.HistoricalOwnership.Queries.query43_certified,N12Compact.HistoricalOwnership.Queries.query44_certified,N12Compact.HistoricalOwnership.Queries.query45_certified,N12Compact.HistoricalOwnership.Queries.query46_certified,N12Compact.HistoricalOwnership.Queries.query47_certified,N12Compact.HistoricalOwnership.Queries.query48_certified,N12Compact.HistoricalOwnership.Queries.query49_certified,N12Compact.HistoricalOwnership.Queries.query50_certified,N12Compact.HistoricalOwnership.Queries.query51_certified,N12Compact.HistoricalOwnership.Queries.query52_certified]⟩
private def single701_4_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32,0,{0}),(32,0,{1}),(32,0,{0,1}),(32,0,{2}),(32,0,{0,2}),(32,0,{1,2}),(32,0,{3}),(32,0,{0,3}),(32,0,{1,3}),(32,0,{2,3}),(32,0,{4}),(32,0,{0,4}),(32,0,{1,4}),(32,0,{2,4}),(32,0,{3,4}),(32,0,{5}),(32,0,{0,5}),(32,0,{1,5}),(32,0,{2,5}),(32,0,{3,5}),(32,0,{4,5}),(32,0,{6}),(32,0,{0,6}),(32,0,{1,6}),(32,0,{2,6}),(32,0,{3,6}),(32,0,{4,6}),(32,0,{5,6}),(32,0,{7}),(32,0,{0,7}),(32,0,{1,7}),(32,0,{2,7}),(32,0,{3,7}),(32,0,{4,7}),(32,0,{5,7}),(32,0,{6,7}),(32,0,{8}),(32,0,{0,8}),(32,0,{1,8}),(32,0,{2,8}),(32,0,{3,8}),(32,0,{4,8}),(32,0,{5,8}),(32,0,{6,8}),(32,0,{7,8}),(32,0,{0,9}),(32,0,{1,9}),(32,0,{2,9}),(32,0,{3,9}),(32,0,{4,9}),(32,0,{5,9}),(32,0,{6,9}),(32,0,{8,9})]
theorem single701_4_0_checked : single701_4_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_4_0 case701Family 0
    single701_4_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_4_1 : DirectSingleDomain := ⟨32,1,1,[{9}],[(certified_query% 411),(certified_query% 412),(certified_query% 413),(certified_query% 414),(certified_query% 415),(certified_query% 416),(certified_query% 417),(certified_query% 418),(certified_query% 419)]⟩
private def single701_4_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(32,1,{0}),(32,1,{1}),(32,1,{2}),(32,1,{3}),(32,1,{4}),(32,1,{5}),(32,1,{6}),(32,1,{7}),(32,1,{8})]
theorem single701_4_1_checked : single701_4_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_4_1 case701Family 1
    single701_4_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_5_0 : DirectSingleDomain := ⟨192,0,1,[∅,{1},{3}],[N12Compact.HistoricalOwnership.Queries.query53_certified,N12Compact.HistoricalOwnership.Queries.query54_certified,N12Compact.HistoricalOwnership.Queries.query55_certified,N12Compact.HistoricalOwnership.Queries.query56_certified,N12Compact.HistoricalOwnership.Queries.query57_certified,N12Compact.HistoricalOwnership.Queries.query58_certified,N12Compact.HistoricalOwnership.Queries.query59_certified,N12Compact.HistoricalOwnership.Queries.query60_certified]⟩
private def single701_5_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(192,0,{0}),(192,0,{2}),(192,0,{4}),(192,0,{5}),(192,0,{6}),(192,0,{7}),(192,0,{8}),(192,0,{9})]
theorem single701_5_0_checked : single701_5_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_5_0 case701Family 0
    single701_5_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_5_1 : DirectSingleDomain := ⟨192,0,0,[∅],[]⟩
private def single701_5_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  []
theorem single701_5_1_checked : single701_5_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_5_1 case701Family 1
    single701_5_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_6_0 : DirectSingleDomain := ⟨256,1,2,[{0},{0,1},{2},{0,2},{4},{0,4},{1,4},{2,4},{0,5},{4,5},{4,6}],[(certified_query% 429),(certified_query% 430),(certified_query% 431),(certified_query% 432),(certified_query% 433),(certified_query% 434),(certified_query% 435),(certified_query% 436),(certified_query% 437),(certified_query% 438),(certified_query% 439),(certified_query% 440),(certified_query% 441),(certified_query% 442),(certified_query% 443),(certified_query% 444),(certified_query% 445),(certified_query% 446),(certified_query% 447),(certified_query% 448),(certified_query% 449),(certified_query% 450),(certified_query% 451),(certified_query% 452),(certified_query% 453),(certified_query% 454),(certified_query% 455),(certified_query% 456),(certified_query% 457),(certified_query% 458),(certified_query% 459),(certified_query% 460),(certified_query% 461),(certified_query% 462),(certified_query% 463),(certified_query% 464),(certified_query% 465),(certified_query% 466),(certified_query% 467),(certified_query% 468),(certified_query% 469),(certified_query% 470),(certified_query% 471),(certified_query% 472)]⟩
private def single701_6_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(256,0,{1}),(256,0,{1,2}),(256,0,{3}),(256,0,{0,3}),(256,0,{1,3}),(256,0,{2,3}),(256,0,{3,4}),(256,0,{5}),(256,0,{1,5}),(256,0,{2,5}),(256,0,{3,5}),(256,0,{6}),(256,0,{0,6}),(256,0,{1,6}),(256,0,{2,6}),(256,0,{3,6}),(256,0,{5,6}),(256,0,{7}),(256,0,{0,7}),(256,0,{1,7}),(256,0,{2,7}),(256,0,{3,7}),(256,0,{4,7}),(256,0,{5,7}),(256,0,{6,7}),(256,0,{8}),(256,0,{0,8}),(256,0,{1,8}),(256,0,{2,8}),(256,0,{3,8}),(256,0,{4,8}),(256,0,{5,8}),(256,0,{6,8}),(256,0,{7,8}),(256,0,{9}),(256,0,{0,9}),(256,0,{1,9}),(256,0,{2,9}),(256,0,{3,9}),(256,0,{4,9}),(256,0,{5,9}),(256,0,{6,9}),(256,0,{7,9}),(256,0,{8,9})]
theorem single701_6_0_checked : single701_6_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_6_0 case701Family 0
    single701_6_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_6_1 : DirectSingleDomain := ⟨256,1,1,[{0},{2},{3}],[(certified_query% 473),(certified_query% 476),(certified_query% 481),(certified_query% 485),(certified_query% 490),(certified_query% 498),(certified_query% 507)]⟩
private def single701_6_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(256,1,{1}),(256,1,{4}),(256,1,{5}),(256,1,{6}),(256,1,{7}),(256,1,{8}),(256,1,{9})]
theorem single701_6_1_checked : single701_6_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_6_1 case701Family 1
    single701_6_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_7_0 : DirectSingleDomain := ⟨1536,0,1,[∅,{4},{5},{6},{7},{8},{9}],[N12Compact.HistoricalOwnership.Queries.query62_certified,N12Compact.HistoricalOwnership.Queries.query63_certified,N12Compact.HistoricalOwnership.Queries.query64_certified,N12Compact.HistoricalOwnership.Queries.query65_certified]⟩
private def single701_7_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1536,0,{0}),(1536,0,{1}),(1536,0,{2}),(1536,0,{3})]
theorem single701_7_0_checked : single701_7_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_7_0 case701Family 0
    single701_7_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_7_1 : DirectSingleDomain := ⟨1536,1,1,[{6}],[N12Compact.HistoricalOwnership.Queries.query66_certified,N12Compact.HistoricalOwnership.Queries.query67_certified,N12Compact.HistoricalOwnership.Queries.query68_certified,N12Compact.HistoricalOwnership.Queries.query69_certified,N12Compact.HistoricalOwnership.Queries.query70_certified,N12Compact.HistoricalOwnership.Queries.query71_certified,N12Compact.HistoricalOwnership.Queries.query72_certified,N12Compact.HistoricalOwnership.Queries.query73_certified,N12Compact.HistoricalOwnership.Queries.query74_certified]⟩
private def single701_7_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(1536,1,{0}),(1536,1,{1}),(1536,1,{2}),(1536,1,{3}),(1536,1,{4}),(1536,1,{5}),(1536,1,{7}),(1536,1,{8}),(1536,1,{9})]
theorem single701_7_1_checked : single701_7_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_7_1 case701Family 1
    single701_7_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_8_0 : DirectSingleDomain := ⟨4096,1,2,[{0},{1},{0,1},{0,2},{1,3}],[(certified_query% 989),(certified_query% 990),(certified_query% 991),(certified_query% 992),(certified_query% 993),(certified_query% 994),(certified_query% 995),(certified_query% 996),(certified_query% 997),(certified_query% 998),(certified_query% 999),(certified_query% 1000),(certified_query% 1001),(certified_query% 1002),(certified_query% 1003),(certified_query% 1004),(certified_query% 1005),(certified_query% 1006),(certified_query% 1007),(certified_query% 1008),(certified_query% 1009),(certified_query% 1010),(certified_query% 1011),(certified_query% 1012),(certified_query% 1013),(certified_query% 1014),(certified_query% 1015),(certified_query% 1016),(certified_query% 1017),(certified_query% 1018),(certified_query% 1019),(certified_query% 1020),(certified_query% 1021),(certified_query% 1022),(certified_query% 1023),(certified_query% 1024),(certified_query% 1025),(certified_query% 1026),(certified_query% 1027),(certified_query% 1028),(certified_query% 1029),(certified_query% 1030),(certified_query% 1031),(certified_query% 1032),(certified_query% 1033),(certified_query% 1034),(certified_query% 1035),(certified_query% 1036),(certified_query% 1037),(certified_query% 1038)]⟩
private def single701_8_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(4096,0,{2}),(4096,0,{1,2}),(4096,0,{3}),(4096,0,{0,3}),(4096,0,{2,3}),(4096,0,{4}),(4096,0,{0,4}),(4096,0,{1,4}),(4096,0,{2,4}),(4096,0,{3,4}),(4096,0,{5}),(4096,0,{0,5}),(4096,0,{1,5}),(4096,0,{2,5}),(4096,0,{3,5}),(4096,0,{4,5}),(4096,0,{6}),(4096,0,{0,6}),(4096,0,{1,6}),(4096,0,{2,6}),(4096,0,{3,6}),(4096,0,{4,6}),(4096,0,{5,6}),(4096,0,{7}),(4096,0,{0,7}),(4096,0,{1,7}),(4096,0,{2,7}),(4096,0,{3,7}),(4096,0,{4,7}),(4096,0,{5,7}),(4096,0,{6,7}),(4096,0,{8}),(4096,0,{0,8}),(4096,0,{1,8}),(4096,0,{2,8}),(4096,0,{3,8}),(4096,0,{4,8}),(4096,0,{5,8}),(4096,0,{6,8}),(4096,0,{7,8}),(4096,0,{9}),(4096,0,{0,9}),(4096,0,{1,9}),(4096,0,{2,9}),(4096,0,{3,9}),(4096,0,{4,9}),(4096,0,{5,9}),(4096,0,{6,9}),(4096,0,{7,9}),(4096,0,{8,9})]
theorem single701_8_0_checked : single701_8_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_8_0 case701Family 0
    single701_8_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_8_1 : DirectSingleDomain := ⟨4096,1,1,[{0},{1},{3}],[(certified_query% 1039),(certified_query% 1043),(certified_query% 1048),(certified_query% 1054),(certified_query% 1061),(certified_query% 1069),(certified_query% 1078)]⟩
private def single701_8_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(4096,1,{2}),(4096,1,{4}),(4096,1,{5}),(4096,1,{6}),(4096,1,{7}),(4096,1,{8}),(4096,1,{9})]
theorem single701_8_1_checked : single701_8_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_8_1 case701Family 1
    single701_8_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_9_0 : DirectSingleDomain := ⟨8192,1,2,[{2},{4},{2,4},{6},{2,6},{4,6}],[(certified_query% 1145),(certified_query% 1146),(certified_query% 1147),(certified_query% 1148),(certified_query% 1149),(certified_query% 1150),(certified_query% 1151),(certified_query% 1152),(certified_query% 1153),(certified_query% 1154),(certified_query% 1155),(certified_query% 1156),(certified_query% 1157),(certified_query% 1158),(certified_query% 1159),(certified_query% 1160),(certified_query% 1161),(certified_query% 1162),(certified_query% 1163),(certified_query% 1164),(certified_query% 1165),(certified_query% 1166),(certified_query% 1167),(certified_query% 1168),(certified_query% 1169),(certified_query% 1170),(certified_query% 1171),(certified_query% 1172),(certified_query% 1173),(certified_query% 1174),(certified_query% 1175),(certified_query% 1176),(certified_query% 1177),(certified_query% 1178),(certified_query% 1179),(certified_query% 1180),(certified_query% 1181),(certified_query% 1182),(certified_query% 1183),(certified_query% 1184),(certified_query% 1185),(certified_query% 1186),(certified_query% 1187),(certified_query% 1188),(certified_query% 1189),(certified_query% 1190),(certified_query% 1191),(certified_query% 1192),(certified_query% 1193)]⟩
private def single701_9_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(8192,0,{0}),(8192,0,{1}),(8192,0,{0,1}),(8192,0,{0,2}),(8192,0,{1,2}),(8192,0,{3}),(8192,0,{0,3}),(8192,0,{1,3}),(8192,0,{2,3}),(8192,0,{0,4}),(8192,0,{1,4}),(8192,0,{3,4}),(8192,0,{5}),(8192,0,{0,5}),(8192,0,{1,5}),(8192,0,{2,5}),(8192,0,{3,5}),(8192,0,{4,5}),(8192,0,{0,6}),(8192,0,{1,6}),(8192,0,{3,6}),(8192,0,{5,6}),(8192,0,{7}),(8192,0,{0,7}),(8192,0,{1,7}),(8192,0,{2,7}),(8192,0,{3,7}),(8192,0,{4,7}),(8192,0,{5,7}),(8192,0,{6,7}),(8192,0,{8}),(8192,0,{0,8}),(8192,0,{1,8}),(8192,0,{2,8}),(8192,0,{3,8}),(8192,0,{4,8}),(8192,0,{5,8}),(8192,0,{6,8}),(8192,0,{7,8}),(8192,0,{9}),(8192,0,{0,9}),(8192,0,{1,9}),(8192,0,{2,9}),(8192,0,{3,9}),(8192,0,{4,9}),(8192,0,{5,9}),(8192,0,{6,9}),(8192,0,{7,9}),(8192,0,{8,9})]
theorem single701_9_0_checked : single701_9_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_9_0 case701Family 0
    single701_9_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_9_1 : DirectSingleDomain := ⟨8192,1,1,[{2},{5}],[(certified_query% 1194),(certified_query% 1195),(certified_query% 1198),(certified_query% 1202),(certified_query% 1211),(certified_query% 1218),(certified_query% 1226),(certified_query% 1234)]⟩
private def single701_9_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(8192,1,{0}),(8192,1,{1}),(8192,1,{3}),(8192,1,{4}),(8192,1,{6}),(8192,1,{7}),(8192,1,{8}),(8192,1,{9})]
theorem single701_9_1_checked : single701_9_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_9_1 case701Family 1
    single701_9_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_10_0 : DirectSingleDomain := ⟨16384,1,2,[{8},{6,8},{9},{7,9},{8,9}],[(certified_query% 1294),(certified_query% 1295),(certified_query% 1296),(certified_query% 1297),(certified_query% 1298),(certified_query% 1299),(certified_query% 1300),(certified_query% 1301),(certified_query% 1302),(certified_query% 1303),(certified_query% 1304),(certified_query% 1305),(certified_query% 1306),(certified_query% 1307),(certified_query% 1308),(certified_query% 1309),(certified_query% 1310),(certified_query% 1311),(certified_query% 1312),(certified_query% 1313),(certified_query% 1314),(certified_query% 1315),(certified_query% 1316),(certified_query% 1317),(certified_query% 1318),(certified_query% 1319),(certified_query% 1320),(certified_query% 1321),(certified_query% 1322),(certified_query% 1323),(certified_query% 1324),(certified_query% 1325),(certified_query% 1326),(certified_query% 1327),(certified_query% 1328),(certified_query% 1329),(certified_query% 1330),(certified_query% 1331),(certified_query% 1332),(certified_query% 1333),(certified_query% 1334),(certified_query% 1335),(certified_query% 1336),(certified_query% 1337),(certified_query% 1338),(certified_query% 1339),(certified_query% 1340),(certified_query% 1341),(certified_query% 1342),(certified_query% 1343)]⟩
private def single701_10_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16384,0,{0}),(16384,0,{1}),(16384,0,{0,1}),(16384,0,{2}),(16384,0,{0,2}),(16384,0,{1,2}),(16384,0,{3}),(16384,0,{0,3}),(16384,0,{1,3}),(16384,0,{2,3}),(16384,0,{4}),(16384,0,{0,4}),(16384,0,{1,4}),(16384,0,{2,4}),(16384,0,{3,4}),(16384,0,{5}),(16384,0,{0,5}),(16384,0,{1,5}),(16384,0,{2,5}),(16384,0,{3,5}),(16384,0,{4,5}),(16384,0,{6}),(16384,0,{0,6}),(16384,0,{1,6}),(16384,0,{2,6}),(16384,0,{3,6}),(16384,0,{4,6}),(16384,0,{5,6}),(16384,0,{7}),(16384,0,{0,7}),(16384,0,{1,7}),(16384,0,{2,7}),(16384,0,{3,7}),(16384,0,{4,7}),(16384,0,{5,7}),(16384,0,{6,7}),(16384,0,{0,8}),(16384,0,{1,8}),(16384,0,{2,8}),(16384,0,{3,8}),(16384,0,{4,8}),(16384,0,{5,8}),(16384,0,{7,8}),(16384,0,{0,9}),(16384,0,{1,9}),(16384,0,{2,9}),(16384,0,{3,9}),(16384,0,{4,9}),(16384,0,{5,9}),(16384,0,{6,9})]
theorem single701_10_0_checked : single701_10_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_10_0 case701Family 0
    single701_10_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_10_1 : DirectSingleDomain := ⟨16384,1,1,[{6},{8},{9}],[(certified_query% 1344),(certified_query% 1345),(certified_query% 1347),(certified_query% 1350),(certified_query% 1354),(certified_query% 1359),(certified_query% 1371)]⟩
private def single701_10_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(16384,1,{0}),(16384,1,{1}),(16384,1,{2}),(16384,1,{3}),(16384,1,{4}),(16384,1,{5}),(16384,1,{7})]
theorem single701_10_1_checked : single701_10_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_10_1 case701Family 1
    single701_10_1Signatures (by rfl) (by decide) (by decide +kernel)

def single701_11_0 : DirectSingleDomain := ⟨34816,1,2,[{3},{1,3},{5},{0,5},{1,5},{3,5},{4,5},{7},{3,7},{5,7}],[N12Compact.HistoricalOwnership.Queries.query75_certified,N12Compact.HistoricalOwnership.Queries.query76_certified,N12Compact.HistoricalOwnership.Queries.query77_certified,N12Compact.HistoricalOwnership.Queries.query78_certified,N12Compact.HistoricalOwnership.Queries.query79_certified,N12Compact.HistoricalOwnership.Queries.query80_certified,N12Compact.HistoricalOwnership.Queries.query81_certified,N12Compact.HistoricalOwnership.Queries.query82_certified,N12Compact.HistoricalOwnership.Queries.query83_certified,N12Compact.HistoricalOwnership.Queries.query84_certified,N12Compact.HistoricalOwnership.Queries.query85_certified,N12Compact.HistoricalOwnership.Queries.query86_certified,N12Compact.HistoricalOwnership.Queries.query87_certified,N12Compact.HistoricalOwnership.Queries.query88_certified,N12Compact.HistoricalOwnership.Queries.query89_certified,N12Compact.HistoricalOwnership.Queries.query90_certified,N12Compact.HistoricalOwnership.Queries.query91_certified,N12Compact.HistoricalOwnership.Queries.query92_certified,N12Compact.HistoricalOwnership.Queries.query93_certified,N12Compact.HistoricalOwnership.Queries.query94_certified,N12Compact.HistoricalOwnership.Queries.query95_certified,N12Compact.HistoricalOwnership.Queries.query96_certified,N12Compact.HistoricalOwnership.Queries.query97_certified,N12Compact.HistoricalOwnership.Queries.query98_certified,N12Compact.HistoricalOwnership.Queries.query99_certified,N12Compact.HistoricalOwnership.Queries.query100_certified,N12Compact.HistoricalOwnership.Queries.query101_certified,N12Compact.HistoricalOwnership.Queries.query102_certified,N12Compact.HistoricalOwnership.Queries.query103_certified,N12Compact.HistoricalOwnership.Queries.query104_certified,N12Compact.HistoricalOwnership.Queries.query105_certified,N12Compact.HistoricalOwnership.Queries.query106_certified,N12Compact.HistoricalOwnership.Queries.query107_certified,N12Compact.HistoricalOwnership.Queries.query108_certified,N12Compact.HistoricalOwnership.Queries.query109_certified,N12Compact.HistoricalOwnership.Queries.query110_certified,N12Compact.HistoricalOwnership.Queries.query111_certified,N12Compact.HistoricalOwnership.Queries.query112_certified,N12Compact.HistoricalOwnership.Queries.query113_certified,N12Compact.HistoricalOwnership.Queries.query114_certified,N12Compact.HistoricalOwnership.Queries.query115_certified,N12Compact.HistoricalOwnership.Queries.query116_certified,N12Compact.HistoricalOwnership.Queries.query117_certified,N12Compact.HistoricalOwnership.Queries.query118_certified,N12Compact.HistoricalOwnership.Queries.query119_certified]⟩
private def single701_11_0Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(34816,0,{0}),(34816,0,{1}),(34816,0,{0,1}),(34816,0,{2}),(34816,0,{0,2}),(34816,0,{1,2}),(34816,0,{0,3}),(34816,0,{2,3}),(34816,0,{4}),(34816,0,{0,4}),(34816,0,{1,4}),(34816,0,{2,4}),(34816,0,{3,4}),(34816,0,{2,5}),(34816,0,{6}),(34816,0,{0,6}),(34816,0,{1,6}),(34816,0,{2,6}),(34816,0,{3,6}),(34816,0,{4,6}),(34816,0,{5,6}),(34816,0,{0,7}),(34816,0,{1,7}),(34816,0,{2,7}),(34816,0,{4,7}),(34816,0,{6,7}),(34816,0,{8}),(34816,0,{0,8}),(34816,0,{1,8}),(34816,0,{2,8}),(34816,0,{3,8}),(34816,0,{4,8}),(34816,0,{5,8}),(34816,0,{6,8}),(34816,0,{7,8}),(34816,0,{9}),(34816,0,{0,9}),(34816,0,{1,9}),(34816,0,{2,9}),(34816,0,{3,9}),(34816,0,{4,9}),(34816,0,{5,9}),(34816,0,{6,9}),(34816,0,{7,9}),(34816,0,{8,9})]
theorem single701_11_0_checked : single701_11_0.Check case701Family 0 :=
  N12Compact.SmallOwnerDomain.checked single701_11_0 case701Family 0
    single701_11_0Signatures (by rfl) (by decide) (by decide +kernel)

def single701_11_1 : DirectSingleDomain := ⟨34816,1,1,[{1},{3},{4}],[N12Compact.HistoricalOwnership.Queries.query120_certified,N12Compact.HistoricalOwnership.Queries.query121_certified,N12Compact.HistoricalOwnership.Queries.query122_certified,N12Compact.HistoricalOwnership.Queries.query123_certified,N12Compact.HistoricalOwnership.Queries.query124_certified,N12Compact.HistoricalOwnership.Queries.query125_certified,N12Compact.HistoricalOwnership.Queries.query126_certified]⟩
private def single701_11_1Signatures : List N12Compact.SmallOwnerDomain.Signature :=
  [(34816,1,{0}),(34816,1,{2}),(34816,1,{5}),(34816,1,{6}),(34816,1,{7}),(34816,1,{8}),(34816,1,{9})]
theorem single701_11_1_checked : single701_11_1.Check case701Family 1 :=
  N12Compact.SmallOwnerDomain.checked single701_11_1 case701Family 1
    single701_11_1Signatures (by rfl) (by decide) (by decide +kernel)


end
end S12
