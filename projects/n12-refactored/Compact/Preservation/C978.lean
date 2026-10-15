import Compact.Preservation.HistoricalDictionary
import Compact.Assembly.RowIdentity

/-! Exact original active graph. `Pending` records unfinished entrance and
stage proofs. The terminal composition below is conditional, not a case completion. -/
namespace N12Compact.Preservation.C978
open S12 S12Pilot S12Completion HistoricalBank
set_option Elab.async false
noncomputable section

def family : Finset Nat := {1,2,12,48,192,256,512,2048,4096,8192,16384,33792}

def continuousScout978Domain0_0Ids : List (Fin poseCount) := [
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
    16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,
    32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,
    48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def continuousScout978Domain0_0 : List PoseLeaf := continuousScout978Domain0_0Ids.map poses

def continuousScout978Domain0_5Ids : List (Fin poseCount) := [
    64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,
    80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,
    96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,
    112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127]
def continuousScout978Domain0_5 : List PoseLeaf := continuousScout978Domain0_5Ids.map poses

def continuousScout978Domain10_0Ids : List (Fin poseCount) := [
    7801,7802,7803,7804,7805,7806,7807,7808,7809,7810,7811,7812,7813,7814,7815,7816,
    7817,7818,7819,7820,7821,7822,7823,7824,7825,7826,7827,7828,7829,7830,7831,7832,
    7833,7834,7835,7836,7837,7838,7839,7840,7841,7842,7843,7844,7845,7846,7847,7848,
    7849,7850,7851,7852,7853,7854,7855,7856,7857,7858,7859,7860,7861,7862,7863,7864]
def continuousScout978Domain10_0 : List PoseLeaf := continuousScout978Domain10_0Ids.map poses

def continuousScout978Domain10_12Ids : List (Fin poseCount) := [
    7865,7866,7867,7868,7869,7870,7871,7872,7873,7874,7875,7876,7877,7878,7879,7880,
    7881,7882,7883,7884,7885,7886,7887,7888,7889,7890,7891,7892,7893,7894,7895,7896,
    7897,7898,7899,7900,7901,7902,7903,7904,7905,7906,7907,7908,7909,7910,7911,7912,
    7913,7914,7915,7916,7917,7918,7919,7920,7921,7922,7923,7924,7925,7926,7927,7928]
def continuousScout978Domain10_12 : List PoseLeaf := continuousScout978Domain10_12Ids.map poses

def continuousScout978Domain10_13Ids : List (Fin poseCount) := [
    7929,7930,7931,7932,7933,7934,7935,7936,7937,7938,7939,7940,7941,7942,7943,7944,
    7945,7946,7947,7948,7949,7950,7951,7952,7953,7954,7955,7956,7957,7958,7959,7960,
    7961,7962,7963,7964,7965,7966,7967,7968,7969,7970,7971,7972,7973,7974,7975,7976,
    7977,7978,7979,7980,7981,7982,7983,7984,7985,7986,7987,7988]
def continuousScout978Domain10_13 : List PoseLeaf := continuousScout978Domain10_13Ids.map poses

def continuousScout978Domain11_0Ids : List (Fin poseCount) := [
    7989,7990,7991,7992,7993,7994,7995,7996,7997,7998,7999,8000,8001,8002,8003,8004,
    8005,8006,8007,8008,8009,8010,8011,8012,8013,8014,8015,8016,8017,8018,8019,8020,
    8021,8022,8023,8024,8025,8026,8027,8028,8029,8030,8031,8032,8033,8034,8035,8036,
    8037,8038,8039,8040,8041,8042,8043,8044,8045,8046,8047,8048,8049,8050,8051,8052]
def continuousScout978Domain11_0 : List PoseLeaf := continuousScout978Domain11_0Ids.map poses

def continuousScout978Domain11_14Ids : List (Fin poseCount) := [
    8053,8054,8055,8056,8057,8058,8059,8060,8061,8062,8063,8064,8065,8066,8067,8068,
    8069,8070,8071,8072,8073,8074,8075,8076,8077,8078,8079,8080,8081,8082,8083,8084,
    8085,8086,8087,8088,8089,8090,8091,8092,8093,8094,8095]
def continuousScout978Domain11_14 : List PoseLeaf := continuousScout978Domain11_14Ids.map poses

def continuousScout978Domain11_15Ids : List (Fin poseCount) := [
    8096,8097,8098]
def continuousScout978Domain11_15 : List PoseLeaf := continuousScout978Domain11_15Ids.map poses

def continuousScout978Domain11_16Ids : List (Fin poseCount) := [
    ]
def continuousScout978Domain11_16 : List PoseLeaf := continuousScout978Domain11_16Ids.map poses

def continuousScout978Domain1_0Ids : List (Fin poseCount) := [
    513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,
    529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,
    545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,
    561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576]
def continuousScout978Domain1_0 : List PoseLeaf := continuousScout978Domain1_0Ids.map poses

def continuousScout978Domain1_6Ids : List (Fin poseCount) := [
    577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,
    593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,
    609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,
    625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640]
def continuousScout978Domain1_6 : List PoseLeaf := continuousScout978Domain1_6Ids.map poses

def continuousScout978Domain1_7Ids : List (Fin poseCount) := [
    695,696,697,698,699,700,8099,8100,8101,8102,8103,8104,8105,8106,8107,8108,
    8109,8110,8111,8112,8113,8114,8115,8116,8117,8118,8119,8120,8121,8122,737,738,
    739]
def continuousScout978Domain1_7 : List PoseLeaf := continuousScout978Domain1_7Ids.map poses

def continuousScout978Domain5_0Ids : List (Fin poseCount) := [
    6683,6684,6685,6686,6687,6688,6689,6690,1197,1198,1199,1200,1201,1202,1203,1204,
    1205,1206,1207,1208,1209,1210,1211,6691,6692,6693,6694,6695,6696,1218,1219,1220,
    1221,1222,1223,1224,1225,6697,6698,6699,6700,6701,6702,6703,6704,6705,6706,6707,
    6708,6709,6710,6711,6712,6713,6714,6715,8123,8124,8125,8126,8127,8128,8129,8130]
def continuousScout978Domain5_0 : List PoseLeaf := continuousScout978Domain5_0Ids.map poses

def continuousScout978Domain5_8Ids : List (Fin poseCount) := [
    6724,6725,6726,6727,6728,8131,8132,8133,8134,8135,8136,8137,8138,8139,8140,8141,
    8142,8143,8144,8145,8146,8147,8148,8149,8150,8151,8152,8153,8154,8155,8156,8157,
    8158,8159,8160,8161,8162,8163,8164,8165,8166,8167,8168,8169,8170,8171,8172,8173,
    8174,8175,8176,8177,8178,8179,8180,8181,8182,8183,8184,8185,8186,8187,8188]
def continuousScout978Domain5_8 : List PoseLeaf := continuousScout978Domain5_8Ids.map poses

def continuousScout978Domain6_0Ids : List (Fin poseCount) := [
    8189,8190,8191,8192,8193,8194,8195,8196,8197,8198,8199,8200,8201,8202,8203,8204,
    8205,8206,8207,8208,8209,8210,8211,8212,8213,8214,8215,8216,8217,8218,8219,8220,
    8221,8222,8223,8224,8225,8226,8227,8228,8229,8230,8231,8232,8233,8234,8235,8236,
    8237,8238,8239,8240,8241,8242,8243,8244,8245,8246,8247,8248,8249,8250,8251,8252]
def continuousScout978Domain6_0 : List PoseLeaf := continuousScout978Domain6_0Ids.map poses

def continuousScout978Domain6_10Ids : List (Fin poseCount) := [
    8253,8254,8255,8256,8257,8258,8259,8260,8261,8262,8263,8264,8265,8266,8267,8268,
    8269,8270,8271,8272,8273,8274,8275,8276,8277,8278,8279,8280,8281,8282,8283,8284,
    8285,8286,8287,8288,8289,8290,8291,8292,8293,8294,8295,8296,8297,8298,8299,8300,
    8301,8302,8303,8304,8305,8306,8307,8308,8309,8310,8311,8312,8313,8314,8315,8316]
def continuousScout978Domain6_10 : List PoseLeaf := continuousScout978Domain6_10Ids.map poses

def continuousScout978Domain6_11Ids : List (Fin poseCount) := [
    8317,8318,8319,8320,8321,8322,8323,8324,8325,8326,8327,8328,8329,8330,8331,8332,
    8333,8334,8335,8336,8337,8338,8339,8340,8341,8342,8343,8344,8345,8346,8347,8348,
    8349,8350,8351,8352,8353,8354,8355,8356,8357,8358,8359,8360,8361,8362,8363,8364,
    8365,8366,8367,8368,8369,8370,8371,8372,8373,8374,8375,8376]
def continuousScout978Domain6_11 : List PoseLeaf := continuousScout978Domain6_11Ids.map poses

def continuousScout978Domain6_9Ids : List (Fin poseCount) := [
    8377,8378,8379,8380,8381,8382,8383,8384,8385,8386,8387,8388,8389,8390,8391,8392,
    8393,8394,8395,8396,8397,8398,8399,8400,8401,8402,8403,8404,8405,8406,8407,8408,
    8409,8410,8411,8412,8413,8414,8415,8416,8417,8418,8419,8420,8421,8422,8423,8424,
    8425,8426,8427,8428,8429,8430,8431,8432,8433,8434,8435,8436,8437,8438,8439,8440]
def continuousScout978Domain6_9 : List PoseLeaf := continuousScout978Domain6_9Ids.map poses

def continuousScout978Domain7_0Ids : List (Fin poseCount) := [
    8441,8442,8443,8444,7354,7355,7356,7357,7358,7359,7360,7361,7362,7363,7364,7365,
    7366,7367,7368,7369,7370,7371,7372,7373,7374,7375,7376,7377,7378,7379,7380,7381,
    7382,7383,7384,7385,7386,7387,7388,7389,7390,7391,7392,7393,7394,7395,8445,8446,
    8447,8448,8449,8450,8451,8452,8453,8454,8455,8456,8457,8458,8459,8460,8461,8462]
def continuousScout978Domain7_0 : List PoseLeaf := continuousScout978Domain7_0Ids.map poses

def continuousScout978Domain7_1Ids : List (Fin poseCount) := [
    8463,8464,8465,8466,8467,8468,8469,8470,8471,8472,8473,8474,8475,8476,8477,8478,
    8479,8480,8481,8482,8483,8484,8485,8486,8487,8488,8489,8490,8491,8492,8493,8494,
    8495,8496,8497,8498,8499,8500,8501,8502,8503,8504,8505,8506,8507,8508,8509,8510,
    8511,8512,8513,8514,8515,8516,8517,8518,8519,8520,8521,8522,8523,8524,8525,8526]
def continuousScout978Domain7_1 : List PoseLeaf := continuousScout978Domain7_1Ids.map poses

def continuousScout978Domain7_2Ids : List (Fin poseCount) := [
    8527,8528,8529,8530,8531,8532,8533,8534,8535,8536,8537,8538,8539,8540,8541,8542,
    8543,8544,8545,8546,8547,8548,8549,8550,8551,8552,8553,8554,8555,8556,8557,8558,
    8559,8560,8561,8562,8563,8564,8565,8566,8567,8568,8569,8570,8571,8572,8573,8574,
    8575,8576,8577,8578,8579,8580,8581,8582,8583,8584,8585,8586,8587,8588,8589,8590]
def continuousScout978Domain7_2 : List PoseLeaf := continuousScout978Domain7_2Ids.map poses

def continuousScout978Domain7_3Ids : List (Fin poseCount) := [
    8591,8592,8593,8594,8595,8596,8597,8598,8599,8600,8601,8602]
def continuousScout978Domain7_3 : List PoseLeaf := continuousScout978Domain7_3Ids.map poses

def continuousScout978Domain8_0Ids : List (Fin poseCount) := [
    1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,
    1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,
    1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,
    1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680]
def continuousScout978Domain8_0 : List PoseLeaf := continuousScout978Domain8_0Ids.map poses

def continuousScout978Domain8_4Ids : List (Fin poseCount) := [
    8603,8604,8605,8606,8607,8608,8609,8610,8611,8612,8613,8614,8615]
def continuousScout978Domain8_4 : List PoseLeaf := continuousScout978Domain8_4Ids.map poses

def continuousScout978Domain9_0Ids : List (Fin poseCount) := [
    1716,1717,1718,1719,1720,1721,1722,1723,1724,1725,1726,1727,1728,1729,1730,1731,
    1732,1733,1734,1735,1736,1737,1738,1739,1740,1741,1742,1743,1744,1745,1746,1747,
    1748,1749,1750,1751,1752,1753,1754,1755,1756,1757,1758,1759,1760,1761,1762,1763,
    1764,1765,1766,1767,1768,1769,8616,8617,8618,8619,8620]
def continuousScout978Domain9_0 : List PoseLeaf := continuousScout978Domain9_0Ids.map poses

structure Pending : Prop where
  initial0 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain0_0 (p.square (ownerIndex p 1))
  initial1 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain1_0 (p.square (ownerIndex p 2))
  initial5 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain5_0 (p.square (ownerIndex p 256))
  initial6 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain6_0 (p.square (ownerIndex p 512))
  initial7 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain7_0 (p.square (ownerIndex p 2048))
  initial8 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain8_0 (p.square (ownerIndex p 4096))
  initial9 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain9_0 (p.square (ownerIndex p 8192))
  initial10 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain10_0 (p.square (ownerIndex p 16384))
  initial11 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout978Domain11_0 (p.square (ownerIndex p 33792))
  /-- Original PruningCoverCheck, step0. -/
  step0 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain7_0 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain5_0 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout978Domain7_1 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step1. -/
  step1 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain7_1 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain8_0 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout978Domain7_2 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step2. -/
  step2 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain7_2 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain11_0 (p.square (ownerIndex p 33792)) →
    OrientedPoseCovered continuousScout978Domain7_3 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step3. -/
  step3 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain8_0 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout978Domain7_3 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain8_4 (p.square (ownerIndex p 4096))
  /-- Original PruningCoverCheck, step4. -/
  step4 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain0_0 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout978Domain9_0 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout978Domain0_5 (p.square (ownerIndex p 1))
  /-- Original PruningCoverCheck, step5. -/
  step5 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain1_0 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout978Domain0_5 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout978Domain1_6 (p.square (ownerIndex p 2))
  /-- Original PruningCoverCheck, step6. -/
  step6 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain1_6 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout978Domain8_4 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout978Domain1_7 (p.square (ownerIndex p 2))
  /-- Original PruningCoverCheck, step7. -/
  step7 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain5_0 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout978Domain7_3 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain5_8 (p.square (ownerIndex p 256))
  /-- Original PruningCoverCheck, step8. -/
  step8 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain6_0 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout978Domain5_8 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout978Domain6_9 (p.square (ownerIndex p 512))
  /-- Original PruningCoverCheck, step9. -/
  step9 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain6_9 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout978Domain9_0 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout978Domain6_10 (p.square (ownerIndex p 512))
  /-- Original PruningCoverCheck, step10. -/
  step10 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain6_10 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout978Domain10_0 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout978Domain6_11 (p.square (ownerIndex p 512))
  /-- Original WindowChordPruningCoverCheck, step11. -/
  step11 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain10_0 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout978Domain1_7 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout978Domain5_8 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout978Domain6_11 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout978Domain10_12 (p.square (ownerIndex p 16384))
  /-- Original PruningCoverCheck, step12. -/
  step12 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain10_12 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout978Domain6_11 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout978Domain10_13 (p.square (ownerIndex p 16384))
  /-- Original WindowChordPruningCoverCheck, step13. -/
  step13 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain11_0 (p.square (ownerIndex p 33792)) →
    OrientedPoseCovered continuousScout978Domain7_3 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain8_4 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout978Domain10_13 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout978Domain11_14 (p.square (ownerIndex p 33792))
  /-- Original PruningCoverCheck, step14. -/
  step14 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain11_14 (p.square (ownerIndex p 33792)) →
    OrientedPoseCovered continuousScout978Domain7_3 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout978Domain11_15 (p.square (ownerIndex p 33792))
  /-- Original PruningCoverCheck, step15. -/
  step15 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout978Domain11_15 (p.square (ownerIndex p 33792)) →
    OrientedPoseCovered continuousScout978Domain10_13 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout978Domain11_16 (p.square (ownerIndex p 33792))

theorem family_impossible (pending : Pending) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : False := by
  have h0 := pending.initial0 p hf
  have h1 := pending.initial1 p hf
  have h5 := pending.initial5 p hf
  have h6 := pending.initial6 p hf
  have h7 := pending.initial7 p hf
  have h8 := pending.initial8 p hf
  have h9 := pending.initial9 p hf
  have h10 := pending.initial10 p hf
  have h11 := pending.initial11 p hf
  have hstep0 := pending.step0 p hf h7 h5
  have hstep1 := pending.step1 p hf hstep0 h8
  have hstep2 := pending.step2 p hf hstep1 h11
  have hstep3 := pending.step3 p hf h8 hstep2
  have hstep4 := pending.step4 p hf h0 h9
  have hstep5 := pending.step5 p hf h1 hstep4
  have hstep6 := pending.step6 p hf hstep5 hstep3
  have hstep7 := pending.step7 p hf h5 hstep2
  have hstep8 := pending.step8 p hf h6 hstep7
  have hstep9 := pending.step9 p hf hstep8 h9
  have hstep10 := pending.step10 p hf hstep9 h10
  have hstep11 := pending.step11 p hf h10 hstep6 hstep7 hstep10
  have hstep12 := pending.step12 p hf hstep11 hstep10
  have hstep13 := pending.step13 p hf h11 hstep2 hstep3 hstep12
  have hstep14 := pending.step14 p hf hstep13 hstep2
  have hstep15 := pending.step15 p hf hstep14 hstep12
  obtain ⟨leaf,member,_⟩ := hstep15
  exact List.not_mem_nil member

private theorem row_checked :
    (RowIdentity.rowAt 509).originalId = 978 ∧
    (RowIdentity.rowAt 509).groups = family := by decide +kernel

theorem excludes_case (pending : Pending) : ExcludesCase 978 := by
  intro r hr hid p hf
  apply family_impossible pending p
  exact hf.trans (RowIdentity.family_at 509 978 family row_checked r hr hid)

#print axioms family_impossible
#print axioms excludes_case
end
end N12Compact.Preservation.C978
