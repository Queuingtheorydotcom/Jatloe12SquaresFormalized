import Compact.Preservation.HistoricalDictionary
import Compact.Assembly.RowIdentity

/-! Exact original active graph. `Pending` records unfinished entrance and
stage proofs. The terminal composition below is conditional, not a case completion. -/
namespace N12Compact.Preservation.C973
open S12 S12Pilot S12Completion HistoricalBank
set_option Elab.async false
noncomputable section

def family : Finset Nat := {1,2,12,48,192,256,512,1024,2048,4096,16384,32768}

def continuousScout973Domain0_0Ids : List (Fin poseCount) := [
    0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
    16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,
    32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,
    48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def continuousScout973Domain0_0 : List PoseLeaf := continuousScout973Domain0_0Ids.map poses

def continuousScout973Domain0_19Ids : List (Fin poseCount) := [
    5910,5911,66,67,68,69,5912,5913,5914,5915,5916,5917,5918,5919,5920,5921,
    5922,5923,5924,5925,5926,5927,5928,5929,5930,5931,5932,5933,5934,5935,5936,5937,
    5938,5939,5940,5941,5942,5943,5944,5945,5946,5947,5948,5949,5950,5951,5952,5953,
    5954,5955,5956,5957,5958,5959,5960,5961,5962,5963,5964,5965]
def continuousScout973Domain0_19 : List PoseLeaf := continuousScout973Domain0_19Ids.map poses

def continuousScout973Domain10_0Ids : List (Fin poseCount) := [
    5966,5967,5968,5969,5970,5971,5972,5973,5974,5975,5976,5977,5978,5979,5980,5981,
    5982,5983,5984,5985,5986,5987,5988,5989,5990,5991,5992,5993,5994,5995,5996,5997,
    5998,5999,6000,6001,6002,6003,6004,6005,6006,6007,6008,6009,6010,6011,6012,6013,
    6014,6015,6016,6017,6018,6019,6020,6021,6022,6023,6024,6025,6026,6027,6028,6029]
def continuousScout973Domain10_0 : List PoseLeaf := continuousScout973Domain10_0Ids.map poses

def continuousScout973Domain10_11Ids : List (Fin poseCount) := [
    6030,6031,6032,6033,6034,6035,6036,6037,6038,6039,6040,6041,6042,6043,6044,6045,
    6046,6047,6048,6049,6050,6051,6052,6053,6054,6055,6056,6057,6058,6059,6060,6061,
    6062,6063,6064,6065,6066,6067,6068,6069,6070,6071,6072,6073,6074,6075,6076,6077,
    6078,6079,6080,6081,6082,6083,6084,6085,6086,6087,6088,6089,6090,6091,6092,6093]
def continuousScout973Domain10_11 : List PoseLeaf := continuousScout973Domain10_11Ids.map poses

def continuousScout973Domain10_17Ids : List (Fin poseCount) := [
    6094,6095,6096,6097,6098,6099,6100,6101,6102,6103,6104,6105,6106,6107,6108,6109,
    6110,6111,6112,6113,6114,6115,6116,6117,6118,6119,6120,6121,6122,6123,6124,6125,
    6126,6127,6128,6129,6130,6131,6132,6133,6134,6135,6136,6137,6138]
def continuousScout973Domain10_17 : List PoseLeaf := continuousScout973Domain10_17Ids.map poses

def continuousScout973Domain10_26Ids : List (Fin poseCount) := [
    6139,6140,6141,6142,6143,6144,6145,6146,6147,6148,6149,6150,6151,6152,6153,6154,
    6155,6156,6157,6158,6159,6160,6161,6162,6163]
def continuousScout973Domain10_26 : List PoseLeaf := continuousScout973Domain10_26Ids.map poses

def continuousScout973Domain10_27Ids : List (Fin poseCount) := [
    6164,6165,6166,6167,6168,6169,6170,6171,6172,6173,6174,6175,6176,6177,6178,6179,
    6180,6181,6182,6183,6184,6185]
def continuousScout973Domain10_27 : List PoseLeaf := continuousScout973Domain10_27Ids.map poses

def continuousScout973Domain10_28Ids : List (Fin poseCount) := [
    ]
def continuousScout973Domain10_28 : List PoseLeaf := continuousScout973Domain10_28Ids.map poses

def continuousScout973Domain10_4Ids : List (Fin poseCount) := [
    6186,6187,6188,6189,6190,6191,6192,6193,6194,6195,6196,6197,6198,6199,6200,6201,
    6202,6203,6204,6205,6206,6207,6208,6209,6210,6211,6212,6213,6214,6215,6216,6217,
    6218,6219,6220,6221,6222,6223,6224,6225,6226,6227,6228,6229,6230,6231,6232,6233,
    6234,6235,6236,6237,6238,6239,6240,6241,6242,6243,6244,6245,6246,6247,6248,6249]
def continuousScout973Domain10_4 : List PoseLeaf := continuousScout973Domain10_4Ids.map poses

def continuousScout973Domain11_0Ids : List (Fin poseCount) := [
    6250,6251,6252,6253,6254,6255,6256,6257,6258,6259,6260,6261,6262,6263,6264,6265,
    6266,6267,6268,6269,6270,6271,6272,6273,6274,6275,6276,6277,6278,6279,6280,6281,
    6282,6283,6284,6285,6286,6287,6288,6289,6290,6291,6292,6293,6294,6295,6296,6297,
    6298,6299,6300,6301,6302,6303,6304,6305,6306,6307,6308,6309,6310,6311,6312,6313]
def continuousScout973Domain11_0 : List PoseLeaf := continuousScout973Domain11_0Ids.map poses

def continuousScout973Domain11_18Ids : List (Fin poseCount) := [
    6314,6315,6316,6317,6318,6319,6320,6321,6322,6323,6324,6325,6326,6327,6328,6329,
    6330,6331,6332,6333,6334,6335,6336,6337,6338,6339,6340,6341,6342,6343,6344,6345,
    6346,6347,6348,6349,6350,6351,6352,6353,6354,6355,6356,6357,6358,6359,6360,6361,
    6362,6363,6364,6365,6366,6367,6368,6369,6370,6371,6372,6373,6374,6375,6376,6377]
def continuousScout973Domain11_18 : List PoseLeaf := continuousScout973Domain11_18Ids.map poses

def continuousScout973Domain1_0Ids : List (Fin poseCount) := [
    513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,
    529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,
    545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,
    561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576]
def continuousScout973Domain1_0 : List PoseLeaf := continuousScout973Domain1_0Ids.map poses

def continuousScout973Domain1_20Ids : List (Fin poseCount) := [
    577,6378,6379,6380,6381,582,583,584,6382,6383,6384,6385,6386,6387,6388,6389,
    6390,6391,6392,6393,6394,6395,6396,6397,6398,6399,6400,6401,605,606,6402,6403,
    6404,6405,6406,6407,6408,6409,6410,6411,6412,6413,6414,6415,6416,6417,6418,6419,
    6420,6421,6422,6423,6424,6425,6426,6427,6428,6429,635,636,637,638,639,640]
def continuousScout973Domain1_20 : List PoseLeaf := continuousScout973Domain1_20Ids.map poses

def continuousScout973Domain3_0Ids : List (Fin poseCount) := [
    6430,6431,6432,6433,6434,6435,6436,6437,6438,6439,6440,6441,6442,6443,6444,6445,
    6446,6447,6448,6449,6450,6451,6452,6453,6454,6455,6456,6457,6458,6459,6460,6461,
    6462,6463,6464,6465,6466,6467,6468,6469,6470,6471,6472,6473,6474,6475,6476,6477,
    6478,6479,6480,6481,6482,6483,6484,6485,6486,6487,6488,6489,6490,6491,6492,6493]
def continuousScout973Domain3_0 : List PoseLeaf := continuousScout973Domain3_0Ids.map poses

def continuousScout973Domain3_12Ids : List (Fin poseCount) := [
    6494,6495,6496,6497,6498,6499,6500,6501,6502,6503,6504,6505,6506,6507,6508,6509,
    6510,6511,6512,6513,6514,6515,6516,6517,6518,6519,6520,6521,6522,6523,6524,6525,
    6526,6527,6528,6529,6530,6531,6532,6533,6534,6535,6536,6537,6538,6539,6540,6541,
    6542,6543,6544,6545,6546,6547,6548,6549,6550,6551,6552,6553,6554,6555,6556,6557]
def continuousScout973Domain3_12 : List PoseLeaf := continuousScout973Domain3_12Ids.map poses

def continuousScout973Domain3_13Ids : List (Fin poseCount) := [
    6558,6559,6560,6561,6562,6563,6564,6565,6566,6567,6568,6569,6570,6571,6572,6573,
    6574,6575,6576,6577,6578,6579,6580,6581,6582,6583,6584,6585,6586,6587,6588,6589,
    6590,6591,6592,6593,6594,6595,6596,6597,6598,6599,6600,6601,6602,6603,6604,6605,
    6606,6607,6608,6609,6610,6611,6612,6613,6614,6615,6616,6617,6618,6619,6620,6621]
def continuousScout973Domain3_13 : List PoseLeaf := continuousScout973Domain3_13Ids.map poses

def continuousScout973Domain4_0Ids : List (Fin poseCount) := [
    1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,
    1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,
    1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,
    1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188]
def continuousScout973Domain4_0 : List PoseLeaf := continuousScout973Domain4_0Ids.map poses

def continuousScout973Domain4_14Ids : List (Fin poseCount) := [
    6622,6623,6624,6625,6626,6627,6628,6629,6630,6631,6632,6633,6634,6635,6636,6637,
    6638,6639,6640,6641,6642,6643,6644,6645,6646,6647,6648,6649,6650,6651,6652,6653,
    6654,6655,6656,6657,6658,6659,6660,6661,6662,6663,6664,6665,6666,6667,6668,6669,
    6670,6671,6672,6673,6674,6675,6676,6677,6678,6679,6680,6681,6682]
def continuousScout973Domain4_14 : List PoseLeaf := continuousScout973Domain4_14Ids.map poses

def continuousScout973Domain5_0Ids : List (Fin poseCount) := [
    6683,6684,6685,6686,6687,6688,6689,6690,1197,1198,1199,1200,1201,1202,1203,1204,
    1205,1206,1207,1208,1209,1210,1211,6691,6692,6693,6694,6695,6696,1218,1219,1220,
    1221,1222,1223,1224,1225,6697,6698,6699,6700,6701,6702,6703,6704,6705,6706,6707,
    6708,6709,6710,6711,6712,6713,6714,6715,6716,6717,6718,6719,6720,6721,6722,6723]
def continuousScout973Domain5_0 : List PoseLeaf := continuousScout973Domain5_0Ids.map poses

def continuousScout973Domain5_15Ids : List (Fin poseCount) := [
    6724,6725,6726,6727,6728,6729,6730,6731,6732,6733,6734,6735,6736,6737,6738,6739,
    6740,6741,6742,6743,6744,6745,6746,6747,6748,6749,6750,6751,6752,6753,6754,6755,
    6756,6757,6758,6759,6760,6761,6762,6763,6764,6765,6766,6767,6768,6769,6770,6771,
    6772,6773,6774,6775,6776,6777,6778,6779,6780,6781,6782,6783,6784,6785,6786]
def continuousScout973Domain5_15 : List PoseLeaf := continuousScout973Domain5_15Ids.map poses

def continuousScout973Domain5_21Ids : List (Fin poseCount) := [
    6787,6788,6789,6790,6791,6792,6793,6794,6795,6796,6797,6798,6799,6800,6801,6802,
    6803,6804,6805,6806,6807,6808,6809,6810,6811,6812,6813,6814,6815,6816,6817,6818,
    6819,6820,6821,6822,6823,6824,6825,6826,6827,6828,6829,6830,6831,6832,6833,6834,
    6835,6836,6837,6838,6839,6840,6841,6842,6843,6844,6845,6846,6847,6848,6849]
def continuousScout973Domain5_21 : List PoseLeaf := continuousScout973Domain5_21Ids.map poses

def continuousScout973Domain5_22Ids : List (Fin poseCount) := [
    6850,6851,6852,6853,6854,6855,6856,6857,6858,6859,6860,6861,6862,6863,6864,6865,
    6866,6867,6868,6869,6870,6871,6872,6873,6874,6875,6876,6877,6878,6879,6880,6881,
    6882,6883,6884,6885,6886,6887,6888,6889,6890,6891,6892]
def continuousScout973Domain5_22 : List PoseLeaf := continuousScout973Domain5_22Ids.map poses

def continuousScout973Domain6_0Ids : List (Fin poseCount) := [
    6893,6894,6895,6896,6897,6898,6899,6900,6901,6902,6903,6904,6905,6906,6907,6908,
    6909,6910,6911,6912,6913,6914,6915,6916,6917,6918,6919,6920,6921,6922,6923,6924,
    6925,6926,6927,6928,6929,6930,6931,6932,6933,6934,6935,6936,6937,6938,6939,6940,
    6941,6942,6943,6944,6945,6946,6947,6948,6949,6950,6951,6952,6953,6954,6955,6956]
def continuousScout973Domain6_0 : List PoseLeaf := continuousScout973Domain6_0Ids.map poses

def continuousScout973Domain6_23Ids : List (Fin poseCount) := [
    6957,6958,6959,6960,6961,6962,6963,6964,6965,6966,6967,6968,6969,6970,6971,6972,
    6973,6974,6975,6976,6977,6978,6979,6980,6981,6982,6983,6984,6985,6986,6987,6988,
    6989,6990,6991,6992,6993,6994,6995,6996,6997,6998,6999,7000,7001,7002,7003,7004,
    7005,7006,7007,7008,7009,7010,7011,7012,7013,7014,7015,7016,7017,7018,7019,7020]
def continuousScout973Domain6_23 : List PoseLeaf := continuousScout973Domain6_23Ids.map poses

def continuousScout973Domain6_24Ids : List (Fin poseCount) := [
    7021,7022,7023,7024,7025,7026,7027,7028,7029]
def continuousScout973Domain6_24 : List PoseLeaf := continuousScout973Domain6_24Ids.map poses

def continuousScout973Domain7_0Ids : List (Fin poseCount) := [
    7030,7031,7032,7033,7034,7035,7036,7037,7038,7039,7040,7041,7042,7043,7044,7045,
    7046,7047,7048,7049,7050,7051,7052,7053,7054,7055,7056,7057,7058,7059,7060,7061,
    7062,7063,7064,7065,7066,7067,7068,7069,7070,7071,7072,7073,7074,7075,7076,7077,
    7078,7079,7080,7081,7082,7083,7084,7085,7086,7087,7088,7089,7090,7091,7092,7093]
def continuousScout973Domain7_0 : List PoseLeaf := continuousScout973Domain7_0Ids.map poses

def continuousScout973Domain7_5Ids : List (Fin poseCount) := [
    7094,7095,7096,7097,7098,7099,7100,7101,7102,7103,7104,7105,7106,7107,7108,7109,
    7110,7111,7112,7113,7114,7115,7116,7117,7118,7119,7120,7121,7122,7123,7124,7125,
    7126,7127,7128,7129,7130,7131,7132,7133,7134,7135,7136,7137,7138,7139,7140,7141,
    7142,7143,7144,7145,7146,7147,7148,7149,7150,7151,7152,7153,7154,7155,7156,7157]
def continuousScout973Domain7_5 : List PoseLeaf := continuousScout973Domain7_5Ids.map poses

def continuousScout973Domain7_6Ids : List (Fin poseCount) := [
    7158,7159,7160,7161,7162,7163,7164,7165,7166,7167,7168,7169,7170,7171,7172,7173,
    7174,7175,7176,7177,7178,7179,7180,7181,7182,7183,7184,7185,7186,7187,7188,7189,
    7190,7191,7192,7193,7194,7195,7196,7197,7198,7199,7200,7201,7202,7203,7204,7205,
    7206,7207,7208,7209,7210,7211,7212,7213,7214,7215,7216,7217,7218,7219,7220,7221]
def continuousScout973Domain7_6 : List PoseLeaf := continuousScout973Domain7_6Ids.map poses

def continuousScout973Domain7_7Ids : List (Fin poseCount) := [
    7222,7223,7224,7225,7226,7227,7228,7229,7230,7231,7232,7233,7234,7235,7236,7237,
    7238,7239,7240,7241,7242,7243,7244,7245,7246,7247,7248,7249,7250,7251,7252,7253,
    7254,7255,7256,7257,7258,7259,7260,7261,7262,7263,7264,7265,7266,7267,7268,7269,
    7270,7271,7272,7273,7274,7275,7276,7277,7278,7279,7280,7281,7282,7283,7284,7285]
def continuousScout973Domain7_7 : List PoseLeaf := continuousScout973Domain7_7Ids.map poses

def continuousScout973Domain7_8Ids : List (Fin poseCount) := [
    7286,7287,7288,7289,7290,7291,7292,7293,7294,7295,7296,7297,7298,7299,7300,7301,
    7302,7303,7304,7305,7306,7307,7308,7309,7310,7311,7312,7313,7314,7315,7316,7317,
    7318,7319,7320,7321,7322,7323,7324,7325,7326,7327,7328,7329,7330,7331,7332,7333,
    7334,7335,7336,7337,7338,7339,7340,7341,7342,7343,7344,7345,7346,7347,7348,7349]
def continuousScout973Domain7_8 : List PoseLeaf := continuousScout973Domain7_8Ids.map poses

def continuousScout973Domain8_0Ids : List (Fin poseCount) := [
    7350,7351,7352,7353,7354,7355,7356,7357,7358,7359,7360,7361,7362,7363,7364,7365,
    7366,7367,7368,7369,7370,7371,7372,7373,7374,7375,7376,7377,7378,7379,7380,7381,
    7382,7383,7384,7385,7386,7387,7388,7389,7390,7391,7392,7393,7394,7395,7396,7397,
    7398,7399,7400,7401,7402,7403,7404,7405,7406,7407,7408,7409,7410,7411,7412,7413]
def continuousScout973Domain8_0 : List PoseLeaf := continuousScout973Domain8_0Ids.map poses

def continuousScout973Domain8_1Ids : List (Fin poseCount) := [
    7414,7415,7416,7417,7418,7419,7420,7421,7422,7423,7424,7425,7426,7427,7428,7429,
    7430,7431,7432,7433,7434,7435,7436,7437,7438,7439,7440,7441,7442,7443,7444,7445,
    7446,7447,7448,7449,7450,7451,7452,7453,7454,7455,7456,7457,7458,7459,7460,7461,
    7462,7463,7464,7465,7466,7467,7468,7469,7470,7471,7472,7473,7474,7475,7476,7477]
def continuousScout973Domain8_1 : List PoseLeaf := continuousScout973Domain8_1Ids.map poses

def continuousScout973Domain8_10Ids : List (Fin poseCount) := [
    7478,7479,7480,7481,7482,7483,7484,7485,7486,7487,7488,7489,7490,7491,7492,7493,
    7494,7495,7496,7497,7498,7499,7500,7501,7502,7503,7504,7505,7506,7507,7508,7509,
    7510,7511,7512,7513,7514,7515,7516,7517,7518,7519,7520,7521,7522,7523,7524,7525,
    7526,7527,7528,7529,7530,7531]
def continuousScout973Domain8_10 : List PoseLeaf := continuousScout973Domain8_10Ids.map poses

def continuousScout973Domain8_16Ids : List (Fin poseCount) := [
    7532,7533,7534,7535,7536,7537,7538,7539,7540,7541,7542,7543,7544,7545,7546,7547,
    7548,7549,7550,7551,7552,7553,7554,7555,7556,7557,7558,7559,7560,7561,7562,7563,
    7564,7565,7566,7567,7568,7569,7570,7571,7572,7573,7574,7575,7576,7577,7578,7579,
    7580,7581,7582,7583,7584,7585]
def continuousScout973Domain8_16 : List PoseLeaf := continuousScout973Domain8_16Ids.map poses

def continuousScout973Domain8_2Ids : List (Fin poseCount) := [
    7586,7587,7588,7589,7590,7591,7592,7593,7594,7595,7596,7597,7598,7599,7600,7601,
    7602,7603,7604,7605,7606,7607,7608,7609,7610,7611,7612,7613,7614,7615,7616,7617,
    7618,7619,7620,7621,7622,7623,7624,7625,7626,7627,7628,7629,7630,7631,7632,7633,
    7634,7635,7636,7637,7638,7639,7640,7641,7642,7643,7644,7645,7646,7647,7648,7649]
def continuousScout973Domain8_2 : List PoseLeaf := continuousScout973Domain8_2Ids.map poses

def continuousScout973Domain8_25Ids : List (Fin poseCount) := [
    7650,7651,7652,7653,7654,7655,7656,7657,7658,7659,7660,7661,7662,7663,7664,7665,
    7666,7667,7668,7669,7670,7671,7672,7673,7674,7675,7676,7677,7678,7679,7680,7681,
    7682,7683,7684,7685,7686,7687,7688,7689,7690,7691,7692,7693,7694,7695,7696,7697,
    7698,7699,7700]
def continuousScout973Domain8_25 : List PoseLeaf := continuousScout973Domain8_25Ids.map poses

def continuousScout973Domain8_9Ids : List (Fin poseCount) := [
    7701,7702,7703,7704,7705,7706,7707,7708,7709,7710,7711,7712,7713,7714,7715,7716,
    7717,7718,7719,7720,7721,7722,7723,7724,7725,7726,7727,7728,7729,7730,7731,7732,
    7733,7734,7735,7736,7737,7738,7739,7740,7741,7742,7743,7744,7745,7746,7747,7748,
    7749,7750,7751,7752,7753,7754]
def continuousScout973Domain8_9 : List PoseLeaf := continuousScout973Domain8_9Ids.map poses

def continuousScout973Domain9_0Ids : List (Fin poseCount) := [
    1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1635,1636,1637,
    1638,1639,1640,1641,1642,1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,
    1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,
    1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680]
def continuousScout973Domain9_0 : List PoseLeaf := continuousScout973Domain9_0Ids.map poses

def continuousScout973Domain9_3Ids : List (Fin poseCount) := [
    7755,7756,7757,7758,7759,7760,7761,7762,7763,7764,7765,7766,7767,7768,7769,7770,
    7771,7772,7773,7774,7775,7776,7777,7778,7779,7780,7781,7782,7783,7784,7785,7786,
    7787,7788,7789,7790,7791,7792,7793,7794,7795,7796,7797,7798,7799,7800]
def continuousScout973Domain9_3 : List PoseLeaf := continuousScout973Domain9_3Ids.map poses

structure Pending : Prop where
  initial0 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain0_0 (p.square (ownerIndex p 1))
  initial1 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain1_0 (p.square (ownerIndex p 2))
  initial3 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain3_0 (p.square (ownerIndex p 48))
  initial4 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain4_0 (p.square (ownerIndex p 192))
  initial5 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain5_0 (p.square (ownerIndex p 256))
  initial6 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain6_0 (p.square (ownerIndex p 512))
  initial7 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain7_0 (p.square (ownerIndex p 1024))
  initial8 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain8_0 (p.square (ownerIndex p 2048))
  initial9 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain9_0 (p.square (ownerIndex p 4096))
  initial10 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain10_0 (p.square (ownerIndex p 16384))
  initial11 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout973Domain11_0 (p.square (ownerIndex p 32768))
  /-- Original PruningCoverCheck, step0. -/
  step0 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain8_0 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain9_0 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain8_1 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step1. -/
  step1 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain8_1 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain11_0 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout973Domain8_2 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step2. -/
  step2 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain9_0 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain1_0 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096))
  /-- Original PruningCoverCheck, step3. -/
  step3 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain10_0 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain6_0 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout973Domain10_4 (p.square (ownerIndex p 16384))
  /-- Original PruningCoverCheck, step4. -/
  step4 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain7_0 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain5_0 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain7_5 (p.square (ownerIndex p 1024))
  /-- Original PruningCoverCheck, step5. -/
  step5 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain7_5 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain6_0 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout973Domain7_6 (p.square (ownerIndex p 1024))
  /-- Original PruningCoverCheck, step6. -/
  step6 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain7_6 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain8_2 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain7_7 (p.square (ownerIndex p 1024))
  /-- Original PruningCoverCheck, step7. -/
  step7 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain7_7 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain10_4 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024))
  /-- Original PruningCoverCheck, step8. -/
  step8 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain8_2 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain8_9 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step9. -/
  step9 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain8_9 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048))
  /-- Original WindowChordPruningCoverCheck, step10. -/
  step10 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain10_4 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain10_11 (p.square (ownerIndex p 16384))
  /-- Original WindowChordPruningCoverCheck, step11. -/
  step11 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain3_0 (p.square (ownerIndex p 48)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain3_12 (p.square (ownerIndex p 48))
  /-- Original PruningCoverCheck, step12. -/
  step12 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain3_12 (p.square (ownerIndex p 48)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain3_13 (p.square (ownerIndex p 48))
  /-- Original PruningCoverCheck, step13. -/
  step13 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain4_0 (p.square (ownerIndex p 192)) →
    OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain4_14 (p.square (ownerIndex p 192))
  /-- Original PruningCoverCheck, step14. -/
  step14 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain5_0 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain5_15 (p.square (ownerIndex p 256))
  /-- Original WindowChordPruningCoverCheck, step15. -/
  step15 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain8_10 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain3_13 (p.square (ownerIndex p 48)) →
    OrientedPoseCovered continuousScout973Domain4_14 (p.square (ownerIndex p 192)) →
    OrientedPoseCovered continuousScout973Domain11_0 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout973Domain8_16 (p.square (ownerIndex p 2048))
  /-- Original PruningCoverCheck, step16. -/
  step16 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain10_11 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain10_17 (p.square (ownerIndex p 16384))
  /-- Original PruningCoverCheck, step17. -/
  step17 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain11_0 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout973Domain3_13 (p.square (ownerIndex p 48)) →
    OrientedPoseCovered continuousScout973Domain11_18 (p.square (ownerIndex p 32768))
  /-- Original PruningCoverCheck, step18. -/
  step18 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain0_0 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout973Domain5_15 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain0_19 (p.square (ownerIndex p 1))
  /-- Original PruningCoverCheck, step19. -/
  step19 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain1_0 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout973Domain0_19 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout973Domain1_20 (p.square (ownerIndex p 2))
  /-- Original PruningCoverCheck, step20. -/
  step20 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain5_15 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain1_20 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout973Domain5_21 (p.square (ownerIndex p 256))
  /-- Original PruningCoverCheck, step21. -/
  step21 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain5_21 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain8_16 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain5_22 (p.square (ownerIndex p 256))
  /-- Original PruningCoverCheck, step22. -/
  step22 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain6_0 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout973Domain5_22 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain6_23 (p.square (ownerIndex p 512))
  /-- Original PruningCoverCheck, step23. -/
  step23 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain6_23 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout973Domain10_17 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain6_24 (p.square (ownerIndex p 512))
  /-- Original PruningCoverCheck, step24. -/
  step24 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain8_16 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain11_18 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout973Domain8_25 (p.square (ownerIndex p 2048))
  /-- Original WindowChordPruningCoverCheck, step25. -/
  step25 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain10_17 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain1_20 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout973Domain5_22 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout973Domain6_24 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout973Domain10_26 (p.square (ownerIndex p 16384))
  /-- Original WindowChordPruningCoverCheck, step26. -/
  step26 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain10_26 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain7_8 (p.square (ownerIndex p 1024)) →
    OrientedPoseCovered continuousScout973Domain8_25 (p.square (ownerIndex p 2048)) →
    OrientedPoseCovered continuousScout973Domain9_3 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout973Domain10_27 (p.square (ownerIndex p 16384))
  /-- Original PruningCoverCheck, step27. -/
  step27 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout973Domain10_27 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout973Domain6_24 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout973Domain10_28 (p.square (ownerIndex p 16384))

theorem family_impossible (pending : Pending) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : False := by
  have h0 := pending.initial0 p hf
  have h1 := pending.initial1 p hf
  have h3 := pending.initial3 p hf
  have h4 := pending.initial4 p hf
  have h5 := pending.initial5 p hf
  have h6 := pending.initial6 p hf
  have h7 := pending.initial7 p hf
  have h8 := pending.initial8 p hf
  have h9 := pending.initial9 p hf
  have h10 := pending.initial10 p hf
  have h11 := pending.initial11 p hf
  have hstep0 := pending.step0 p hf h8 h9
  have hstep1 := pending.step1 p hf hstep0 h11
  have hstep2 := pending.step2 p hf h9 h1
  have hstep3 := pending.step3 p hf h10 h6
  have hstep4 := pending.step4 p hf h7 h5
  have hstep5 := pending.step5 p hf hstep4 h6
  have hstep6 := pending.step6 p hf hstep5 hstep1
  have hstep7 := pending.step7 p hf hstep6 hstep3
  have hstep8 := pending.step8 p hf hstep1 hstep7
  have hstep9 := pending.step9 p hf hstep8 hstep2
  have hstep10 := pending.step10 p hf hstep3 hstep7 hstep9 hstep2
  have hstep11 := pending.step11 p hf h3 hstep7 hstep9 hstep2
  have hstep12 := pending.step12 p hf hstep11 hstep7
  have hstep13 := pending.step13 p hf h4 hstep2
  have hstep14 := pending.step14 p hf h5 hstep9
  have hstep15 := pending.step15 p hf hstep9 hstep12 hstep13 h11
  have hstep16 := pending.step16 p hf hstep10 hstep7
  have hstep17 := pending.step17 p hf h11 hstep12
  have hstep18 := pending.step18 p hf h0 hstep14
  have hstep19 := pending.step19 p hf h1 hstep18
  have hstep20 := pending.step20 p hf hstep14 hstep19
  have hstep21 := pending.step21 p hf hstep20 hstep15
  have hstep22 := pending.step22 p hf h6 hstep21
  have hstep23 := pending.step23 p hf hstep22 hstep16
  have hstep24 := pending.step24 p hf hstep15 hstep17
  have hstep25 := pending.step25 p hf hstep16 hstep19 hstep21 hstep23
  have hstep26 := pending.step26 p hf hstep25 hstep7 hstep24 hstep2
  have hstep27 := pending.step27 p hf hstep26 hstep23
  obtain ⟨leaf,member,_⟩ := hstep27
  exact List.not_mem_nil member

private theorem row_checked :
    (RowIdentity.rowAt 504).originalId = 973 ∧
    (RowIdentity.rowAt 504).groups = family := by decide +kernel

theorem excludes_case (pending : Pending) : ExcludesCase 973 := by
  intro r hr hid p hf
  apply family_impossible pending p
  exact hf.trans (RowIdentity.family_at 504 973 family row_checked r hr hid)

#print axioms family_impossible
#print axioms excludes_case
end
end N12Compact.Preservation.C973
