import Compact.Preservation.HistoricalDictionary
import Compact.Assembly.RowIdentity

/-! Exact original active graph. `Pending` records unfinished entrance and
stage proofs. The terminal composition below is conditional, not a case completion. -/
namespace N12Compact.Preservation.C717
open S12 S12Pilot S12Completion HistoricalBank
set_option Elab.async false
noncomputable section

def family : Finset Nat := {1,2,12,16,32,192,768,3072,4096,8192,16384,32768}

def continuousScout717Domain0_0Ids : List (Fin poseCount) := [
    1939,1940,1941,1942,1943,1944,1945,1946,1947,1948,1949,1950,1951,1952,1953,1954,
    1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,
    1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,
    1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,
    2003,2004,2005,2006,2007,2008,2009,2010,2011,2012,2013,2014,2015,2016,2017,2018,
    2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,
    2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2050,
    2051,2052,2053,2054,2055,2056,2057,2058,2059,2060,2061,2062,2063,2064,2065,2066]
def continuousScout717Domain0_0 : List PoseLeaf := continuousScout717Domain0_0Ids.map poses

def continuousScout717Domain0_1Ids : List (Fin poseCount) := [
    2067,3860,3861,3862,3863,3864,3865,3866,3867,3868,3869,3870,3871,3872,3873,3874,
    3875,3876,3877,3878,3879,3880,3881,3882,3883,3884,3885,3886,3887,3888,3889,3890,
    3891,3892,3893,3894,3895,3896,3897,3898,3899,3900,3901,3902,3903,3904,3905,3906,
    3907,3908,3909,3910,3911,3912,3913,3914,3915,3916,3917,3918,3919,3920,3921,3922,
    3923,3924,3925,3926,3927,3928,3929,3930,3931,3932,3933,3934,3935,3936,3937,3938,
    3939,3940,3941,3942,3943,3944,3945,3946,3947,3948,3949,3950,3951,3952,3953,3954,
    3955,3956,3957,3958,3959,3960,3961,3962,3963,3964,3965,3966,3967,3968,3969,3970,
    3971,3972,3973,3974,3975,3976,3977,3978,3979,3980,3981,3982,3983,3984,3985,2194]
def continuousScout717Domain0_1 : List PoseLeaf := continuousScout717Domain0_1Ids.map poses

def continuousScout717Domain0_14Ids : List (Fin poseCount) := [
    3986,3987,3988,3989,3990,3991,3992,3993,3994,3995,3996,3997,3998,3999,4000,4001,
    4002,4003,4004,4005,4006,4007,4008,4009,4010,4011,4012,4013,4014,4015,4016,4017,
    4018,4019,4020,4021,4022,4023,4024,4025,4026,4027,4028,4029,4030,4031,4032,4033,
    4034,4035,4036,4037,4038,4039,4040,4041,4042,4043,4044,4045,4046,4047,4048,4049,
    4050,4051,4052,4053,4054,4055,4056,4057,4058,4059,4060,4061,4062,4063,4064,4065,
    4066,4067,4068,4069,4070,4071,4072,4073,4074,4075,4076,4077,4078,4079,4080,4081,
    4082,4083,4084,4085,4086,4087,4088,4089,4090,4091,4092,4093,4094,4095,4096,4097,
    4098]
def continuousScout717Domain0_14 : List PoseLeaf := continuousScout717Domain0_14Ids.map poses

def continuousScout717Domain0_15Ids : List (Fin poseCount) := [
    4099,4100,4101,4102,4103,4104,4105,4106,4107,4108,4109,4110,4111,4112,4113,4114,
    4115,4116,4117,4118,4119,4120,4121,4122,4123,4124,4125,4126,4127,4128,4129,4130,
    4131,4132,4133,4134,4135,4136,4137,4138,4139,4140,4141,4142,4143,4144,4145]
def continuousScout717Domain0_15 : List PoseLeaf := continuousScout717Domain0_15Ids.map poses

def continuousScout717Domain10_0Ids : List (Fin poseCount) := [
    2195,2196,2197,2198,2199,2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,
    2211,2212,2213,4146,4147,4148,2217,2218,2219,2220,2221,2222,2223,2224,2225,2226,
    2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,
    2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,
    2259,2260,2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,
    2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287,2288,2289,2290,
    2291,2292,2293,2294,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,
    2307]
def continuousScout717Domain10_0 : List PoseLeaf := continuousScout717Domain10_0Ids.map poses

def continuousScout717Domain11_0Ids : List (Fin poseCount) := [
    2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321,2322,2323,
    2324,2325,2326,2327,2328,2329,2330,2331,2332,2333,2334,2335,2336,2337,2338,2339,
    2340,2341,2342,2343,2344,2345,2346,2347,2348,2349,2350,2351,2352,2353,2354,2355,
    2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367,2368,2369,2370,2371,
    2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,4149,4150,2387,
    2388,2389,2390,2391,2392,2393,2394,2395,2396,2397,2398,2399,2400,2401,2402,2403,
    2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2417,2418,2419,
    2420,2421]
def continuousScout717Domain11_0 : List PoseLeaf := continuousScout717Domain11_0Ids.map poses

def continuousScout717Domain1_0Ids : List (Fin poseCount) := [
    2422,2423,2424,2425,2426,2427,2428,2429,2430,2431,2432,2433,2434,2435,2436,2437,
    2438,2439,2440,2441,2442,2443,2444,2445,2446,2447,2448,2449,2450,2451,2452,2453,
    2454,2455,2456,2457,2458,2459,2460,2461,2462,2463,2464,2465,2466,2467,2468,2469,
    2470,2471,2472,2473,2474,2475,2476,2477,2478,2479,2480,2481,2482,2483,2484,2485,
    2486,2487,2488,2489,2490,2491,2492,2493,2494,2495,2496,2497,2498,2499,2500,2501,
    2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514,2515,2516,2517,
    2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,
    2534,2535,2536,2537,2538,2539,2540,2541,2542,2543,2544,2545,2546,2547,2548,2549]
def continuousScout717Domain1_0 : List PoseLeaf := continuousScout717Domain1_0Ids.map poses

def continuousScout717Domain1_2Ids : List (Fin poseCount) := [
    2550,4151,4152,4153,4154,4155,4156,4157,4158,4159,4160,4161,4162,4163,4164,4165,
    4166,4167,4168,4169,4170,4171,4172,4173,4174,4175,4176,4177,4178,4179,4180,4181,
    4182,4183,4184,4185,4186,4187,4188,4189,4190,4191,4192,4193,4194,4195,4196,4197,
    4198,4199,4200,4201,4202,4203,4204,4205,4206,4207,4208,4209,4210,4211,4212,4213,
    4214,4215,4216,4217,4218,4219,4220,4221,4222,4223,4224,4225,4226,4227,4228,4229,
    4230,4231,4232,4233,4234,4235,4236,4237,4238,4239,4240,4241,4242,4243,4244,4245,
    4246,4247,4248,4249,4250,4251,4252,4253,4254,4255,4256,4257,4258,4259,4260,4261,
    4262,4263,4264,4265,4266,4267,4268,4269,4270,4271,4272,4273,4274,4275,4276,2669]
def continuousScout717Domain1_2 : List PoseLeaf := continuousScout717Domain1_2Ids.map poses

def continuousScout717Domain2_0Ids : List (Fin poseCount) := [
    4277,4278,4279,4280,4281,4282,4283,4284,4285,4286,4287,4288,4289,4290,4291,4292,
    4293,4294,4295,4296,4297,4298,4299,4300,4301,4302,4303,4304,4305,4306,4307,4308,
    4309,4310,4311,4312,4313,4314,4315,4316,4317,4318,4319,4320,4321,4322,4323,4324,
    4325,4326,4327,4328,4329,4330,4331,4332,4333,4334,4335,4336,4337,4338,4339,4340,
    4341,4342,4343,4344,4345,4346,4347,4348,4349,4350,4351,4352,4353,4354,4355,4356,
    4357,4358,4359,4360,4361,4362,4363,4364,4365,4366,4367,4368,4369,4370,4371,4372,
    4373,4374,4375,4376,4377,4378,4379,4380,4381,4382,4383,4384,4385,4386,4387,4388,
    4389,4390,4391,4392,4393,4394,4395,4396,4397,4398,4399,4400,4401,4402,4403,4404]
def continuousScout717Domain2_0 : List PoseLeaf := continuousScout717Domain2_0Ids.map poses

def continuousScout717Domain2_3Ids : List (Fin poseCount) := [
    4405,4406,4407,4408,4409,4410,4411,4412,4413,4414,4415,4416,4417,4418,4419,4420,
    4421,4422,4423,4424,4425,4426,4427,4428,4429,4430,4431,4432,4433,4434,4435,4436,
    4437,4438,4439,4440,4441,4442,4443,4444,4445,4446,4447,4448,4449,4450,4451,4452,
    4453,4454,4455,4456,4457,4458,4459,4460,4461,4462,4463,4464,4465,4466,4467,4468,
    4469,4470,4471,4472,4473,4474,4475,4476,4477,4478,4479,4480,4481,4482,4483,4484,
    4485,4486,4487,4488,4489,4490,4491,4492,4493,4494,4495,4496,4497,4498]
def continuousScout717Domain2_3 : List PoseLeaf := continuousScout717Domain2_3Ids.map poses

def continuousScout717Domain3_0Ids : List (Fin poseCount) := [
    4499,4500,4501,4502,4503,4504,4505,4506,4507,4508,4509,4510,4511,4512,4513,4514,
    4515,4516,4517,4518,4519,4520,4521,4522,4523,4524,4525,4526,4527,4528,4529,4530,
    4531,4532,4533,4534,4535,4536,4537,4538,4539,4540,4541,4542,4543,4544,4545,4546,
    4547,4548,4549,4550,4551,4552,4553,4554,4555,4556,4557,4558,4559,4560,4561,4562,
    4563,4564,4565,4566,4567,4568,4569,4570,4571,4572,4573,4574,4575,4576,4577,4578,
    4579,4580,4581,4582,4583,4584,4585,4586,4587,4588,4589,4590,4591,4592,4593,4594,
    4595,4596,4597,4598,4599,4600,4601,4602,4603,4604,4605,4606,4607,4608,4609,4610,
    4611,4612,4613,4614,4615,4616,4617,4618,4619,4620,4621,4622,4623,4624,4625,4626]
def continuousScout717Domain3_0 : List PoseLeaf := continuousScout717Domain3_0Ids.map poses

def continuousScout717Domain3_16Ids : List (Fin poseCount) := [
    4627,4628,4629,4630,4631,4632,4633,4634,4635,4636,4637,4638,4639,4640,4641,4642,
    4643,4644,4645,4646,4647,4648,4649,4650,4651,4652,4653,4654,4655,4656,4657,4658,
    4659,4660,4661,4662,4663,4664,4665,4666,4667,4668,4669,4670,4671,4672,4673,4674,
    4675,4676,4677,4678,4679,4680,4681,4682,4683,4684,4685,4686,4687,4688,4689,4690,
    4691,4692,4693,4694,4695,4696,4697,4698,4699,4700,4701,4702,4703,4704,4705,4706,
    4707,4708,4709,4710,4711,4712,4713,4714,4715,4716,4717,4718,4719,4720,4721,4722,
    4723,4724,4725,4726,4727,4728,4729,4730,4731,4732,4733,4734,4735,4736,4737,4738,
    4739]
def continuousScout717Domain3_16 : List PoseLeaf := continuousScout717Domain3_16Ids.map poses

def continuousScout717Domain3_17Ids : List (Fin poseCount) := [
    4740,4741,4742,4743,4744,4745,4746]
def continuousScout717Domain3_17 : List PoseLeaf := continuousScout717Domain3_17Ids.map poses

def continuousScout717Domain3_4Ids : List (Fin poseCount) := [
    4747,4748,4749,4750,4751,4752,4753,4754,4755,4756,4757,4758,4759,4760,4761,4762,
    4763,4764,4765,4766,4767,4768,4769,4770,4771,4772,4773,4774,4775,4776,4777,4778,
    4779,4780,4781,4782,4783,4784,4785,4786,4787,4788,4789,4790,4791,4792,4793,4794,
    4795,4796,4797,4798,4799,4800,4801,4802,4803,4804,4805,4806,4807,4808,4809,4810,
    4811,4812,4813,4814,4815,4816,4817,4818,4819,4820,4821,4822,4823,4824,4825,4826,
    4827,4828,4829,4830,4831,4832,4833,4834,4835,4836,4837,4838,4839,4840,4841,4842,
    4843,4844,4845,4846,4847,4848,4849,4850,4851,4852,4853,4854,4855,4856,4857,4858,
    4859,4860,4861,4862,4863,4864,4865,4866,4867,4868,4869,4870,4871,4872,4873,4874]
def continuousScout717Domain3_4 : List PoseLeaf := continuousScout717Domain3_4Ids.map poses

def continuousScout717Domain4_0Ids : List (Fin poseCount) := [
    4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4886,4887,4888,4889,4890,
    4891,4892,4893,4894,4895,4896,4897,4898,4899,4900,4901,4902,4903,4904,4905,4906,
    4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4919,4920,4921,4922,
    4923,4924,4925,4926,4927,4928,4929,4930,4931,4932,4933,4934,4935,4936,4937,4938,
    4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4953,4954,
    4955,4956,4957,4958,4959,4960,4961,4962,4963,4964,4965,4966,4967,4968,4969,4970,
    4971,4972,4973,4974,4975,4976,4977,4978,4979,4980,4981,4982,4983,4984,4985,4986,
    4987,4988,4989,4990,4991,4992,4993,4994,4995,4996,4997,4998,4999,5000,5001,5002]
def continuousScout717Domain4_0 : List PoseLeaf := continuousScout717Domain4_0Ids.map poses

def continuousScout717Domain4_5Ids : List (Fin poseCount) := [
    5003,5004,5005,5006,5007,5008,5009,5010,5011,5012,5013,5014,5015,5016,5017,5018,
    5019,5020,5021,5022,5023,5024,5025,5026,5027,5028,5029,5030,5031,5032,5033,5034,
    5035,5036,5037,5038,5039,5040,5041,5042,5043,5044,5045,5046,5047,5048,5049,5050,
    5051,5052,5053,5054,5055,5056,5057,5058,5059,5060,5061,5062,5063,5064,5065,5066,
    5067,5068,5069,5070,5071,5072,5073,5074,5075,5076,5077,5078,5079,5080,5081,5082,
    5083,5084,5085,5086,5087,5088,5089,5090,5091,5092,5093,5094,5095,5096,5097,5098,
    5099,5100,5101,5102,5103,5104,5105,5106,5107,5108,5109,5110,5111,5112,5113,5114,
    5115,5116,5117,5118,5119,5120,5121,5122,5123,5124,5125,5126,5127,5128,5129,5130]
def continuousScout717Domain4_5 : List PoseLeaf := continuousScout717Domain4_5Ids.map poses

def continuousScout717Domain6_0Ids : List (Fin poseCount) := [
    5131,5132,5133,5134,5135,5136,5137,5138,5139,5140,5141,5142,5143,5144,5145,5146,
    5147,5148,5149,5150,5151,5152,5153,5154,5155,5156,5157,5158,5159,5160,5161,5162,
    5163,5164,5165,5166,5167,5168,5169,5170,5171,5172,5173,5174,5175,5176,5177,5178,
    5179,5180,5181,5182,5183,5184,5185,5186,5187,5188,5189,5190,5191,5192,5193,5194,
    5195,5196,5197,5198,5199,5200,5201,5202,5203,5204,5205,5206,5207,5208,5209,5210,
    5211,5212,5213,5214,5215,5216,5217,5218,5219,5220,5221,5222,5223,5224,5225,5226,
    5227,5228,5229,5230,5231,5232,5233,5234,5235,5236,5237,5238,5239,5240,5241,5242,
    5243,5244,5245,5246,5247,5248,5249,5250,5251,5252,5253,5254,5255,5256,5257,5258]
def continuousScout717Domain6_0 : List PoseLeaf := continuousScout717Domain6_0Ids.map poses

def continuousScout717Domain6_18Ids : List (Fin poseCount) := [
    5259,5260,5261,5262,5263,5264,5265,5266,5267,5268,5269,5270,5271,5272,5273,5274]
def continuousScout717Domain6_18 : List PoseLeaf := continuousScout717Domain6_18Ids.map poses

def continuousScout717Domain6_19Ids : List (Fin poseCount) := [
    ]
def continuousScout717Domain6_19 : List PoseLeaf := continuousScout717Domain6_19Ids.map poses

def continuousScout717Domain6_6Ids : List (Fin poseCount) := [
    5275,5276,5277,5278,5279,5280,5281,5282,5283,5284,5285,5286,5287,5288,5289,5290,
    5291,5292,5293,5294,5295,5296,5297,5298,5299,5300,5301,5302,5303,5304,5305,5306,
    5307,5308,5309,5310,5311,5312,5313,5314,5315,5316,5317,5318,5319,5320,5321,5322,
    5323,5324,5325,5326,5327,5328,5329,5330,5331,5332,5333,5334,5335,5336,5337,5338,
    5339,5340,5341,5342,5343,5344,5345,5346,5347,5348,5349,5350,5351,5352,5353,5354,
    5355,5356,5357,5358,5359,5360,5361,5362,5363,5364,5365,5366,5367,5368,5369,5370,
    5371,5372,5373,5374,5375,5376,5377,5378,5379,5380,5381,5382,5383,5384,5385,5386,
    5387,5388,5389,5390,5391,5392,5393,5394,5395,5396,5397,5398,5399,5400,5401,5402]
def continuousScout717Domain6_6 : List PoseLeaf := continuousScout717Domain6_6Ids.map poses

def continuousScout717Domain6_7Ids : List (Fin poseCount) := [
    5403,5404,5405,5406,5407,5408,5409,5410,5411,5412,5413,5414,5415,5416,5417,5418,
    5419,5420,5421,5422,5423,5424,5425,5426,5427,5428,5429,5430,5431,5432,5433,5434,
    5435,5436,5437,5438,5439,5440,5441,5442,5443,5444,5445,5446,5447,5448,5449,5450,
    5451,5452,5453,5454,5455,5456,5457,5458,5459,5460,5461,5462,5463,5464,5465,5466,
    5467,5468,5469]
def continuousScout717Domain6_7 : List PoseLeaf := continuousScout717Domain6_7Ids.map poses

def continuousScout717Domain6_8Ids : List (Fin poseCount) := [
    5470,5471,5472,5473,5474,5475,5476,5477,5478,5479,5480,5481,5482,5483,5484,5485,
    5486,5487,5488,5489,5490,5491,5492,5493,5494,5495,5496]
def continuousScout717Domain6_8 : List PoseLeaf := continuousScout717Domain6_8Ids.map poses

def continuousScout717Domain7_0Ids : List (Fin poseCount) := [
    5497,5498,5499,5500,5501,5502,5503,5504,5505,5506,5507,5508,5509,5510,5511,5512,
    5513,5514,5515,5516,5517,5518,5519,5520,5521,5522,5523,5524,5525,5526,5527,5528,
    5529,5530,5531,5532,5533,5534,5535,5536,5537,5538,5539,5540,5541,5542,5543,5544,
    5545,5546,5547,5548,5549,5550,5551,5552,5553,5554,5555,5556,5557,5558,5559,5560,
    5561,5562,5563,5564,5565,5566,5567,5568,5569,5570,5571,5572,5573,5574,5575,5576,
    5577,5578,5579,5580,5581,5582,5583,5584,5585,5586,5587,5588,5589,5590,5591,5592,
    5593,5594,5595,5596,5597,5598,5599,5600,5601,5602,5603,5604,5605,5606,5607,5608,
    5609,5610,5611,5612,5613,5614,5615,5616,5617,5618,5619,5620,5621,5622,5623,5624]
def continuousScout717Domain7_0 : List PoseLeaf := continuousScout717Domain7_0Ids.map poses

def continuousScout717Domain7_10Ids : List (Fin poseCount) := [
    5625,5626,5627,5628,5629,5630,5631,5632,5633,5634,5635,5636,5637,5638,5639,5640,
    5641,5642]
def continuousScout717Domain7_10 : List PoseLeaf := continuousScout717Domain7_10Ids.map poses

def continuousScout717Domain7_11Ids : List (Fin poseCount) := [
    5643,5644,5645,5646,5647,5648,5649,5650,5651,5652,5653]
def continuousScout717Domain7_11 : List PoseLeaf := continuousScout717Domain7_11Ids.map poses

def continuousScout717Domain7_9Ids : List (Fin poseCount) := [
    5654,5655,5656,5657,5658,5659,5660,5661,5662,5663,5664,5665,5666,5667,5668,5669,
    5670,5671,5672,5673,5674,5675,5676,5677,5678,5679,5680,5681,5682,5683,5684,5685,
    5686,5687,5688,5689,5690,5691,5692,5693,5694,5695,5696,5697,5698,5699,5700,5701,
    5702,5703,5704,5705,5706,5707,5708,5709,5710,5711,5712,5713,5714,5715,5716,5717,
    5718,5719,5720,5721,5722,5723,5724,5725,5726,5727,5728,5729,5730,5731,5732,5733,
    5734,5735,5736,5737,5738,5739,5740,5741,5742,5743,5744,5745,5746,5747,5748,5749,
    5750,5751,5752,5753,5754,5755,5756,5757,5758,5759,5760,5761,5762,5763,5764,5765,
    5766,5767,5768,5769,5770,5771,5772,5773,5774,5775,5776,5777,5778,5779,5780,5781]
def continuousScout717Domain7_9 : List PoseLeaf := continuousScout717Domain7_9Ids.map poses

def continuousScout717Domain8_0Ids : List (Fin poseCount) := [
    3529,3530,3531,3532,3533,3534,3535,3536,3537,3538,3539,3540,3541,3542,3543,3544,
    3545,3546,3547,5782,5783,5784,3551,3552,3553,3554,3555,3556,3557,3558,3559,3560,
    3561,3562,3563,3564,3565,3566,3567,3568,3569,3570,3571,3572,3573,3574,3575,3576,
    3577,3578,3579,3580,3581,3582,3583,3584,3585,3586,3587,3588,3589,3590,3591,3592,
    3593,3594,3595,3596,3597,3598,3599,3600,3601,3602,3603,3604,3605,3606,3607,3608,
    3609,3610,3611,3612,3613,3614,3615,3616,3617,3618,3619,3620,3621,3622,3623,3624,
    3625,3626,3627,3628,3629,3630,3631,3632,3633,3634,3635,3636,3637,3638,3639,3640,
    3641]
def continuousScout717Domain8_0 : List PoseLeaf := continuousScout717Domain8_0Ids.map poses

def continuousScout717Domain9_0Ids : List (Fin poseCount) := [
    3746,3747,3748,3749,3750,3751,3752,3753,3754,3755,3756,3757,3758,3759,3760,3761,
    3762,3763,3764,3765,3766,3767,3768,3769,3770,3771,3772,3773,3774,3775,3776,3777,
    3778,3779,3780,3781,3782,3783,3784,3785,3786,3787,3788,3789,3790,3791,3792,3793,
    3794,3795,3796,3797,3798,3799,3800,3801,3802,3803,3804,3805,3806,3807,3808,3809,
    3810,3811,3812,3813,3814,3815,3816,3817,3818,3819,3820,3821,3822,3823,3824,3825,
    3826,3827,3828,3829,3830,3831,3832,3833,3834,3835,3836,3837,3838,3839,3840,3841,
    3842,3843,3844,3845,3846,3847,3848,3849,3850,3851,3852,3853,3854,3855,3856,3857,
    3858,3859]
def continuousScout717Domain9_0 : List PoseLeaf := continuousScout717Domain9_0Ids.map poses

def continuousScout717Domain9_12Ids : List (Fin poseCount) := [
    5785,5786,5787,5788,5789,5790,5791,5792,5793,5794,5795,5796,5797,5798,5799,5800,
    5801,5802,5803,5804,5805,5806,5807,5808,5809,5810,5811,5812,5813,5814,5815,5816,
    5817,5818,5819,5820,5821,5822,5823,5824,5825,5826,5827,5828,5829,5830,5831,5832,
    5833,5834,5835,5836,5837,5838,5839,5840,5841,5842,5843,5844,5845,5846,5847,5848,
    5849,5850,5851,5852,5853,5854,5855,5856,5857,5858,5859,5860,5861,5862,5863,5864,
    5865,5866,5867,5868,5869,5870,5871,5872,5873,5874,5875,5876,5877,5878,5879,5880,
    5881,5882,5883,5884,5885,5886,5887,5888]
def continuousScout717Domain9_12 : List PoseLeaf := continuousScout717Domain9_12Ids.map poses

def continuousScout717Domain9_13Ids : List (Fin poseCount) := [
    5889,5890,5891,5892,5893,5894,5895,5896,5897,5898,5899,5900,5901,5902,5903,5904,
    5905,5906,5907,5908,5909]
def continuousScout717Domain9_13 : List PoseLeaf := continuousScout717Domain9_13Ids.map poses

structure Pending : Prop where
  initial0 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain0_0 (p.square (ownerIndex p 1))
  initial1 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain1_0 (p.square (ownerIndex p 2))
  initial2 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain2_0 (p.square (ownerIndex p 12))
  initial3 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain3_0 (p.square (ownerIndex p 16))
  initial4 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain4_0 (p.square (ownerIndex p 32))
  initial6 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain6_0 (p.square (ownerIndex p 768))
  initial7 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain7_0 (p.square (ownerIndex p 3072))
  initial8 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain8_0 (p.square (ownerIndex p 4096))
  initial9 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain9_0 (p.square (ownerIndex p 8192))
  initial10 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain10_0 (p.square (ownerIndex p 16384))
  initial11 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain11_0 (p.square (ownerIndex p 32768))
  /-- Original PruningCoverCheck, step0. -/
  step0 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain0_0 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout717Domain1_0 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout717Domain0_1 (p.square (ownerIndex p 1))
  /-- Original PruningCoverCheck, step1. -/
  step1 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain1_0 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout717Domain8_0 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout717Domain1_2 (p.square (ownerIndex p 2))
  /-- Original PruningCoverCheck, step2. -/
  step2 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain2_0 (p.square (ownerIndex p 12)) →
    OrientedPoseCovered continuousScout717Domain10_0 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout717Domain2_3 (p.square (ownerIndex p 12))
  /-- Original PruningCoverCheck, step3. -/
  step3 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain3_0 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout717Domain4_0 (p.square (ownerIndex p 32)) →
    OrientedPoseCovered continuousScout717Domain3_4 (p.square (ownerIndex p 16))
  /-- Original PruningCoverCheck, step4. -/
  step4 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain4_0 (p.square (ownerIndex p 32)) →
    OrientedPoseCovered continuousScout717Domain10_0 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout717Domain4_5 (p.square (ownerIndex p 32))
  /-- Original PruningCoverCheck, step5. -/
  step5 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_0 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain0_1 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout717Domain6_6 (p.square (ownerIndex p 768))
  /-- Original PruningCoverCheck, step6. -/
  step6 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_6 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain7_0 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain6_7 (p.square (ownerIndex p 768))
  /-- Original PruningCoverCheck, step7. -/
  step7 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_7 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain9_0 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout717Domain6_8 (p.square (ownerIndex p 768))
  /-- Original PruningCoverCheck, step8. -/
  step8 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain7_0 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain3_4 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout717Domain7_9 (p.square (ownerIndex p 3072))
  /-- Original PruningCoverCheck, step9. -/
  step9 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain7_9 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain6_8 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain7_10 (p.square (ownerIndex p 3072))
  /-- Original PruningCoverCheck, step10. -/
  step10 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain7_10 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain11_0 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072))
  /-- Original PruningCoverCheck, step11. -/
  step11 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain9_0 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout717Domain2_3 (p.square (ownerIndex p 12)) →
    OrientedPoseCovered continuousScout717Domain9_12 (p.square (ownerIndex p 8192))
  /-- Original PruningCoverCheck, step12. -/
  step12 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain9_12 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout717Domain6_8 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain9_13 (p.square (ownerIndex p 8192))
  /-- Original PruningCoverCheck, step13. -/
  step13 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain0_1 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout717Domain1_2 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout717Domain0_14 (p.square (ownerIndex p 1))
  /-- Original PruningCoverCheck, step14. -/
  step14 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain0_14 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout717Domain9_13 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout717Domain0_15 (p.square (ownerIndex p 1))
  /-- Original PruningCoverCheck, step15. -/
  step15 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain3_4 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout717Domain4_5 (p.square (ownerIndex p 32)) →
    OrientedPoseCovered continuousScout717Domain3_16 (p.square (ownerIndex p 16))
  /-- Original PruningCoverCheck, step16. -/
  step16 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain3_16 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain3_17 (p.square (ownerIndex p 16))
  /-- Original VerticalChordPruningCoverCheck, step17. -/
  step17 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_8 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain0_15 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain11_0 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout717Domain6_18 (p.square (ownerIndex p 768))
  /-- Original VerticalChordPruningCoverCheck, step18. -/
  step18 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_18 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain3_17 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain9_13 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout717Domain6_19 (p.square (ownerIndex p 768))

theorem family_impossible (pending : Pending) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : False := by
  have h0 := pending.initial0 p hf
  have h1 := pending.initial1 p hf
  have h2 := pending.initial2 p hf
  have h3 := pending.initial3 p hf
  have h4 := pending.initial4 p hf
  have h6 := pending.initial6 p hf
  have h7 := pending.initial7 p hf
  have h8 := pending.initial8 p hf
  have h9 := pending.initial9 p hf
  have h10 := pending.initial10 p hf
  have h11 := pending.initial11 p hf
  have hstep0 := pending.step0 p hf h0 h1
  have hstep1 := pending.step1 p hf h1 h8
  have hstep2 := pending.step2 p hf h2 h10
  have hstep3 := pending.step3 p hf h3 h4
  have hstep4 := pending.step4 p hf h4 h10
  have hstep5 := pending.step5 p hf h6 hstep0
  have hstep6 := pending.step6 p hf hstep5 h7
  have hstep7 := pending.step7 p hf hstep6 h9
  have hstep8 := pending.step8 p hf h7 hstep3
  have hstep9 := pending.step9 p hf hstep8 hstep7
  have hstep10 := pending.step10 p hf hstep9 h11
  have hstep11 := pending.step11 p hf h9 hstep2
  have hstep12 := pending.step12 p hf hstep11 hstep7
  have hstep13 := pending.step13 p hf hstep0 hstep1
  have hstep14 := pending.step14 p hf hstep13 hstep12
  have hstep15 := pending.step15 p hf hstep3 hstep4
  have hstep16 := pending.step16 p hf hstep15 hstep10
  have hstep17 := pending.step17 p hf hstep7 hstep14 hstep10 h11
  have hstep18 := pending.step18 p hf hstep17 hstep16 hstep10 hstep12
  obtain ⟨leaf,member,_⟩ := hstep18
  exact List.not_mem_nil member

private theorem row_checked :
    (RowIdentity.rowAt 398).originalId = 717 ∧
    (RowIdentity.rowAt 398).groups = family := by decide +kernel

theorem excludes_case (pending : Pending) : ExcludesCase 717 := by
  intro r hr hid p hf
  apply family_impossible pending p
  exact hf.trans (RowIdentity.family_at 398 717 family row_checked r hr hid)

#print axioms family_impossible
#print axioms excludes_case
end
end N12Compact.Preservation.C717
