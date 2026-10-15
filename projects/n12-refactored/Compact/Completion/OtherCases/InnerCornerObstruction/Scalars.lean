import Compact.Completion.CommonCases.CanonicalQuadratic

/-! All four continuous endpoint estimates of INNER-CORNER-INWARD-POINT.
The rational quadratic factorization includes the entire closed intervals. -/
namespace N12Compact.Completion.OtherCases.InnerCornerObstruction.Scalars
open CommonCases.CanonicalQuadratic
set_option Elab.async false

theorem before_sixth (c s : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) (cut : 6*s≤c) : (413/500)*c+s<1 := by
  simpa only [one_mul] using before_one c s (413/500) 1 6 1 cn sn unit
    (by norm_num) (by norm_num) (by simpa only [one_mul] using cut)
    (by norm_num [firstCoeff]) (by norm_num [secondCoeff])

theorem after_four_ninth (c s : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) (cut : 4*c≤9*s) : c+(103/500)*s<1 := by
  simpa only [one_mul] using after_one c s 1 (103/500) 9 4 cn sn unit
    (by norm_num) (by norm_num) cut
    (by norm_num [firstCoeff]) (by norm_num [secondCoeff])

theorem upper_v (c s : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) (cut : c≤6*s) : (26/25)*c-(19/50)*s<1 := by
  have bound := after_one c s (26/25) (-(19/50)) 6 1 cn sn unit
    (by norm_num) (by norm_num) (by simpa only [one_mul] using cut)
    (by norm_num [firstCoeff]) (by norm_num [secondCoeff])
  linarith only [bound]

theorem upper_u (c s : ℝ) (cn : 0≤c) (sn : 0≤s)
    (unit : c^2+s^2=1) (cut : 9*s≤4*c) : (313/500)*c+(26/25)*s<1 :=
  before_one c s (313/500) (26/25) 9 4 cn sn unit
    (by norm_num) (by norm_num) cut
    (by norm_num [firstCoeff]) (by norm_num [secondCoeff])

end N12Compact.Completion.OtherCases.InnerCornerObstruction.Scalars
