import S12.AngleData64

namespace N12Compact.C898Initial
open S12

/-- Ordinary kernel proof of complete closed-interval coverage. -/
theorem angles64_cover_kernel : CoversInterval 0 1 (angles64.map Subtype.val) := by
  norm_num [angles64, CoversInterval, angle64_0, angle64_1, angle64_2, angle64_3, angle64_4, angle64_5, angle64_6, angle64_7, angle64_8, angle64_9, angle64_10, angle64_11, angle64_12, angle64_13, angle64_14, angle64_15, angle64_16, angle64_17, angle64_18, angle64_19, angle64_20, angle64_21, angle64_22, angle64_23, angle64_24, angle64_25, angle64_26, angle64_27, angle64_28, angle64_29, angle64_30, angle64_31, angle64_32, angle64_33, angle64_34, angle64_35, angle64_36, angle64_37, angle64_38, angle64_39, angle64_40, angle64_41, angle64_42, angle64_43, angle64_44, angle64_45, angle64_46, angle64_47, angle64_48, angle64_49, angle64_50, angle64_51, angle64_52, angle64_53, angle64_54, angle64_55, angle64_56, angle64_57, angle64_58, angle64_59, angle64_60, angle64_61, angle64_62, angle64_63]

#print axioms angles64_cover_kernel
end N12Compact.C898Initial
