import Compact.Completion.C1092.MPPMForwardPositiveDSupport

/-! Complete positive-recipient two-central theorem of
C1092-POSITIVE-D-TRANSFER section 1. The source square C is in the
southwest sector and J is its physical southeast successor. The proof
checks every actual separator axis, both directions and both angle orders.
No boundary origin ownership, wall, side cap, or support premise is assumed.
Source-only, uncompiled. -/
namespace N12Compact.C1092MPPMForwardPositiveD
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open Completion.OtherCases
set_option Elab.async false

/-- The positive successor cannot own the origin (2,1). Its marker and
forward point are the only strict successor anchors used by the support
argument; its ordinary pair is not needed for this local implication. -/
theorem previous_origin_excluded (C J : OpenSquare)
    (side : 1<C.side) (sameSide : C.side=J.side)
    (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c)
    (dp : 0<J.c) (tn : 0≤J.s) (h : Predecessor C)
    (markerJ : J.Inside (47/20) (33/20))
    (forwardJ : J.Inside 2 (87/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ J.Inside x y)) :
    ¬J.Inside 2 1 := by
  intro origin
  obtain ⟨lowerU,f,upperV,data⟩ := predecessor_faces C side cp sn order h
  have cu := (CommonCases.CanonicalScalars.bounds C.c C.s cp sn order C.unit_normal).2.1
  have rejectCU : ¬upper C C.c C.s≤lower J C.c C.s := by
    intro separation
    have strict := (strict_bounds J 2 1 C.c C.s C.unit_normal origin).1
    rw [(ownU C).2] at separation
    nlinarith only [strict,separation,lowerU,side,cu,sn]
  have rejectCV : ¬upper C C.s (-C.c)≤lower J C.s (-C.c) := by
    intro separation
    have strict := (strict_bounds J 2 (87/50) C.s (-C.c)
      (by nlinarith only [C.unit_normal]) forwardJ).1
    have support : upper C C.s (-C.c)= -C.loV := by
      calc
        upper C C.s (-C.c)=upper C (-(-C.s)) (-C.c) := by rw [neg_neg]
        _= -lower C (-C.s) C.c := WallProfile.upper_neg C (-C.s) C.c
        _= -C.loV := by rw [(ownV C).1]
    rw [support] at separation
    nlinarith only [strict,separation,upperV,side,data.short]
  have rejectJU : ¬upper C J.c J.s≤lower J J.c J.s := by
    intro separation
    have strict := (strict_bounds J 2 1 J.c J.s J.unit_normal origin).1
    have support := recipient_u C J f side cp sn order dp tn lowerU upperV h.forward data
    nlinarith only [strict,separation,support]
  have rejectJV : ¬upper C J.s (-J.c)≤lower J J.s (-J.c) := by
    intro separation
    have strict := (strict_bounds J 2 (87/50) J.s (-J.c)
      (by nlinarith only [J.unit_normal]) forwardJ).1
    have support := recipient_negative_v C J f side cp sn dp tn lowerU upperV h.ordinaryG data
    nlinarith only [strict,separation,support]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (separation : upper C nx ny≤lower J nx ny) : 0<nx := by
    have first := (strict_bounds C (33/20) (33/20) nx ny unit h.marker).2
    have last := (strict_bounds J (47/20) (33/20) nx ny unit markerJ).1
    nlinarith only [first,last,separation]
  have reverse (nx ny : ℝ) (separation : upper J nx ny≤lower C nx ny) :
      upper C (-nx) (-ny)≤lower J (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [separation]
  have axes := CongruentSAT.faceSeparation_of_disjoint C J sameSide apart
  change pairRadius C J≤|C.c*(centerX J-centerX C)+C.s*(centerY J-centerY C)| ∨
    pairRadius C J≤|-C.s*(centerX J-centerX C)+C.c*(centerY J-centerY C)| ∨
    pairRadius J C≤|J.c*(centerX J-centerX C)+J.s*(centerY J-centerY C)| ∨
    pairRadius J C≤|-J.s*(centerX J-centerX C)+J.c*(centerY J-centerY C)| at axes
  have separate (nx ny R : ℝ)
      (radius : supportRadius C nx ny+supportRadius J nx ny=R)
      (axis : R≤|nx*(centerX J-centerX C)+ny*(centerY J-centerY C)|) :=
    separated C J nx ny (by rwa [radius])
  rcases axes with cuAxis | cvAxis | juAxis | jvAxis
  · rcases separate _ _ _ (parallel_radius C J) cuAxis with forward | backward
    · exact rejectCU forward
    · have failed := cone (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (reverse _ _ backward)
      linarith only [failed,cp]
  · rcases separate _ _ _ (transverse_radius C J) cvAxis with forward | backward
    · have failed := cone (-C.s) C.c (by nlinarith only [C.unit_normal]) forward
      linarith only [failed,sn]
    · apply rejectCV
      simpa only [neg_neg] using reverse _ _ backward
  · have radius : supportRadius C J.c J.s+supportRadius J J.c J.s=pairRadius J C := by
      rw [add_comm]
      exact parallel_radius J C
    rcases separate _ _ _ radius juAxis with forward | backward
    · exact rejectJU forward
    · have failed := cone (-J.c) (-J.s) (by nlinarith only [J.unit_normal])
        (reverse _ _ backward)
      linarith only [failed,dp]
  · have radius : supportRadius C (-J.s) J.c+supportRadius J (-J.s) J.c=pairRadius J C := by
      rw [add_comm]
      exact transverse_radius J C
    rcases separate _ _ _ radius jvAxis with forward | backward
    · have failed := cone (-J.s) J.c (by nlinarith only [J.unit_normal]) forward
      linarith only [failed,tn]
    · apply rejectJV
      simpa only [neg_neg] using reverse _ _ backward

#print axioms previous_origin_excluded
end N12Compact.C1092MPPMForwardPositiveD
