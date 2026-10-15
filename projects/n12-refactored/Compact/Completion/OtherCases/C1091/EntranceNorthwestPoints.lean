import Compact.Completion.OtherCases.C1091.EntranceMergedShallow

/-! A corrected point-level entrance for the residual C1091 northwest
branch. The merged square owns either (1.6,2) or (1.46,2.01), with the
second ordinate above 2. An inward northwest square omitting F3 and the
actual southeast-owned center owns the first point as well as its existing
strong inward point. No top-wall auxiliary ownership is needed.

Source only; no compilation, numerical search or generated certificate. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceNorthwestPoints
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

/-- A literal split of the genuine merged profile. At 7s=c the first
alternative still has strict bands, because its marker is strictly owned. -/
theorem merged_alternative (A : OpenSquare) (h : EntranceMergedShallow.Input A) :
    A.Inside (3/5) 1 ∨ A.Inside (23/50) (101/100) := by
  obtain ⟨B,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame A
  have data := h.reframe shape same
  by_cases sign : 0≤B.s
  · have cn : Normal B.c B.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using range,B.unit_normal⟩
    have p := EntranceMergedShallow.profile B data cn
    have bounds := normal_bounds cn
    by_cases shallow : 7*B.s≤B.c
    · left
      apply (same _ _).mp
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [data.left.1,data.left.2.2.1,data.marker.2.1,
          data.side,p.1,p.2.1,cp,bounds.2.1,cn.2.1,shallow]
    · right
      apply (same _ _).mp
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [data.left.1,data.left.2.2.1,data.marker.2.1,
          data.side,p.1,p.2.1,p.2.2,cp,bounds.2.1,cn.2.1,shallow]
  · have sn : B.s≤0 := le_of_not_ge sign
    have order : -B.s≤B.c := by linarith only [(abs_le.mp range).1]
    exfalso
    apply data.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [data.left.1,data.left.2.2.1,data.marker.2.1,
        data.marker.2.2.2,cp,sn,order]

theorem merged_alternative_original (A : OpenSquare) (side : 1<A.side)
    (left : A.Inside (457/500) 1) (marker : A.Inside (33/20) (33/20))
    (corner : ¬A.Inside 1 1) (wall : ¬A.Inside (457/500) 2) :
    A.Inside (8/5) 2 ∨ A.Inside (73/50) (201/100) := by
  have data : EntranceMergedShallow.Input (A.translated 1 1) where
    side := side
    left := by norm_num only [inside_translated_iff]; exact left
    marker := by norm_num only [inside_translated_iff]; exact marker
    corner := by norm_num only [inside_translated_iff]; exact corner
    wall := by norm_num only [inside_translated_iff]; exact wall
  have result := merged_alternative (A.translated 1 1) data
  norm_num only [inside_translated_iff] at result
  exact result

private theorem positive_low (N : OpenSquare) (cp : 0<N.c)
    (sn : 0≤N.s) (order : N.s≤N.c)
    (marker : N.Inside (33/20) (47/20))
    (inner : N.Inside (87/50) 2)
    (strong : N.Inside (73/50) (201/100)) : N.Inside (8/5) 2 := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [strong.1,inner.2.1,inner.2.2.1,marker.2.2.2,cp,sn,order]

/-- For the negative sign the genuine foreign center selects upper u.
An F3 lower-u exit would give side <= .4c+t <= .7(c+t) <= 1.
Its remaining upper-v exit places (1.6,2) strictly inside, since the
two points have the same abscissa and projected distance c <= 1. -/
private theorem negative_low (N : OpenSquare) (t : ℝ) (signed : N.s=-t)
    (side : 1<N.side) (cp : 0<N.c) (tn : 0≤t) (order : t≤N.c)
    (marker : N.Inside (33/20) (47/20))
    (inner : N.Inside (87/50) 2) (elbow : N.Inside 2 (113/50))
    (strong : N.Inside (73/50) (201/100))
    (missingF3 : ¬N.Inside (8/5) 3) (missingCenter : ¬N.Inside 2 2) :
    N.Inside (8/5) 2 := by
  have unit := N.unit_normal
  rw [signed] at unit
  have cn : Normal N.c t := ⟨tn,order,by nlinarith only [unit]⟩
  have bounds := normal_bounds cn
  have mm := marker
  have ii := inner
  have ee := elbow
  have ss := strong
  simp only [OpenSquare.Inside,InBands,signed] at mm ii ee ss
  have upperU : N.loU+N.side≤2*N.c-2*t := by
    apply le_of_not_gt
    intro high
    apply missingCenter
    dsimp only [OpenSquare.Inside,InBands]
    rw [signed]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,ii.1,ii.2.2.1,ee.2.2.2,cp,tn]
  have lowF3 : N.loU<(8/5)*N.c-3*t := by
    apply lt_of_not_ge
    intro low
    have width : (2/5)*N.c+t≤1 := by
      linarith only [bounds.2.2.2.2.2,order]
    linarith only [low,upperU,width,side]
  have upperV : N.loV+N.side≤(8/5)*t+3*N.c := by
    apply le_of_not_gt
    intro high
    apply missingF3
    dsimp only [OpenSquare.Inside,InBands]
    rw [signed]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [lowF3,high,ee.2.1,ii.2.2.1,cp,tn,order]
  dsimp only [OpenSquare.Inside,InBands]
  rw [signed]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [ss.1,ii.2.1,mm.2.2.2,upperV,side,cp,tn,order,bounds.2.1]

/-- All canonical orientations of the same physical northwest owner.
The center exclusion must come from its genuine foreign southeast owner. -/
theorem northwest_low (N : OpenSquare) (side : 1<N.side)
    (marker : N.Inside (33/20) (47/20))
    (inner : N.Inside (87/50) 2) (elbow : N.Inside 2 (113/50))
    (strong : N.Inside (73/50) (201/100))
    (missingF3 : ¬N.Inside (8/5) 3) (missingCenter : ¬N.Inside 2 2) :
    N.Inside (8/5) 2 := by
  obtain ⟨F,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame N
  have fm := (same _ _).mpr marker
  have fi := (same _ _).mpr inner
  have fe := (same _ _).mpr elbow
  have fs := (same _ _).mpr strong
  apply (same _ _).mp
  by_cases sign : 0≤F.s
  · exact positive_low F cp sign (by simpa only [abs_of_nonneg sign] using range)
      fm fi fs
  · exact negative_low F (-F.s) (by ring) (by simpa only [shape] using side)
      cp (by linarith only [sign]) (by linarith only [(abs_le.mp range).1]) fm fi fe fs
      (fun own => missingF3 ((same _ _).mp own))
      (fun own => missingCenter ((same _ _).mp own))

end
#print axioms merged_alternative_original
#print axioms northwest_low
end N12Compact.Completion.OtherCases.C1091.EntranceNorthwestPoints
