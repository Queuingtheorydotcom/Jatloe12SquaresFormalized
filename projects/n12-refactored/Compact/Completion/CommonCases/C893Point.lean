import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames

/-! The actual owned corner marker in C893 is preserved. Its G outward
anchor suffices: the F outward anchor is derived strictly by the square
bands, avoiding a stronger optional F-label entrance. -/
namespace N12Compact.CommonCases.C893Point
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (upper : q.Inside 1 (2/5))
    (corner : q.Inside (543/500) 1)
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingT : ¬q.Inside (22/25) 1) :
    q.Inside (1/2) 0 ∨ q.Inside (27/50) (-1/100) := by
  classical
  simp only [OpenSquare.Inside, InBands, mul_one, mul_zero, add_zero]
    at missingG missingR missingT
  have cu := (CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have tLowU : q.loU < q.c*(22/25)+q.s := by linarith only [marker.1,cp,sn]
  have tHighU : q.c*(22/25)+q.s < q.loU+q.side := by linarith only [corner.2.1,cp]
  have tLowV : q.loV < -q.s*(22/25)+q.c := by linarith only [marker.2.2.1,cp,order]
  have tFace : q.loV+q.side ≤ -q.s*(22/25)+q.c :=
    le_of_not_gt (fun h => missingT ⟨tLowU,tHighU,tLowV,h⟩)
  have gHighU : q.c*(13/50) < q.loU+q.side := by linarith only [marker.2.1,cp,sn]
  have gHighV : -q.s*(13/50) < q.loV+q.side := by linarith only [marker.2.2.2,cp,order]
  have gLowV : q.loV < -q.s*(13/50) := by linarith only [tFace,side,cu,sn]
  have gFace : q.c*(13/50) ≤ q.loU :=
    le_of_not_gt (fun h => missingG ⟨h,gHighU,gLowV,gHighV⟩)
  have rLowU : q.loU < q.c*(543/500) := by linarith only [marker.1,cp,order]
  have rHighU : q.c*(543/500) < q.loU+q.side := by linarith only [gFace,side,cu]
  have rHighV : -q.s*(543/500) < q.loV+q.side := by linarith only [upper.2.2.2,cp,sn]
  have rFace : -q.s*(543/500) ≤ q.loV :=
    le_of_not_gt (fun h => missingR ⟨rLowU,rHighU,h,rHighV⟩)
  have span : 1 < q.c+(103/500)*q.s := by linarith only [rFace,tFace,side]
  have sp : 0 < q.s := by linarith only [span,cu]
  have shallow : 2*q.s < q.c := by
    by_contra failed
    have steep : q.c ≤ 2*q.s := le_of_not_gt failed
    have coefficient : 0 < (239391/250000)*q.s-(103/250)*q.c := by
      linarith only [steep,cp]
    have product := mul_pos sp coefficient
    have short : q.c+(103/500)*q.s < 1 := by nlinarith only [q.unit_normal,product,cp,sn]
    linarith only [short,span]
  have outward : q.Inside 1 (13/50) := by
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [marker.1,cp,order]
    · linarith only [corner.2.1,cp,sn]
    · linarith only [tFace,side,cu,order,sn]
    · linarith only [upper.2.2.2,cp]
  by_cases tiny : 20*q.s < q.c
  · left
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [marker.1,tiny,cp]
    · linarith only [outward.2.1,cp,sn]
    · linarith only [tFace,side,cu,sn]
    · linarith only [marker.2.2.2,cp,sn]
  · have ratio := mul_nonneg
      (show 0 ≤ 20*q.s-q.c by linarith only [le_of_not_gt tiny])
      (show 0 ≤ 20*q.s+q.c by linarith only [cp,sn])
    have sineLow : 1/21 < q.s := by nlinarith only [ratio,q.unit_normal,sn]
    right
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [marker.1,shallow,cp]
    · linarith only [outward.2.1,cp,sn]
    · linarith only [tFace,side,cu,sineLow]
    · linarith only [marker.2.2.2,cp,sn]

private theorem negative_impossible (q : OpenSquare) (t : ℝ)
    (signed : q.s = -t) (side : 1 < q.side) (cp : 0 < q.c)
    (tn : 0 ≤ t) (order : t ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (corner : q.Inside (543/500) 1)
    (missingR : ¬q.Inside (543/500) 0)
    (missingT : ¬q.Inside (22/25) 1) : False := by
  simp only [OpenSquare.Inside, InBands, mul_one, mul_zero, add_zero]
    at missingR missingT
  have m := marker
  have h := corner
  simp only [OpenSquare.Inside,InBands,signed] at m h
  have p : q.Inside 1 1 := by
    dsimp [OpenSquare.Inside,InBands]; rw [signed]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [m.1,m.2.2.1,h.2.1,h.2.2.2,cp,tn,order]
  have pp := p
  simp only [OpenSquare.Inside,InBands,signed] at pp
  have tHighU : q.c*(22/25)+q.s < q.loU+q.side := by
    rw [signed]; linarith only [pp.2.1,cp]
  have tLowV : q.loV < -q.s*(22/25)+q.c := by
    rw [signed]; linarith only [m.2.2.1,cp,tn]
  have tHighV : -q.s*(22/25)+q.c < q.loV+q.side := by
    rw [signed]; linarith only [pp.2.2.2,tn]
  have tFace : q.c*(22/25)+q.s ≤ q.loU :=
    le_of_not_gt (fun own => missingT ⟨own,tHighU,tLowV,tHighV⟩)
  have slope : 53*q.c < 65*t := by rw [signed] at tFace; linarith only [tFace,m.1]
  have rLowU : q.loU < q.c*(543/500) := by linarith only [m.1,cp,tn]
  have rLowV : q.loV < -q.s*(543/500) := by rw [signed]; linarith only [m.2.2.1,slope,cp]
  have rHighV : -q.s*(543/500) < q.loV+q.side := by rw [signed]; linarith only [pp.2.2.2,cp,order]
  have rFace : q.loU+q.side ≤ q.c*(543/500) :=
    le_of_not_gt (fun own => missingR ⟨rLowU,own,rLowV,rHighV⟩)
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have short := OutwardScalars.increasing_projection q.c t (103/500) 1
    cp tn order unit (by norm_num) (by norm_num) (by norm_num)
  rw [signed] at tFace
  linarith only [tFace,rFace,short,side]

theorem points (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (7/20) (7/20)) (upper : q.Inside 1 (2/5))
    (corner : q.Inside (543/500) 1)
    (missingG : ¬q.Inside (13/50) 0)
    (missingR : ¬q.Inside (543/500) 0)
    (missingT : ¬q.Inside (22/25) 1) :
    q.Inside (1/2) 0 ∨ q.Inside (27/50) (-1/100) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr upper
  have h := (same _ _).mpr corner
  have g : ¬r.Inside (13/50) 0 := fun own => missingG ((same _ _).mp own)
  have rr : ¬r.Inside (543/500) 0 := fun own => missingR ((same _ _).mp own)
  have tt : ¬r.Inside (22/25) 1 := fun own => missingT ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · rcases positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m a h g rr tt with first | second
    · exact Or.inl ((same _ _).mp first)
    · exact Or.inr ((same _ _).mp second)
  · exact (negative_impossible r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) m h rr tt).elim

theorem points_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (47/20)) (upper : q.Inside 3 (12/5))
    (corner : q.Inside (1543/500) 3)
    (missingG : ¬q.Inside (113/50) 2)
    (missingR : ¬q.Inside (1543/500) 2)
    (missingT : ¬q.Inside (72/25) 3) :
    q.Inside (5/2) 2 ∨ q.Inside (127/50) (199/100) := by
  have h := points (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact upper)
    (by norm_num [inside_translated_iff]; exact corner)
    (by norm_num [inside_translated_iff]; exact missingG)
    (by norm_num [inside_translated_iff]; exact missingR)
    (by norm_num [inside_translated_iff]; exact missingT)
  norm_num [inside_translated_iff] at h
  exact h

#print axioms points_original
end N12Compact.CommonCases.C893Point
