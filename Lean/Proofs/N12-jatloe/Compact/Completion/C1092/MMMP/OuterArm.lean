import Compact.Completion.C1092.MMMP.OuterArmSupport
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! A centered inward square cannot also own the outer .4 point of the
genuine wall neighbor. The entire canonical cover and complete physical
support sources are used, with no side cap or sampled angle restriction. -/
namespace N12Compact.C1092MMMPOuterArm
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

private theorem positive (C W : OpenSquare) (cn : Normal C.c C.s)
    (side : 1<C.side) (M : C.Inside (7/20) (7/20))
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (A : ¬C.Inside (2/5) 1) (T : W.Inside 1 (13/50))
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have lowerV : -C.s+(13/50)*C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    apply apart 1 (13/50)
    refine ⟨?_,T⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [Q.1,R.2.1,R.2.2.2,low,cp,cn.1,cn.2.1]
  have upperV : C.loV+C.side≤C.c-(2/5)*C.s := by
    apply le_of_not_gt
    intro high
    apply A
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [M.1,M.2.2.1,R.2.1,high,cp,cn.1,cn.2.1]
  have short := short_projections C (37/50) (3/5) (by norm_num)
  linarith only [lowerV,upperV,side,short.2.1]

private theorem negative (C W : OpenSquare) (cn : Normal C.c (-C.s)) (sign : C.s<0)
    (side : 1<C.side) (same : C.side=W.side)
    (origin : C.Inside 0 0) (M : C.Inside (7/20) (7/20))
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (N : ¬C.Inside (-7/20) (7/20)) (D : ¬C.Inside (7/20) (-7/20))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have o : C.loU<0 ∧ 0<C.loU+C.side ∧ C.loV<0 ∧ 0<C.loV+C.side := by
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero] using origin
  have lowerU : -(7/20)*(C.c-C.s)≤C.loU := by
    apply le_of_not_gt
    intro low
    apply N
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,o.2.1,o.2.2.1,M.2.2.2,cp,sign,cn.2.1]
  have lowerV : -(7/20)*(C.c+C.s)≤C.loV := by
    apply le_of_not_gt
    intro low
    apply D
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,o.1,o.2.2.2,lowerU,side,cp,sign,cn.2.1,cb.2.2.2.2.2]
  exact C1092MMMPOuterArmSupport.impossible C W C.c (-C.s) rfl (by ring) cn
    (by linarith only [sign]) side same (by linarith only [lowerV]) o.2.2.1 Q R S T wall cut apart

theorem impossible (C W : OpenSquare) (side : 1<C.side) (same : C.side=W.side)
    (origin : C.Inside 0 0) (M : C.Inside (7/20) (7/20))
    (P : C.Inside 0 (13/50)) (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (A : ¬C.Inside (2/5) 1) (N : ¬C.Inside (-7/20) (7/20))
    (D : ¬C.Inside (7/20) (-7/20))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  classical
  obtain ⟨V,cp,canon,shape,inside,_⟩ := ClosedFrames.canonical_frame C
  have ha : 1<V.side := by rwa [shape]
  have actualApart : ∀ x y, ¬(V.Inside x y ∧ W.Inside x y) :=
    fun x y own => apart x y ⟨(inside _ _).mp own.1,own.2⟩
  by_cases sign : 0≤V.s
  · have cn : Normal V.c V.s := ⟨sign,by simpa only [abs_of_nonneg sign] using canon,V.unit_normal⟩
    exact positive V W cn ha ((inside _ _).mpr M) ((inside _ _).mpr Q)
      ((inside _ _).mpr R) (fun own => A ((inside _ _).mp own)) T actualApart
  · have sign : V.s<0 := lt_of_not_ge sign
    have cn : Normal V.c (-V.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_neg sign] using canon,by nlinarith only [V.unit_normal]⟩
    exact negative V W cn sign ha (shape.trans same) ((inside _ _).mpr origin)
      ((inside _ _).mpr M) ((inside _ _).mpr Q) ((inside _ _).mpr R)
      (fun own => N ((inside _ _).mp own)) (fun own => D ((inside _ _).mp own))
      S T wall cut actualApart

#print axioms impossible
end N12Compact.C1092MMMPOuterArm
