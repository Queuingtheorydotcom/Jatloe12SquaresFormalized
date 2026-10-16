import Compact.Completion.OtherCases.C983.F4SoutheastSignSupports
import Compact.Completion.C1092.MixedCornerSupports
import Compact.Geometry.ClosedFrames

/-! C983-F4-TOP-ONLY-8208-ENDING section 2.1 and the unchanged sign
argument in C983-F4-MIXED-NEGATIVE-8208-ENDING section 2. The actual western
square is reindexed, never replaced by independently chosen face values.
Every forward and reverse face axis and both canonical signs are included. -/
namespace N12Compact.Completion.OtherCases.C983.F4SoutheastSign
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C1092MixedCornerSupports
set_option Elab.async false

theorem entrance (E : OpenSquare) (side : 1<E.side)
    (cp : 0<E.c) (sn : 0≤E.s) (order : E.s≤E.c)
    (M : E.Inside (7/20) (-7/20)) (D : E.Inside (13/50) 0)
    (A : E.Inside 1 (-13/50)) (missingR : ¬E.Inside 1 0)
    (missingF : ¬E.Inside 0 (-13/50)) : F4SoutheastSignSupports.Data E := by
  have cap : E.loU+E.side≤E.c := by
    apply le_of_not_gt
    intro high
    apply missingR
    simp only [OpenSquare.Inside,InBands,mul_one,mul_zero,zero_mul,add_zero,zero_add]
    refine ⟨?_,high,?_,?_⟩ <;> linarith only [D.1,D.2.2.2,A.2.2.1,cp,sn]
  have floor : -(13/50)*E.s≤E.loU := by
    apply le_of_not_gt
    intro low
    apply missingF
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,D.2.1,D.2.2.2,M.2.2.1,cp,sn,order]
  have width : 1<E.c+(13/50)*E.s := by linarith only [floor,cap,side]
  have cosineUpper : E.c≤1 := by
    nlinarith only [E.unit_normal,sq_nonneg E.s,sq_nonneg (E.c-1)]
  have sineUpper : E.s≤1 := by
    nlinarith only [E.unit_normal,sq_nonneg E.c,sq_nonneg (E.s-1)]
  have sp : 0<E.s := by linarith only [width,cosineUpper]
  have square := mul_pos (show 0<E.c+(13/50)*E.s-1 by linarith only [width])
    (show 0<E.c+1-(13/50)*E.s by linarith only [cp,sineUpper])
  have small : E.s<1/2 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg sp.le
      (show 0≤E.s-1/2 by linarith only [bad])
    nlinarith only [product,square,E.unit_normal,sp]
  have cosine : 4/5<E.c := by linarith only [width,small]
  have strictUpper : E.c<1 := by
    nlinarith only [E.unit_normal,mul_pos sp sp,cp,sq_nonneg (E.c-1)]
  exact ⟨cosine,strictUpper,sp,small,by linarith only [cap,side],
    by linarith only [M.2.2.1],by linarith only [D.2.1],by linarith only [D.2.2.2]⟩

/-- A nonnegative southeast frame contradicts the full actual western
square, with no northeast cap point or bottom-bar premise. -/
theorem nonnegative_impossible (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side) (cp : 0<E.c) (sn : 0≤E.s) (order : E.s≤E.c)
    (P : W.Inside (-7/20) (-7/20)) (Q : W.Inside (-7/20) (7/20))
    (F : W.Inside 0 (-13/50)) (O : W.Inside 0 0)
    (M : E.Inside (7/20) (-7/20)) (D : E.Inside (13/50) 0)
    (A : E.Inside 1 (-13/50)) (missingR : ¬E.Inside 1 0)
    (missingF : ¬E.Inside 0 (-13/50))
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : False := by
  have data := entrance E side cp sn order M D A missingR missingF
  obtain ⟨w,wp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame W
  have p := (inside _ _).mpr P
  have q := (inside _ _).mpr Q
  have f := (inside _ _).mpr F
  have o := (inside _ _).mpr O
  have same' : w.side=E.side := shape.trans same
  have disjoint : ∀ x y,¬(w.Inside x y ∧ E.Inside x y) :=
    fun x y own => apart x y ⟨(inside _ _).mp own.1,own.2⟩
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper w nx ny≤lower E nx ny) : 0<nx ∧ ny<nx := by
    have first := (strict_bounds w _ _ nx ny unit p).2
    have last := (strict_bounds E _ _ nx ny unit M).1
    have other := (strict_bounds w _ _ nx ny unit q).2
    constructor <;> linarith only [first,last,other,sep]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower w nx ny) :
      upper w (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [(negative_support w nx ny).2,(negative_support E nx ny).1]
    exact neg_le_neg sep
  have bounds := abs_le.mp range
  have noWU (sep : upper w w.c w.s≤lower E w.c w.s ∨
      upper E w.c w.s≤lower w w.c w.s) : False := by
    rcases sep with forward|backward
    · by_cases sign : 0≤w.s
      · have low := F4SoutheastSignSupports.positive_u E data w.c w.s wp sign
        have high := (strict_bounds w _ _ w.c w.s w.unit_normal o).2
        linarith only [low,high,forward]
      · have low := F4SoutheastSignSupports.negative_w E data w.c (-w.s) wp
          (by linarith only [sign]) (by linarith only [bounds.1])
        simp only [neg_neg] at low
        have high := (strict_bounds w _ _ w.c w.s w.unit_normal f).2
        linarith only [low,high,forward]
    · have direction := cone (-w.c) (-w.s)
        (by simpa only [neg_sq] using w.unit_normal) (reverse _ _ backward)
      linarith only [direction.1,wp]
  have noWV (sep : upper w (-w.s) w.c≤lower E (-w.s) w.c ∨
      upper E (-w.s) w.c≤lower w (-w.s) w.c) : False := by
    have unit : (-w.s)^2+w.c^2=1 := by nlinarith only [w.unit_normal]
    rcases sep with forward|backward
    · have direction := cone (-w.s) w.c unit forward
      linarith only [direction.2,bounds.1]
    · have opposite : upper w w.s (-w.c)≤lower E w.s (-w.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      by_cases sign : 0≤w.s
      · have low := F4SoutheastSignSupports.positive_v E data w.c w.s wp sign bounds.2
        have high := (strict_bounds w _ _ w.s (-w.c)
          (by nlinarith only [w.unit_normal]) f).2
        linarith only [low,high,opposite]
      · have direction := cone w.s (-w.c) (by nlinarith only [w.unit_normal]) opposite
        linarith only [direction.1,sign]
  have noEU (sep : upper w E.c E.s≤lower E E.c E.s ∨
      upper E E.c E.s≤lower w E.c E.s) : False := by
    rcases sep with forward|backward
    · rw [(ownU E).1] at forward
      have high := (strict_bounds w _ _ E.c E.s E.unit_normal o).2
      linarith only [forward,high,data.lowerU,data.cosineUpper]
    · have direction := cone (-E.c) (-E.s)
        (by simpa only [neg_sq] using E.unit_normal) (reverse _ _ backward)
      linarith only [direction.1,cp]
  have noEV (sep : upper w (-E.s) E.c≤lower E (-E.s) E.c ∨
      upper E (-E.s) E.c≤lower w (-E.s) E.c) : False := by
    have unit : (-E.s)^2+E.c^2=1 := by nlinarith only [E.unit_normal]
    rcases sep with forward|backward
    · have direction := cone (-E.s) E.c unit forward
      linarith only [direction.1,sn]
    · have opposite : upper w E.s (-E.c)≤lower E E.s (-E.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      have formula : lower E E.s (-E.c)= -(E.loV+E.side) := by
        simpa only [neg_neg,(ownV E).2] using (negative_support E (-E.s) E.c).1
      rw [formula] at opposite
      have high := (strict_bounds w _ _ E.s (-E.c)
        (by nlinarith only [E.unit_normal]) f).2
      linarith only [opposite,high,data.upperV,order]
  have axes := CongruentSAT.faceSeparation_of_disjoint w E same' disjoint
  change pairRadius w E≤|w.c*(centerX E-centerX w)+w.s*(centerY E-centerY w)| ∨
    pairRadius w E≤|-w.s*(centerX E-centerX w)+w.c*(centerY E-centerY w)| ∨
    pairRadius E w≤|E.c*(centerX E-centerX w)+E.s*(centerY E-centerY w)| ∨
    pairRadius E w≤|-E.s*(centerX E-centerX w)+E.c*(centerY E-centerY w)| at axes
  have separate (nx ny radius : ℝ)
      (identity : supportRadius w nx ny+supportRadius E nx ny=radius)
      (axis : radius≤|nx*(centerX E-centerX w)+ny*(centerY E-centerY w)|) :=
    separated w E nx ny (by rwa [identity])
  rcases axes with wu|wv|eu|ev
  · exact noWU (separate _ _ _ (parallel_radius w E) wu)
  · exact noWV (separate _ _ _ (transverse_radius w E) wv)
  · have identity : supportRadius w E.c E.s+supportRadius E E.c E.s=pairRadius E w := by
      rw [add_comm]
      exact parallel_radius E w
    exact noEU (separate _ _ _ identity eu)
  · have identity : supportRadius w (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E w := by
      rw [add_comm]
      exact transverse_radius E w
    exact noEV (separate _ _ _ identity ev)

/-- Any canonical representation of this same southeast square has a
strictly negative sine. The axial case is included in the contradiction. -/
theorem canonical_negative (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side) (cp : 0<E.c) (range : |E.s|≤E.c)
    (P : W.Inside (-7/20) (-7/20)) (Q : W.Inside (-7/20) (7/20))
    (F : W.Inside 0 (-13/50)) (O : W.Inside 0 0)
    (M : E.Inside (7/20) (-7/20)) (D : E.Inside (13/50) 0)
    (A : E.Inside 1 (-13/50)) (missingR : ¬E.Inside 1 0)
    (missingF : ¬E.Inside 0 (-13/50))
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) : E.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  exact nonnegative_impossible W E side same cp nonnegative (abs_le.mp range).2
    P Q F O M D A missingR missingF apart

/-- Physical all-angle form: reindexing preserves the actual E and all
strict memberships; only its canonical face coordinates change. -/
theorem exists_negative (W E : OpenSquare) (side : 1<E.side)
    (same : W.side=E.side)
    (P : W.Inside (-7/20) (-7/20)) (Q : W.Inside (-7/20) (7/20))
    (F : W.Inside 0 (-13/50)) (O : W.Inside 0 0)
    (M : E.Inside (7/20) (-7/20)) (D : E.Inside (13/50) 0)
    (A : E.Inside 1 (-13/50)) (missingR : ¬E.Inside 1 0)
    (missingF : ¬E.Inside 0 (-13/50))
    (apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)) :
    ∃ C : OpenSquare, ∃ t : ℝ, C.side=E.side ∧
      (∀ x y, C.Inside x y ↔ E.Inside x y) ∧
      0<C.c ∧ C.s= -t ∧ 0<t ∧ t≤C.c := by
  obtain ⟨C,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame E
  have negative := canonical_negative W C (by rwa [shape]) (same.trans shape.symm) cp range
    P Q F O ((inside _ _).mpr M) ((inside _ _).mpr D) ((inside _ _).mpr A)
    (fun own => missingR ((inside _ _).mp own))
    (fun own => missingF ((inside _ _).mp own))
    (fun x y own => apart x y ⟨own.1,(inside x y).mp own.2⟩)
  exact ⟨C,-C.s,shape,inside,cp,by ring,by linarith only [negative],
    by linarith only [(abs_le.mp range).1]⟩

#print axioms nonnegative_impossible
#print axioms canonical_negative
#print axioms exists_negative
end N12Compact.Completion.OtherCases.C983.F4SoutheastSign
