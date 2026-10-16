import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNorthwestGeometry
import Compact.Completion.C1092.MMMP.TwoFifthsEntranceRight

/-! The complete actual E/W entrance for the shared upper-third step.
All wall points belong to their original Q8/Q10, and the central
halfpoints and markers remain in the same actual Q7. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
open C1092MMMPEndingAxes C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
set_option Elab.async false

/-- The universal negative-W/N support from UPPER-STRICT-POINTS,
with only the weaker top-cap faces and lower half-angle. -/
theorem negative_northwest_profile (W N : OpenSquare)
    (side : 1<W.side) (same : W.side=N.side) (wn : Normal W.c (-W.s))
    (n : NortheastCore N) (origin : W.Inside 0 0)
    (left : W.Inside (-1/2) 0) (marker : W.Inside (-7/20) (7/20))
    (missing : ¬W.Inside (-7/20) (-7/20))
    (apart : ∀ x y,¬(W.Inside x y ∧ N.Inside x y)) :
    -W.s<7/50 ∧ 99/100<W.c ∧ W.loV+W.side<25/33 := by
  let C := clockwise W
  let B := clockwise N
  have nn : Normal N.c N.s := ⟨n.sine.le,n.canonical,N.unit_normal⟩
  have zero : C.Inside 0 0 := by simpa only [C,inside_clockwise,neg_zero] using origin
  have down : C.Inside 0 (-1/2) := by
    apply (inside_clockwise _ _ _).mpr
    convert left using 1
    norm_num
  have mark : C.Inside (-7/20) (-7/20) := by
    apply (inside_clockwise _ _ _).mpr
    convert marker using 1
    norm_num
  have absent : ¬C.Inside (7/20) (-7/20) := by
    intro own
    apply missing
    have raw := (inside_clockwise _ _ _).mp own
    convert raw using 1
    norm_num
  have support := C1092MMMMFirstPair.positive_support C B side same wn nn n.sine
    zero down mark absent
    (by apply (inside_clockwise _ _ _).mpr; convert n.marker using 1; norm_num)
    (by apply (inside_clockwise _ _ _).mpr; convert n.top using 1; norm_num)
    (by dsimp [B,clockwise]; linarith only [n.lowerV,n.cosine])
    (by simpa only [B,clockwise] using n.upperU)
    (by
      intro x y own
      exact apart y (-x)
        ⟨(inside_clockwise _ _ _).mp own.1,(inside_clockwise _ _ _).mp own.2⟩)
  have cp : 0<C.c := by change 0<W.c; linarith only [(normal_bounds wn).1]
  have cap : C.loU+C.side≤(7/20)*(C.c+(-C.s)) := by
    have normal : Normal C.c (-C.s) := wn
    apply le_of_not_gt
    intro high
    apply absent
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [zero.1,zero.2.2.2,down.2.2.1,high,cp,normal.1,normal.2.1]
  have small := C1092MMMMPairScalars.small_of_support wn nn side
    (by linarith only [zero.2.1]) (by linarith only [zero.2.2.2]) cap support
  have wc : 99/100<W.c := small.2
  let alpha := N.c*W.c+N.s*W.s
  let k := N.s*W.c-N.c*W.s
  have an : 0≤alpha := by
    have first := mul_nonneg (sub_nonneg.mpr n.canonical)
      (show 0≤W.c by linarith only [wc])
    have last := mul_nonneg n.sine.le (sub_nonneg.mpr wn.2.1)
    dsimp [alpha]; nlinarith only [first,last]
  have raw : alpha*(W.loU+W.side)+k*(W.loV+W.side)≤N.c+N.s-W.side := by
    dsimp [C,B,clockwise] at support
    dsimp [alpha,k]
    nlinarith only [support]
  have quarter := mul_pos n.sine
    (show 0<4*N.s-1-N.c by linarith only [n.halfLow])
  have scaled : 0<(1+N.c)*(4-4*N.c-N.s) := by
    nlinarith only [quarter,N.unit_normal]
  have gap : 0<4-4*N.c-N.s :=
    pos_of_mul_pos_right scaled (by linarith only [n.cosine])
  have face : 0<W.loV+W.side := by linarith only [origin.2.2.2]
  have longitudinal := mul_nonneg an
    (show 0≤W.loU+W.side by linarith only [origin.2.1])
  have transverse := mul_nonneg
    (mul_nonneg n.cosine.le wn.1) face.le
  have high : W.loV+W.side<25/33 := by
    apply lt_of_not_ge
    intro large
    have strict := mul_pos (show 0<W.c-99/100 by linarith only [wc]) face
    have prod : 3/4<W.c*(W.loV+W.side) := by nlinarith only [large,strict]
    have weighted := mul_pos n.sine (sub_pos.mpr prod)
    dsimp [alpha,k] at raw longitudinal transverse
    nlinarith only [raw,longitudinal,transverse,weighted,gap,side]
  exact ⟨small.1,small.2,high⟩

structure NorthwestCore (W : OpenSquare) : Prop where
  normal : Normal W.c W.s
  slope : 8*W.s<7*W.c
  origin : W.Inside 0 0
  marker : W.Inside (-7/20) (7/20)
  height : 23/25<W.loV+W.side
  lowerU : W.side-W.c+(2/5)*W.s≤W.loU+W.side

theorem northwest_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (E N : OpenSquare) (ep : SoutheastActual p E)
    (e : C1092TwoFifths.Southeast E)
    (np : C1092MMMPNortheastActualSign.PositiveActual p N) :
    ∃ W : OpenSquare,W.side=(owners p 7).side ∧
      (∀ x y,W.Inside x y↔(owners p 7).Inside (2+x) (2+y)) ∧ NorthwestCore W := by
  classical
  let Q := (owners p 7).translated 2 2
  obtain ⟨W,wc,canon,shape,inside,_⟩ := ClosedFrames.canonical_frame Q
  have actual (x y : ℝ) : W.Inside x y↔(owners p 7).Inside (2+x) (2+y) :=
    (inside x y).trans (inside_translated_iff _ _ _ _ _)
  have ws : W.side=(owners p 7).side := shape
  have side : 1<W.side := by rw [ws]; exact side_gt p 7
  have sameEW : E.side=W.side := ep.side.trans ((side_same p 5 7).trans ws.symm)
  have sameWN : W.side=N.side := ws.trans ((side_same p 7 6).trans np.side.symm)
  have origin : W.Inside 0 0 := by
    apply (actual _ _).mpr; norm_num; exact northwest_center p hf hb
  have leftHalf : W.Inside (-1/2) 0 := by
    apply (actual _ _).mpr; norm_num; exact northwest_left p hf hb
  have left : W.Inside (-13/50) 0 := by
    apply (actual _ _).mpr; norm_num; exact (northwest_pair p hf hb).2
  have north : W.Inside 0 (13/50) := by
    apply (actual _ _).mpr; norm_num; exact (northwest_pair p hf hb).1
  have diagonal : W.Inside (-1/2) (1/2) := by
    apply (actual _ _).mpr; norm_num; exact northwest_diagonal p hf hb
  have marker : W.Inside (-7/20) (7/20) := by
    apply (actual _ _).mpr; norm_num
    simpa [S12.marker] using marker_point p hf 7 11 (by decide +kernel)
  have missingSW : ¬W.Inside (-7/20) (-7/20) := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    have foreign : (owners p 4).Inside (33/20) (33/20) := by
      simpa [S12.marker] using marker_point p hf 4 8 (by decide +kernel)
    exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨h,foreign⟩
  have missingNE : ¬W.Inside (7/20) (7/20) := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    have foreign : (owners p 6).Inside (47/20) (47/20) := by
      simpa [S12.marker] using marker_point p hf 6 10 (by decide +kernel)
    exact owners_disjoint p hf 7 6 (by decide) _ _ ⟨h,foreign⟩
  have missingLeft : ¬W.Inside (-1) (39/100) := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    have foreign := local_wall_segment p mmmp hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at foreign
    exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨h,foreign⟩
  have missingFar : ¬W.Inside (-1) (2/5) := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨h,C1092MMMPLeftFar.point p hf hb⟩
  have apartEW : ∀ x y,¬(E.Inside x y ∧ W.Inside x y) :=
    fun x y own => owners_disjoint p hf 5 7 (by decide) _ _
      ⟨(ep.actual x y).mp own.1,(actual x y).mp own.2⟩
  have apartWN : ∀ x y,¬(W.Inside x y ∧ N.Inside x y) :=
    fun x y own => owners_disjoint p hf 7 6 (by decide) _ _
      ⟨(actual x y).mp own.1,(np.actual x y).mp own.2⟩
  have em : E.Inside (7/20) (-7/20) := by
    apply (ep.actual _ _).mpr; norm_num
    simpa [S12.marker] using marker_point p hf 5 9 (by decide +kernel)
  have eo : ¬E.Inside 0 0 := fun own => apartEW 0 0 ⟨own,origin⟩
  have ef : ¬E.Inside 1 (-13/50) := by
    intro own
    have h := (ep.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,near⟩
  have cap := (southeast_caps E e.side e.cosine e.sine ep.normal.2.1 em
    e.inner e.forward eo ef).2
  have eHeight := southeast_height E e cap
  have positive : 0<W.s := by
    apply lt_of_not_ge
    intro sign
    have wn : Normal W.c (-W.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_nonpos sign] using canon,
      by nlinarith only [W.unit_normal]⟩
    have n := northeast_core p hf hb N np
    have small := negative_northwest_profile W N side sameWN wn n origin leftHalf marker missingSW apartWN
    exact negative_northwest_impossible E W e sameEW wn small.2.1 small.1
      eHeight small.2.2 origin left north apartEW
  have wn : Normal W.c W.s := ⟨positive.le,
    by simpa only [abs_of_pos positive] using canon,W.unit_normal⟩
  have slope := positive_northwest_faces W side wn origin diagonal missingSW missingNE missingLeft
  have height := positive_northwest_height E W e sameEW wn eHeight origin left north apartEW
  have low := positive_northwest_left_face W wn slope height origin missingFar
  exact ⟨W,ws,actual,wn,slope,origin,marker,by linarith only [height],low⟩

#print axioms negative_northwest_profile
#print axioms northwest_profile
end N12Compact.C1092MMMPTwoFifthsEntrance
