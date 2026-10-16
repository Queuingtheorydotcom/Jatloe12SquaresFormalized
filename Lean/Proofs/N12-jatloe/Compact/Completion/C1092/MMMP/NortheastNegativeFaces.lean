import Compact.Completion.C1092.ShortChordTable

/-! The actual corner, wall marker and center crosspoint replace an
unproved top origin in the MMMP nonpositive northeast face calculation. -/
namespace N12Compact.C1092MMMPNortheastNegativeFaces
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure Faces (B : OpenSquare) : Prop where
  lowerU : -B.c+B.s≤B.loU
  upperU : B.loU+B.side≤-(39/100)*B.c
  upperV : B.loV+B.side≤B.c+(39/100)*B.s
  sine : 9/20 < -B.s
  cosine : B.c<9/10

private theorem negative (B : OpenSquare) (b t : ℝ)
    (bframe : B.c=b) (tframe : B.s=-t) (bn : Normal b t) (side : 1<B.side)
    (M : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (I : ¬B.Inside (-39/100) 0) (J : ¬B.Inside (-39/100) 1)
    (W : ¬B.Inside (-543/500) 0) (K : ¬B.Inside (-1) 1)
    (A : ¬B.Inside (-1/2) 0) : Faces B := by
  classical
  have bb := normal_bounds bn
  have bp : 0<b := by linarith only [bb.1]
  have m := M
  have h1 := H1
  have h2 := H2
  dsimp [OpenSquare.Inside,InBands] at m h1 h2
  rw [bframe,tframe] at m h1 h2
  have upperV : B.loV+B.side≤b-(39/100)*t := by
    apply le_of_not_gt
    intro failure
    apply J
    dsimp [OpenSquare.Inside,InBands]
    rw [bframe,tframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,h2.1,m.2.1,m.2.2.1,bp,bn.1,bn.2.1]
  have upperU : B.loU+B.side≤-(39/100)*b := by
    apply le_of_not_gt
    intro failure
    have lowerV : B.loV < -(39/100)*t := by linarith only [upperV,side,bb.2.1]
    apply I
    dsimp [OpenSquare.Inside,InBands]
    rw [bframe,tframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,lowerV,h2.1,m.2.2.2,bp,bn.1]
  have tp : 0<t := by linarith only [upperU,m.2.1,bp]
  have lowerV : -(543/500)*t≤B.loV := by
    apply le_of_not_gt
    intro failure
    apply W
    dsimp [OpenSquare.Inside,InBands]
    rw [bframe,tframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,upperU,side,m.2.1,h2.2.2.2,bp,bn.1,bn.2.1,bb.2.1]
  have lowerU : -b-t≤B.loU := by
    apply le_of_not_gt
    intro failure
    have corner : B.loV+B.side≤b-t := by
      apply le_of_not_gt
      intro upper
      apply K
      dsimp [OpenSquare.Inside,InBands]
      rw [bframe,tframe]
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [failure,upper,h2.2.1,h2.2.2.1,bp,bn.1]
    have width : 1<b+(43/500)*t := by linarith only [lowerV,corner,side]
    have first := mul_pos (show 0<1+b by linarith only [bp])
      (show 0<b+(43/500)*t-1 by linarith only [width])
    have last := mul_nonneg bn.1 (show 0≤1-b by linarith only [bb.2.1])
    have factor : 0<t*((43/250)-t) := by nlinarith only [first,last,bn.2.2]
    have tiny : t<43/250 := by
      apply lt_of_not_ge
      intro bad
      have product := mul_nonpos_of_nonneg_of_nonpos bn.1
        (show 43/250-t≤0 by linarith only [bad])
      linarith only [factor,product]
    apply A
    dsimp [OpenSquare.Inside,InBands]
    rw [bframe,tframe]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upperU,side,m.2.1,m.2.2.2,corner,bb.1,bb.2.1,bn.1,bn.2.1,tiny]
  have width : B.side≤t+(61/100)*b := by linarith only [lowerU,upperU]
  have steep := C1092ShortChordTable.steep bn side width
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [bframe,tframe]
    linarith only [lowerU]
  · simpa only [bframe] using upperU
  · rw [bframe,tframe]
    linarith only [upperV]
  · simpa only [tframe,neg_neg] using steep.1
  · simpa only [bframe] using steep.2

theorem faces (B : OpenSquare) (bn : Normal B.c (-B.s)) (side : 1<B.side)
    (M : B.Inside (-7/20) (7/20))
    (H1 : B.Inside (-1) (13/50)) (H2 : B.Inside (-1) (2/5))
    (I : ¬B.Inside (-39/100) 0) (J : ¬B.Inside (-39/100) 1)
    (W : ¬B.Inside (-543/500) 0) (K : ¬B.Inside (-1) 1)
    (A : ¬B.Inside (-1/2) 0) : Faces B :=
  negative B B.c (-B.s) rfl (by ring) bn side M H1 H2 I J W K A

#print axioms faces
end N12Compact.C1092MMMPNortheastNegativeFaces
