import Compact.Completion.C1092.MPPMPositiveBoundaryOriginScalars
import Compact.Completion.C1092.WholeSupports
import Compact.Completion.OtherCases.WallProfile.VertexGeometry
import S12.SquareSupportBase

/-! POSITIVE-BOUNDARY-ORIGIN Theorem1, including its direct wall/corner
transfer. Every support and wall uses the same actual square. No side
upper cap, center bound, incoming angle partition or support is assumed. -/
namespace N12Compact.C1092MPPMPositiveBoundaryOrigin
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports Scalars
open Completion.OtherCases.WallProfile
set_option Elab.async false
noncomputable section

structure Input (C B : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=B.side
  central : Normal C.c C.s
  boundary : Normal B.c B.s
  lowerU : -C.c-C.s/2≤C.loU
  upperU : C.loU+C.side≤0
  upperV : C.loV+C.side≤C.s
  ordinaryG : C.Inside (-1) (-2/5)
  forward : C.Inside (-13/50) 0
  marker : B.Inside 0 (-543/500)
  outer : B.Inside (-2/5) (-1)
  near : B.Inside (-13/50) (-1)
  floor : ∀ x y,B.Inside x y → -2≤y
  corner : ∀ y : ℝ,-543/500≤y → y≤-1 → ¬B.Inside (-1) y
  apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)

private theorem lower_wall (B : OpenSquare) (normal : Normal B.c B.s)
    (floor : ∀ x y,B.Inside x y → -2≤y) : -2≤B.s*B.loU+B.c*B.loV := by
  have bb := normal_bounds normal
  have bp : 0<B.c := by linarith only [bb.1]
  have bound := square_support_bound B 0 (-1) 2
    (by intro x y own; have h := floor x y own; nlinarith only [h])
  have center : centerY B=B.s*(B.loU+B.side/2)+B.c*(B.loV+B.side/2) := by
    linear_combination B.s*(center_coordinates B).1+B.c*(center_coordinates B).2-
      centerY B*B.unit_normal
  simp only [squareRadius,zero_mul,one_mul,neg_mul,neg_zero,zero_add,
    abs_neg,abs_of_nonneg normal.1,abs_of_pos bp] at bound
  nlinarith only [bound,center]

private theorem missing_upper (C B : OpenSquare) (h : Input C B)
    (missing : ¬B.Inside 0 (-1)) : B.loU+B.side≤-B.s := by
  have bp : 0<B.c := by linarith only [(normal_bounds h.boundary).1]
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [h.marker.1,h.marker.2.2.1,h.outer.2.2.2,
      high,bp,h.boundary.1]

/-- The direct wall-point lemma at the exact corner segment. It includes
the cosine-threshold equality and the axial boundary orientation. -/
theorem direct_origin (C B : OpenSquare) (h : Input C B)
    (large : 457/500≤B.side*B.c) : B.Inside 0 (-1) := by
  by_contra missing
  have face := missing_upper C B h missing
  have bb := normal_bounds h.boundary
  have bp : 0<B.c := by linarith only [bb.1]
  have side : 1<B.side := by simpa only [h.same] using h.side
  have wall := lower_wall B h.boundary h.floor
  by_cases zero : B.s=0
  · nlinarith only [face,h.marker.2.1,zero]
  have rp : 0<B.s := lt_of_le_of_ne h.boundary.1 (Ne.symm zero)
  let x := B.c*B.loU-B.s*(B.loV+B.side)
  let y := B.s*B.loU+B.c*(B.loV+B.side)
  have closed : ClosedInside B x y := vertex B B.loU (B.loV+B.side)
    ⟨le_rfl,by linarith only [B.side_pos]⟩
    ⟨by linarith only [B.side_pos],le_rfl⟩
  have ywall : B.side*B.c-2≤y := by dsimp [y]; nlinarith only [wall]
  have ylow : -543/500≤y := by linarith only [ywall,large]
  have coordinate : B.c*x=B.loU-B.s*y := by
    dsimp [x,y]
    linear_combination B.loU*B.unit_normal
  have weighted := mul_nonneg h.boundary.1 (sub_nonneg.mpr ywall)
  have coefficient : 0<1+B.c*B.s := by nlinarith only [mul_pos bp rp]
  have strict := mul_pos (sub_pos.mpr side) coefficient
  have rectangle := mul_nonneg (show 0≤1-B.c by linarith only [bb.2.1])
    (show 0≤1-B.s by linarith only [bb.2.2.2.1])
  have left : x< -1 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg bp.le (show 0≤x+1 by linarith only [bad])
    nlinarith only [coordinate,face,weighted,strict,rectangle,product]
  by_cases high : -1≤y
  · apply h.corner (-1) (by norm_num) le_rfl
    have vcoordinate : -B.s*x+B.c*y=B.loV+B.side := by
      dsimp [x,y]
      linear_combination (B.loV+B.side)*B.unit_normal
    have first := mul_pos rp (show 0< -1-x by linarith only [left])
    have last := mul_nonneg bp.le (show 0≤y+1 by linarith only [high])
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [face,side,bb.2.1,h.outer.2.1,h.marker.2.2.1,
        bp,h.boundary.1,vcoordinate,first,last]
  · let t := (-1-x)/(-2/5-x)
    have den : 0< -2/5-x := by linarith only [left]
    have tn : 0<t := div_pos (by linarith only [left]) den
    have tu : t<1 := (div_lt_one den).mpr (by linarith)
    have relation : t*(-2/5-x)= -1-x := div_mul_cancel₀ _ den.ne'
    have xeq : (1-t)*x+t*(-2/5)= -1 := by nlinarith only [relation]
    have point := strict_closed_segment B x y (-2/5) (-1) t closed h.outer tn tu
    rw [xeq] at point
    have low := mul_nonneg (show 0≤1-t by linarith only [tu])
      (show 0≤y+543/500 by linarith only [ylow])
    have high := mul_nonneg (show 0≤1-t by linarith only [tu])
      (show 0≤-1-y by linarith only [high])
    exact h.corner ((1-t)*y+t*(-1))
      (by nlinarith only [low,tn]) (by nlinarith only [high]) point

private theorem boundary_data (C B : OpenSquare) (h : Input C B)
    (missing : ¬B.Inside 0 (-1)) :
    0<B.s ∧ (5/12)*B.c<B.s ∧
      B.loU+B.side≤-B.s ∧
      B.side*(B.c+B.s)-2+B.s^2≤B.c*(B.loV+B.side) := by
  have bb := normal_bounds h.boundary
  have bp : 0<B.c := by linarith only [bb.1]
  have face := missing_upper C B h missing
  have cosine : B.side*B.c<457/500 :=
    lt_of_not_ge (fun large => missing (direct_origin C B h large))
  have side : 1<B.side := by simpa only [h.same] using h.side
  have positive := mul_pos (sub_pos.mpr side) bp
  have cap : B.c<457/500 := by nlinarith only [cosine,positive]
  have ratio : (5/12)*B.c<B.s := by
    apply lt_of_not_ge
    intro bad
    have first := mul_nonneg (show 0≤5*B.c-12*B.s by linarith only [bad])
      (show 0≤5*B.c+12*B.s by linarith only [bp,h.boundary.1])
    have last := mul_pos (sub_pos.mpr cap)
      (show 0<457/500+B.c by linarith only [bp])
    nlinarith only [first,last,B.unit_normal]
  have rp : 0<B.s := by linarith only [ratio,bp]
  have wall := lower_wall B h.boundary h.floor
  have weight := mul_nonneg h.boundary.1
    (show 0≤-B.s-(B.loU+B.side) by linarith only [face])
  exact ⟨rp,ratio,face,by nlinarith only [wall,weight]⟩

private theorem cone (C B : OpenSquare) (h : Input C B) (nx ny : ℝ)
    (unit : nx^2+ny^2=1) (sep : upper B nx ny≤lower C nx ny) :
    0<ny ∧ nx<(30/37)*ny := by
  have first := (strict_bounds B _ _ nx ny unit h.near).2
  have last := (strict_bounds C _ _ nx ny unit h.forward).1
  have outer := (strict_bounds C _ _ nx ny unit h.ordinaryG).1
  constructor <;> linarith only [first,last,outer,sep]

private theorem separators (C B : OpenSquare) (h : Input C B) :
    upper B (-C.s) C.c≤C.loV ∨ B.loV+B.side≤lower C (-B.s) B.c := by
  have cp : 0<C.c := by linarith only [(normal_bounds h.central).1]
  have bp : 0<B.c := by linarith only [(normal_bounds h.boundary).1]
  have reverse (nx ny : ℝ) (sep : upper C nx ny≤lower B nx ny) :
      upper B (-nx) (-ny)≤lower C (-nx) (-ny) := by
    rw [upper_neg,lower_neg]
    linarith only [sep]
  have down (nx ny : ℝ) (unit : nx^2+ny^2=1) (yn : ny≤0)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    have failed := cone C B h nx ny unit sep
    linarith only [failed.1,yn]
  have axes := CongruentSAT.faceSeparation_of_disjoint B C h.same.symm
    (fun x y own => h.apart x y ⟨own.2,own.1⟩)
  change pairRadius B C≤|B.c*(centerX C-centerX B)+B.s*(centerY C-centerY B)| ∨
    pairRadius B C≤|-B.s*(centerX C-centerX B)+B.c*(centerY C-centerY B)| ∨
    pairRadius C B≤|C.c*(centerX C-centerX B)+C.s*(centerY C-centerY B)| ∨
    pairRadius C B≤|-C.s*(centerX C-centerX B)+C.c*(centerY C-centerY B)| at axes
  have split (nx ny rad : ℝ)
      (eq : supportRadius B nx ny+supportRadius C nx ny=rad)
      (axis : rad≤|nx*(centerX C-centerX B)+ny*(centerY C-centerY B)|) :=
    separated B C nx ny (by rwa [eq])
  rcases axes with bu|bv|cu|cv
  · rcases split _ _ _ (parallel_radius B C) bu with forward|backward
    · have failed := cone C B h B.c B.s B.unit_normal forward
      exfalso; linarith only [failed.2,h.boundary.2.1,bp]
    · exact False.elim (down (-B.c) (-B.s) (by nlinarith only [B.unit_normal])
        (by linarith only [h.boundary.1]) (reverse _ _ backward))
  · rcases split _ _ _ (transverse_radius B C) bv with forward|backward
    · right; simpa only [(ownV B).2] using forward
    · have opposite : upper B B.s (-B.c)≤lower C B.s (-B.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      exact False.elim (down B.s (-B.c) (by nlinarith only [B.unit_normal])
        (by linarith only [bp]) opposite)
  · have radius : supportRadius B C.c C.s+supportRadius C C.c C.s=pairRadius C B := by
      rw [add_comm]; exact parallel_radius C B
    rcases split _ _ _ radius cu with forward|backward
    · have failed := cone C B h C.c C.s C.unit_normal forward
      exfalso; linarith only [failed.2,h.central.2.1,cp]
    · exact False.elim (down (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (by linarith only [h.central.1]) (reverse _ _ backward))
  · have radius : supportRadius B (-C.s) C.c+supportRadius C (-C.s) C.c=pairRadius C B := by
      rw [add_comm]; exact transverse_radius C B
    rcases split _ _ _ radius cv with forward|backward
    · left; simpa only [(ownV C).1] using forward
    · have opposite : upper B C.s (-C.c)≤lower C C.s (-C.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      exact False.elim (down C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by linarith only [cp]) opposite)

/-- The full local positive-boundary origin transfer. -/
theorem origin (C B : OpenSquare) (h : Input C B) : B.Inside 0 (-1) := by
  by_contra missing
  obtain ⟨rp,ratio,face,wallD⟩ := boundary_data C B h missing
  let c := C.c
  let s := C.s
  let b := B.c
  let r := B.s
  let a := B.side
  let A := C.loU+C.side
  let J := B.loU+B.side
  let D := B.loV+B.side
  let k := c*b+s*r
  let delta := c*r-s*b
  let m := max (-delta) 0
  have cb := normal_bounds h.central
  have bb := normal_bounds h.boundary
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have bp : 0<b := by dsimp [b]; linarith only [bb.1]
  have kp : 0<k := by
    have first := mul_pos cp bp
    have last := mul_nonneg h.central.1 h.boundary.1
    dsimp [k,c,s,b,r] at *
    nlinarith only [first,last]
  have side : 1<a := by simpa only [h.same] using h.side
  have mn : 0≤m := le_max_right _ _
  have uFloor : a-c-s/2≤A := by dsimp [A,a,c,s]; rw [←h.same]; linarith only [h.lowerU]
  have vCap : C.loV≤s-a := by dsimp [a,s]; rw [←h.same]; linarith only [h.upperV]
  rcases separators C B h with central|boundary
  · have formula : upper B (-s) c=delta*J+k*D+a*m := by
      rw [(formulas B (-s) c).2,
        show (-s)*B.c+c*B.s=delta by dsimp [delta,b,r]; ring,
        show -(-s)*B.s+c*B.c=k by dsimp [k,b,r]; ring,
        max_eq_left kp.le]
      by_cases positive : 0≤delta
      · dsimp [J,D,a,m]
        rw [max_eq_left positive,max_eq_right (by linarith only [positive])]
        ring
      · have negative : delta≤0 := (lt_of_not_ge positive).le
        dsimp [J,D,a,m]
        rw [max_eq_right negative,max_eq_left (by linarith only [negative])]
        ring
    have wall := lower_wall B h.boundary h.floor
    have actualWall : 0≤r*J+b*D-a*(b+r)+2 := by dsimp [J,D,a,b,r]; nlinarith only [wall]
    have w0 := mul_nonneg kp.le actualWall
    have w1 := mul_nonneg h.central.1 (show 0≤-J-r by linarith only [face])
    have w2 := mul_nonneg bp.le (show 0≤s-a-C.loV by linarith only [vCap])
    have coefficient : 0≤b+k*(b+r)+b*m := by
      nlinarith only [mul_nonneg kp.le (show 0≤b+r by linarith only [bp,rp]),mul_nonneg bp.le mn,bp]
    have w3 := mul_nonneg (show 0≤a-1 by linarith only [side]) coefficient
    have positive := v_positive h.central h.boundary rp
    have identity : b*(upper B (-s) c-C.loV)=
        k*(r*J+b*D-a*(b+r)+2)+s*(-J-r)+b*(s-a-C.loV)+
        (a-1)*(b+k*(b+r)+b*m)+vMargin c s b r := by
      rw [formula]
      dsimp [vMargin,k,delta,m,b,r]
      linear_combination -s*J*B.unit_normal
    have separated := mul_nonpos_of_nonneg_of_nonpos bp.le
      (show upper B (-s) c-C.loV≤0 by linarith only [central])
    nlinarith only [identity,w0,w1,w2,w3,positive,separated]
  · by_cases order : 0≤delta
    · have formula : lower C (-r) b= -delta*A+k*C.loV := by
        exact lower_np C (-r) b (-delta) k
          (by dsimp [c,s,delta]; ring) (by dsimp [c,s,k]; ring)
          (by linarith only [order]) kp.le
      have phi : plusPhi c s b r=k*(1-s)+delta*(1-c-s/2) := by
        dsimp [plusPhi,k,delta,c,s]
        linear_combination r*C.unit_normal
      have w0 : 0≤b*D-a*(b+r)+2-r^2 := by linarith only [wallD]
      have w1 := mul_nonneg bp.le
        (show 0≤lower C (-r) b-D by linarith only [boundary])
      have w2 := mul_nonneg (mul_nonneg bp.le order) (sub_nonneg.mpr uFloor)
      have w3 := mul_nonneg (mul_nonneg bp.le kp.le)
        (show 0≤s-a-C.loV by linarith only [vCap])
      have coefficient : 0≤b+r+b*(k+delta) := by
        nlinarith only [mul_nonneg bp.le (add_nonneg kp.le order),bp,rp]
      have w4 := mul_nonneg (show 0≤a-1 by linarith only [side]) coefficient
      have positive := plus_positive h.central h.boundary rp order
      have identity : (b*D-a*(b+r)+2-r^2)+b*(lower C (-r) b-D)+
          b*delta*(A-(a-c-s/2))+b*k*(s-a-C.loV)=
          -plusMargin c s b r-(a-1)*(b+r+b*(k+delta)) := by
        rw [formula]
        dsimp [plusMargin]
        rw [phi]
        ring
      nlinarith only [identity,w0,w1,w2,w3,w4,positive]
    · have order : delta≤0 := (lt_of_not_ge order).le
      have formula : lower C (-r) b= -delta*C.loU+k*C.loV := by
        exact lower_nn C (-r) b (-delta) k
          (by dsimp [c,s,delta]; ring) (by dsimp [c,s,k]; ring)
          (by linarith only [order]) kp.le
      have uCap : C.loU≤-a := by dsimp [a]; rw [←h.same]; linarith only [h.upperU]
      have phi : minusPhi c s b r=k*(1-s)-delta := by dsimp [minusPhi,k,delta]; ring
      have w0 : 0≤b*D-a*(b+r)+2-r^2 := by linarith only [wallD]
      have w1 := mul_nonneg bp.le
        (show 0≤lower C (-r) b-D by linarith only [boundary])
      have w2 := mul_nonneg (mul_nonneg bp.le (show 0≤-delta by linarith only [order]))
        (show 0≤-a-C.loU by linarith only [uCap])
      have w3 := mul_nonneg (mul_nonneg bp.le kp.le)
        (show 0≤s-a-C.loV by linarith only [vCap])
      have coefficient : 0≤b+r+b*(k-delta) := by
        have product := mul_nonneg bp.le (show 0≤k-delta by linarith only [kp,order])
        linarith only [product,bp,rp]
      have w4 := mul_nonneg (show 0≤a-1 by linarith only [side]) coefficient
      have positive := minus_positive h.central h.boundary ratio order
      have identity : (b*D-a*(b+r)+2-r^2)+b*(lower C (-r) b-D)+
          b*(-delta)*(-a-C.loU)+b*k*(s-a-C.loV)=
          -minusMargin c s b r-(a-1)*(b+r+b*(k-delta)) := by
        rw [formula]
        dsimp [minusMargin]
        rw [phi]
        ring
      nlinarith only [identity,w0,w1,w2,w3,w4,positive]

end
#print axioms direct_origin
#print axioms origin
end N12Compact.C1092MPPMPositiveBoundaryOrigin
