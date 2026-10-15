import Compact.Completion.OtherCases.C983.F4BottomMidpoint
import Compact.Completion.OtherCases.C983.F4OuterScalars

/-! The outer-midpoint theorem, C983-F4-TOP-ONLY-8208-ENDING §4, using
the larger cap and strengthened own-normal estimate of
C983-F4-MIXED-NEGATIVE-8208-ENDING §4. All points refer to the same physical
W and E, in the chart translated by (-2,-2). -/
namespace N12Compact.Completion.OtherCases.C983.F4OuterMidpoint
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C981CompletionSupportForms
set_option Elab.async false

structure Input (W E : OpenSquare) (t : ℝ) : Prop where
  southeast : F4BottomMidpoint.SoutheastData E t
  same : W.side=E.side
  half : t/(1+E.c)<3/20
  lowerU : (13/50)*t≤E.loU
  east : E.Inside (1/2) 0
  southwest : W.Inside (-7/20) (-7/20)
  northwest : W.Inside (-7/20) (7/20)
  inward : W.Inside 0 (-13/50)
  center : W.Inside 0 0
  missingNorth : ¬W.Inside 0 (13/50)
  missingLeft : ¬W.Inside (-1) (13/50)
  missingCorner : ¬W.Inside (-1) (-2/5)
  apart : ∀ x y,¬(W.Inside x y ∧ E.Inside x y)

private theorem missing_faces (W E : OpenSquare) (t : ℝ) (data : Input W E t)
    (missing : ¬E.Inside 1 (-1/2)) :
    E.loU<E.c+t/2-1 ∧ E.loU<42/409 ∧ E.Inside 0 (-1/2) := by
  have e := data.southeast
  have m := e.marker
  have a := e.outer
  have d := e.elbow
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,
    mul_one,mul_neg,add_zero,zero_add] at m a d
  have cp : 0<E.c := by linarith only [e.cosine]
  have unit : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have cu : E.c≤1 := by nlinarith only [unit,sq_nonneg t,cp]
  have upper : E.loU+E.side≤E.c+t/2 := by
    apply le_of_not_gt
    intro high
    apply missing
    simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_one]
    refine ⟨?_,high,?_,?_⟩ <;>
      linarith only [m.1,a.2.2.2,e.upperV,e.sideLarge,cu,cp,e.sinePositive]
  have exactCap : E.loU<E.c+t/2-1 := by linarith only [upper,e.sideLarge]
  have cap := F4OuterScalars.outer_cap E.c t e.cosine e.sinePositive e.sineSmall unit data.half
  refine ⟨exactCap,lt_trans exactCap cap,?_⟩
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,zero_add]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [exactCap,cu,d.2.1,d.2.2.2,e.cosine,e.sinePositive,
      e.sineSmall,e.upperV,e.sideLarge]

private theorem positive_faces (W E : OpenSquare) (t : ℝ) (data : Input W E t)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missingC : ¬W.Inside 0 (-1/2)) :
    -(W.c/2)≤W.loV ∧ W.loU+W.side≤(13/50)*W.s ∧
    W.loV+W.side≤W.s+(13/50)*W.c ∧ 13/50<W.s := by
  have p := data.southwest
  have q := data.northwest
  have f := data.inward
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add] at p q f
  have side : 1<W.side := by simpa only [data.same] using data.southeast.sideLarge
  have cu : W.c≤1 := by nlinarith only [W.unit_normal,sq_nonneg W.s,cp]
  have low : -W.c/2≤W.loV := by
    apply le_of_not_gt
    intro inside
    apply missingC
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add]
    refine ⟨?_,?_,inside,?_⟩ <;>
      linarith only [p.1,f.2.1,f.2.2.2,cp,sn,order]
  have upperU : W.loU+W.side≤(13/50)*W.s := by
    apply le_of_not_gt
    intro high
    apply data.missingNorth
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add]
    refine ⟨?_,high,?_,?_⟩ <;>
      linarith only [f.1,f.2.2.1,q.2.2.2,cp,sn]
  have lowerL : W.loU< -W.c+(13/50)*W.s := by
    linarith only [upperU,side,cu]
  have upperV : W.loV+W.side≤W.s+(13/50)*W.c := by
    apply le_of_not_gt
    intro high
    apply data.missingLeft
    simp only [OpenSquare.Inside,InBands,mul_neg_one,neg_mul,neg_neg]
    refine ⟨lowerL,?_,?_,high⟩ <;>
      linarith only [f.2.1,p.2.2.1,cp,sn,order]
  have angle := F4OuterScalars.positive_angle W.c W.s cp sn W.unit_normal
    (by linarith only [low,upperV,side])
  exact ⟨low,upperU,upperV,angle⟩

private theorem negative_faces (W E : OpenSquare) (t r : ℝ) (data : Input W E t)
    (signed : W.s= -r) (cp : 0<W.c) (rn : 0≤r) (order : r≤W.c)
    (missingC : ¬W.Inside 0 (-1/2)) :
    W.loV+W.side≤(13/50)*W.c ∧ W.loU+W.side≤r/2 ∧ 39/100<r := by
  have p := data.southwest
  have q := data.northwest
  have f := data.inward
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add]
    at p q f
  have side : 1<W.side := by simpa only [data.same] using data.southeast.sideLarge
  have unit : W.c^2+r^2=1 := by simpa only [signed,neg_sq] using W.unit_normal
  have cu : W.c≤1 := by nlinarith only [unit,sq_nonneg r,cp]
  have highV : W.loV+W.side≤(13/50)*W.c := by
    apply le_of_not_gt
    intro high
    apply data.missingNorth
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add]
    refine ⟨?_,?_,?_,high⟩ <;>
      linarith only [q.1,f.2.1,p.2.2.1,cp,rn,order]
  have lowV : W.loV< -W.c/2 := by linarith only [highV,side,cu]
  have highU : W.loU+W.side≤r/2 := by
    apply le_of_not_gt
    intro high
    apply missingC
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add]
    refine ⟨?_,high,lowV,?_⟩ <;>
      linarith only [f.1,f.2.2.2,cp,rn]
  have steep : (9/100)*W.c<(7/20)*r := by linarith only [q.2.2.2,highV]
  have rp : 0<r := by linarith only [steep,cp]
  have angle : 39/100<r := by
    apply lt_of_not_ge
    intro small
    have quadratic : W.c≤1-r^2/2 := by nlinarith only [unit,sq_nonneg (W.c-1)]
    have monotone := mul_nonneg (show 0≤39/100-r by linarith only [small])
      (show 0≤1-(33/100)*(r+39/100) by linarith only [small,rn])
    have gap : (33/50)*W.c+r<1 := by nlinarith only [quadratic,monotone]
    have lowerV : W.loV< -r-(2/5)*W.c := by linarith only [highV,gap,side]
    have lowerU : -W.c+(2/5)*r≤W.loU := by
      apply le_of_not_gt
      intro low
      apply data.missingCorner
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg_one,neg_mul]
      refine ⟨low,?_,lowerV,?_⟩ <;>
        linarith only [p.2.1,p.2.2.2,cp,rn,order]
    have width : 1<W.c+r/10 := by linarith only [highU,lowerU,side]
    have square := mul_pos (show 0<W.c+r/10-1 by linarith only [width])
      (show 0<W.c+r/10+1 by linarith only [cp,rn])
    have ratio := mul_pos rp (sub_pos.mpr steep)
    nlinarith only [square,ratio,unit]
  exact ⟨highV,highU,angle⟩

private theorem positive_normals (W E : OpenSquare) (t : ℝ) (data : Input W E t)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missingC : ¬W.Inside 0 (-1/2)) (cap : E.loU<42/409) :
    lower E W.s (-W.c)<upper W W.s (-W.c) ∧
    lower E E.c E.s<upper W E.c E.s := by
  have e := data.southeast
  obtain ⟨low,upperU,upperV,angle⟩ := positive_faces W E t data cp sn order missingC
  have ep : 0<E.c := by linarith only [e.cosine]
  have eu : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have ecu : E.c≤1 := by nlinarith only [eu,sq_nonneg t,ep]
  have rp : 0<W.s := by linarith only [angle]
  let k := E.c*W.c-t*W.s
  let h := E.c*W.s+t*W.c
  have kp : 0<k := by
    have bound := mul_nonneg e.sinePositive.le (sub_nonneg.mpr order)
    have gap := mul_pos cp (show 0<E.c-t by linarith only [e.cosine,e.sineSmall])
    dsimp only [k]
    nlinarith only [bound,gap]
  have hp : 0<h := by dsimp only [h]; positivity
  have x := data.east
  have o := data.center
  have f := data.inward
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,add_zero] at x
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero,zero_add] at o f
  have hUp : h≤2*W.c := by
    have first := mul_nonneg ep.le (sub_nonneg.mpr order)
    have second := mul_nonneg cp.le (show 0≤2-E.c-t by linarith only [ecu,e.sineSmall])
    dsimp only [h]
    nlinarith only [first,second]
  have lower : lower E W.s (-W.c)=h*E.loU-k*(E.loV+E.side) := by
    rw [lower_in_bands,e.signed]
    have first : W.s*E.c+(-W.c)*(-t)=h := by dsimp only [h]; ring
    have second : -W.s*(-t)+(-W.c)*E.c= -k := by dsimp only [k]; ring
    rw [first,second,abs_of_nonneg hp.le,abs_of_nonpos (neg_nonpos.mpr kp.le)]
    ring
  have first := mul_pos hp (sub_pos.mpr cap)
  have second := mul_pos kp (show 0<E.loV+E.side by linarith only [x.2.2.2,e.sinePositive])
  have ownW := (strict_bounds W 0 (-13/50) W.s (-W.c)
    (by nlinarith only [W.unit_normal]) data.inward).2
  have ownNormal : lower E W.s (-W.c)<upper W W.s (-W.c) := by
    rw [lower]
    nlinarith only [first,second,hUp,ownW,cp]
  have upper : upper W E.c E.s=k*(W.loU+W.side)-h*W.loV := by
    rw [upper_in_bands,e.signed]
    have first : E.c*W.c+(-t)*W.s=k := by dsimp only [k]; ring
    have second : -E.c*W.s+(-t)*W.c= -h := by dsimp only [h]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonpos (neg_nonpos.mpr hp.le)]
    ring
  have side : 1<W.side := by simpa only [data.same] using e.sideLarge
  have support := F4OuterScalars.positive_support E.c t W.c W.s (W.loU+W.side) W.loV
    e.cosine e.sinePositive e.sineSmall eu cp sn order W.unit_normal angle o.2.1
    (by linarith only [f.2.2.1]) (by linarith only [upperV,side])
  have ownE : lower E E.c E.s<upper W E.c E.s := by
    rw [(ownU E).1,upper]
    dsimp only [k,h]
    exact lt_trans cap support
  exact ⟨ownNormal,ownE⟩

private theorem negative_normals (W E : OpenSquare) (t r : ℝ) (data : Input W E t)
    (signed : W.s= -r) (cp : 0<W.c) (rn : 0≤r) (order : r≤W.c)
    (missingC : ¬W.Inside 0 (-1/2)) (exactCap : E.loU<E.c+t/2-1)
    (cap : E.loU<42/409) :
    lower E W.c W.s<upper W W.c W.s ∧
    lower E E.c E.s<upper W E.c E.s := by
  have e := data.southeast
  obtain ⟨highV,highU,angle⟩ := negative_faces W E t r data signed cp rn order missingC
  have ep : 0<E.c := by linarith only [e.cosine]
  have eu : E.c^2+t^2=1 := by simpa only [e.signed,neg_sq] using E.unit_normal
  have wu : W.c^2+r^2=1 := by simpa only [signed,neg_sq] using W.unit_normal
  have rp : 0<r := by linarith only [angle]
  have sr : t<r := by linarith only [angle,e.sineSmall]
  have dc : W.c<E.c := by nlinarith only [wu,eu,sr,cp,ep,e.sinePositive]
  let k := E.c*W.c+t*r
  let h := E.c*r-t*W.c
  have kp : 0<k := by dsimp only [k]; positivity
  have hp : 0<h := by
    have first := mul_pos ep (sub_pos.mpr sr)
    have second := mul_pos e.sinePositive (sub_pos.mpr dc)
    dsimp only [h]
    nlinarith only [first,second]
  have x := data.east
  have f := data.inward
  have q := data.northwest
  simp only [OpenSquare.Inside,InBands,e.signed,neg_neg,mul_zero,zero_mul,add_zero] at x
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add] at f q
  have lower : lower E W.c W.s=k*E.loU-h*(E.loV+E.side) := by
    rw [lower_in_bands,e.signed,signed]
    have first : W.c*E.c+(-r)*(-t)=k := by dsimp only [k]; ring
    have second : -W.c*(-t)+(-r)*E.c= -h := by dsimp only [h]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonpos (neg_nonpos.mpr hp.le)]
    ring
  have first := mul_pos kp (sub_pos.mpr exactCap)
  have second := mul_pos hp (show 0<E.loV+E.side-t/2 by linarith only [x.2.2.2])
  have scalar := F4OuterScalars.negative_own_support E.c t W.c r
    e.cosine e.sinePositive e.sineSmall eu cp angle wu
  have ownW : lower E W.c W.s<upper W W.c W.s := by
    rw [lower,(ownU W).2]
    dsimp only [k,h] at first second ⊢
    nlinarith only [first,second,scalar,f.2.1]
  have upper : upper W E.c E.s=k*(W.loU+W.side)+h*(W.loV+W.side) := by
    rw [upper_in_bands,e.signed,signed]
    have first : E.c*W.c+(-t)*(-r)=k := by dsimp only [k]; ring
    have second : -E.c*(-r)+(-t)*W.c=h := by dsimp only [h]; ring
    rw [first,second,abs_of_nonneg kp.le,abs_of_nonneg hp.le]
    ring
  have firstPoint := mul_pos kp (show 0<W.loU+W.side-(13/50)*r by linarith only [f.2.1])
  have secondPoint := mul_pos hp
    (show 0<W.loV+W.side-(7/20)*(W.c-r) by linarith only [q.2.2.2])
  have scalar := F4OuterScalars.negative_support E.c t W.c r
    e.cosine e.sinePositive e.sineSmall eu cp angle order wu
  have identity : (13/50)*k*r+(7/20)*h*(W.c-r)=
      E.c*((61/100)*W.c*r-(7/20)*r^2)+
        t*((61/100)*r^2+(7/20)*W.c*r-7/20) := by
    dsimp only [k,h]
    linear_combination -(7/20)*t*wu
  have support : 42/409<k*(W.loU+W.side)+h*(W.loV+W.side) := by
    nlinarith only [firstPoint,secondPoint,scalar,identity]
  have ownE : lower E E.c E.s<upper W E.c E.s := by
    rw [(ownU E).1,upper]
    exact lt_trans cap support
  exact ⟨ownW,ownE⟩

/-- The outer point is strict in its actual southeast square. The temporary
midpoint is introduced only under the missing-outer-point supposition. -/
theorem inside (W E : OpenSquare) (t : ℝ) (data : Input W E t) : E.Inside 1 (-1/2) := by
  by_contra missing
  obtain ⟨exactCap,cap,cPoint⟩ := missing_faces W E t data missing
  obtain ⟨q,cp,range,shape,physical,_⟩ := ClosedFrames.canonical_frame W
  have bounds := abs_le.mp range
  have d : Input q E t :=
    { southeast := data.southeast
      same := shape.trans data.same
      half := data.half
      lowerU := data.lowerU
      east := data.east
      southwest := (physical _ _).mpr data.southwest
      northwest := (physical _ _).mpr data.northwest
      inward := (physical _ _).mpr data.inward
      center := (physical _ _).mpr data.center
      missingNorth := fun own => data.missingNorth ((physical _ _).mp own)
      missingLeft := fun own => data.missingLeft ((physical _ _).mp own)
      missingCorner := fun own => data.missingCorner ((physical _ _).mp own)
      apart := fun x y own => data.apart x y ⟨(physical _ _).mp own.1,own.2⟩ }
  have missingC : ¬q.Inside 0 (-1/2) := fun own => d.apart _ _ ⟨own,cPoint⟩
  have ep : 0<E.c := by linarith only [d.southeast.cosine]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper q nx ny≤lower E nx ny) : 0<nx ∧ ny<0 := by
    have p := (strict_bounds q _ _ nx ny unit d.southwest).2
    have m := (strict_bounds E _ _ nx ny unit d.southeast.marker).1
    have f := (strict_bounds q _ _ nx ny unit d.inward).2
    have c := (strict_bounds E _ _ nx ny unit cPoint).1
    constructor <;> linarith only [p,m,f,c,sep]
  have reverse (nx ny : ℝ) (sep : upper E nx ny≤lower q nx ny) :
      upper q (-nx) (-ny)≤lower E (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noWU (sep : upper q q.c q.s≤lower E q.c q.s ∨
      upper E q.c q.s≤lower q q.c q.s) : False := by
    rcases sep with forward | backward
    · by_cases sign : 0≤q.s
      · have normal := (cone _ _ q.unit_normal forward).2
        linarith only [normal,sign]
      · have no := (negative_normals q E t (-q.s) d (by ring) cp
          (by linarith only [sign]) (by linarith only [bounds.1]) missingC exactCap cap).1
        exact (not_lt_of_ge forward) no
    · have normal := (cone _ _ (by simpa only [neg_sq] using q.unit_normal)
        (reverse _ _ backward)).1
      linarith only [normal,cp]
  have noWV (sep : upper q (-q.s) q.c≤lower E (-q.s) q.c ∨
      upper E (-q.s) q.c≤lower q (-q.s) q.c) : False := by
    rcases sep with forward | backward
    · have normal := (cone _ _ (by nlinarith only [q.unit_normal]) forward).2
      linarith only [normal,cp]
    · have opposite : upper q q.s (-q.c)≤lower E q.s (-q.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      by_cases sign : 0≤q.s
      · have no := (positive_normals q E t d cp sign bounds.2 missingC cap).1
        exact (not_lt_of_ge opposite) no
      · have normal := (cone _ _ (by nlinarith only [q.unit_normal]) opposite).1
        linarith only [normal,sign]
  have noEU (sep : upper q E.c E.s≤lower E E.c E.s ∨
      upper E E.c E.s≤lower q E.c E.s) : False := by
    rcases sep with forward | backward
    · by_cases sign : 0≤q.s
      · exact (not_lt_of_ge forward) (positive_normals q E t d cp sign bounds.2 missingC cap).2
      · exact (not_lt_of_ge forward) (negative_normals q E t (-q.s) d (by ring) cp
          (by linarith only [sign]) (by linarith only [bounds.1]) missingC exactCap cap).2
    · have normal := (cone _ _ (by simpa only [neg_sq] using E.unit_normal)
        (reverse _ _ backward)).1
      linarith only [normal,ep]
  have noEV (sep : upper q (-E.s) E.c≤lower E (-E.s) E.c ∨
      upper E (-E.s) E.c≤lower q (-E.s) E.c) : False := by
    rcases sep with forward | backward
    · have normal := (cone _ _ (by nlinarith only [E.unit_normal]) forward).2
      linarith only [normal,ep]
    · have opposite : upper q E.s (-E.c)≤lower E E.s (-E.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      have normal := (cone _ _ (by nlinarith only [E.unit_normal]) opposite).1
      rw [d.southeast.signed] at normal
      linarith only [normal,d.southeast.sinePositive]
  have axes := CongruentSAT.faceSeparation_of_disjoint q E d.same d.apart
  change pairRadius q E≤|q.c*(centerX E-centerX q)+q.s*(centerY E-centerY q)| ∨
    pairRadius q E≤|-q.s*(centerX E-centerX q)+q.c*(centerY E-centerY q)| ∨
    pairRadius E q≤|E.c*(centerX E-centerX q)+E.s*(centerY E-centerY q)| ∨
    pairRadius E q≤|-E.s*(centerX E-centerX q)+E.c*(centerY E-centerY q)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius q nx ny+supportRadius E nx ny=radius)
      (axis : radius≤|nx*(centerX E-centerX q)+ny*(centerY E-centerY q)|) :=
    separated q E nx ny (by rwa [eq])
  rcases axes with wu | wv | eu | ev
  · exact noWU (separate _ _ _ (parallel_radius q E) wu)
  · exact noWV (separate _ _ _ (transverse_radius q E) wv)
  · have radius : supportRadius q E.c E.s+supportRadius E E.c E.s=pairRadius E q := by
      rw [add_comm]
      exact parallel_radius E q
    exact noEU (separate _ _ _ radius eu)
  · have radius : supportRadius q (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E q := by
      rw [add_comm]
      exact transverse_radius E q
    exact noEV (separate _ _ _ radius ev)

#print axioms inside
end N12Compact.Completion.OtherCases.C983.F4OuterMidpoint
