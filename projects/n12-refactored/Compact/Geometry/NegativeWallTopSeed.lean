import Compact.Geometry.CentralLeftWallSeparation
import Compact.Geometry.C977NegativeCorner

/-! Conditional upper and lower faces of a negative left-wall square.
The upper face retains the explicit exclusion of (1,2.88); this exclusion
has not been derived for the paired upper corner in original C696/C977.
The central square need not own (1,2). All separation statements concern
the two full squares. -/
namespace N12Compact.NegativeWallTopSeed

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

private theorem sine_bound {c s : ℝ} (normal : Normal c s) : s≤71/100 := by
  have b := normal_bounds normal
  have order := mul_nonneg (sub_nonneg.mpr normal.2.1)
    (show 0≤c+s by linarith only [b.1,normal.1])
  have half : s^2≤1/2 := by nlinarith only [order,normal.2.2]
  nlinarith only [half,sq_nonneg (s-71/100)]

/-- A rational bound over the whole canonical arc; no angle subdivision. -/
theorem longitudinal_margin {C S d t : ℝ} (an : Normal C S) (wn : Normal d t) :
    0<1-d*(1-C)^2/2-t*(22/25+S*(1-C/2)) := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have sb := sine_bound an
  have tb := sine_bound wn
  have square : (1-C)^2≤9/100 := by
    have p := mul_nonneg (show 0≤C-7/10 by linarith only [ab.1])
      (show 0≤13/10-C by linarith only [ab.2.1])
    nlinarith only [p]
  have weighted := mul_nonneg (sub_nonneg.mpr wb.2.1) (sq_nonneg (1-C))
  have inner : S*(1-C/2)≤923/2000 := by
    have first := mul_nonneg an.1
      (show 0≤C/2-7/20 by linarith only [ab.1])
    nlinarith only [first,sb]
  have replace := mul_nonneg wn.1 (sub_nonneg.mpr inner)
  nlinarith only [square,weighted,replace,tb]

/-- The transverse branch has a nonnegative gap, including the common
horizontal frame. Strict ownership supplies strictness in the application. -/
theorem transverse_margin {C S d t : ℝ} (an : Normal C S) (wn : Normal d t) :
    C*t*((22/25)*t-(43/500)*d-1)+
      S*(1/2+(43/500)*t^2+(22/25)*d*t-d)≤0 := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have cp : 0<C := by linarith only [ab.1]
  have dp : 0≤d := by linarith only [wb.1]
  have dt := mul_nonneg dp wn.1
  have order := mul_nonneg (sub_nonneg.mpr wn.2.1)
    (show 0≤d+t by linarith only [wb.1,wn.1])
  have half : t^2≤1/2 := by nlinarith only [order,wn.2.2]
  have chord := mul_nonneg
    (show 0≤d+t-1 by linarith only [wb.2.2.2.2.1])
    (show 0≤3/2-(d+t) by linarith only [wb.2.2.2.2.2])
  have sum : 1+(4/5)*d*t≤d+t := by
    nlinarith only [chord,wn.2.2]
  have first : t*((22/25)*t-(43/500)*d-1)≤0 := by
    have bound : (22/25)*t-(43/500)*d-1≤0 := by
      linarith only [wb.2.2.2.1,dp]
    exact mul_nonpos_of_nonneg_of_nonpos wn.1 bound
  let B := 1/2+(43/500)*t^2+(22/25)*d*t-d
  have combined : t*((22/25)*t-(43/500)*d-1)+B<0 := by
    dsimp [B]
    nlinarith only [sum,half,dt]
  by_cases sign : 0≤B
  · have replacement := mul_nonneg (sub_nonneg.mpr an.2.1) sign
    have strict := mul_neg_of_pos_of_neg cp combined
    dsimp [B] at *
    nlinarith only [replacement,strict]
  · have second : S*B≤0 :=
      mul_nonpos_of_nonneg_of_nonpos an.1 (le_of_not_ge sign)
    have scaled := mul_nonpos_of_nonneg_of_nonpos cp.le first
    dsimp [B] at *
    nlinarith only [scaled,second]

/-- The two directed support modes remain valid without central ownership
of (1,2). The actual wall auxiliary point (1,2.4) supplies the upper anchor. -/
theorem alternatives (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (same : A.side=W.side) (side : 1<A.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (left : A.Inside (3/2) 2) (low : A.Inside 2 (3/2))
    (center : A.Inside (33/20) (33/20))
    (marker : W.Inside (457/500) 2) (high : W.Inside 1 (12/5))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    A.loV+A.side≤lower W (-A.s) A.c ∨
      W.loU+W.side≤lower A W.c W.s := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have ac : 0<A.c := by linarith only [ab.1]
  have wc : 0<W.c := by linarith only [wb.1]
  have au : ¬ (upper A A.c A.s≤lower W A.c A.s ∨
      upper W A.c A.s≤lower A A.c A.s) := by
    have a := strict_bounds A _ _ A.c A.s A.unit_normal left
    have m := strict_bounds W _ _ A.c A.s A.unit_normal marker
    have f := strict_bounds W _ _ A.c A.s A.unit_normal high
    rw [(ownU A).1] at *
    rintro (sep | sep)
    · nlinarith only [sep,a.2,m.1,ac]
    · nlinarith only [sep,f.2,cap,side,ab.2.1,an.1]
  have av : ¬ upper W (-A.s) A.c≤lower A (-A.s) A.c := by
    have unit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    have a := strict_bounds A _ _ (-A.s) A.c unit low
    have f := strict_bounds W _ _ (-A.s) A.c unit high
    intro sep
    nlinarith only [sep,a.1,f.2,ac,an.1]
  have wu : ¬ upper A W.c W.s≤lower W W.c W.s := by
    have a := strict_bounds A _ _ W.c W.s W.unit_normal low
    have m := strict_bounds W _ _ W.c W.s W.unit_normal marker
    rw [ws] at a m
    intro sep
    rw [ws] at sep
    nlinarith only [sep,a.2,m.1,wc,wn.1]
  have wv : ¬ (upper A (-W.s) W.c≤lower W (-W.s) W.c ∨
      upper W (-W.s) W.c≤lower A (-W.s) W.c) := by
    have unit : (-W.s)^2+W.c^2=1 := by nlinarith only [W.unit_normal]
    have a := strict_bounds A _ _ (-W.s) W.c unit left
    have p := strict_bounds A _ _ (-W.s) W.c unit center
    have m := strict_bounds W _ _ (-W.s) W.c unit marker
    have f := strict_bounds W _ _ (-W.s) W.c unit high
    rw [ws] at a p m f
    rintro (sep | sep) <;> rw [ws] at sep <;>
      nlinarith only [sep,a.2,p.1,m.1,f.2,wc,wn.1,wn.2.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint A W same apart
  change pairRadius A W ≤ |A.c*(centerX W-centerX A)+A.s*(centerY W-centerY A)| ∨
    pairRadius A W ≤ |-A.s*(centerX W-centerX A)+A.c*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |W.c*(centerX W-centerX A)+W.s*(centerY W-centerY A)| ∨
    pairRadius W A ≤ |-W.s*(centerX W-centerX A)+W.c*(centerY W-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius A nx ny+supportRadius W nx ny=R)
      (sep : R≤|nx*(centerX W-centerX A)+ny*(centerY W-centerY A)|) :=
    separated A W nx ny (by rwa [identity])
  rcases axes with sep | sep | sep | sep
  · exact False.elim (au (separateAxis _ _ _ (parallel_radius A W) sep))
  · rcases separateAxis _ _ _ (transverse_radius A W) sep with h | h
    · left; simpa only [(ownV A).2] using h
    · exact False.elim (av h)
  · have identity : supportRadius A W.c W.s+supportRadius W W.c W.s=pairRadius W A := by
      rw [add_comm]; exact parallel_radius W A
    rcases separateAxis _ _ _ identity sep with h | h
    · exact False.elim (wu h)
    · right; simpa only [(ownU W).2] using h
  · have identity : supportRadius A (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W A := by
      rw [add_comm]; exact transverse_radius W A
    exact False.elim (wv (separateAxis _ _ _ identity sep))

/-- The explicit upper-point exclusion forces the wall's upper V face, even
when A misses (1,2). No assumption on that disputed point occurs here. -/
theorem upper_face (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (same : A.side=W.side) (side : 1<A.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (left : A.Inside (3/2) 2) (low : A.Inside 2 (3/2))
    (center : A.Inside (33/20) (33/20))
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (113/50))
    (high : W.Inside 1 (12/5)) (missing : ¬W.Inside 1 (72/25))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    W.loV+W.side≤t+(72/25)*W.c := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have ac : 0<A.c := by linarith only [ab.1]
  have wc : 0<W.c := by linarith only [wb.1]
  have width : 1<W.side := by rwa [←same]
  let k := A.c*W.c-A.s*t
  let h := A.s*W.c+A.c*t
  have kp : 0≤k := by
    have first := mul_nonneg wc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 wc.le) (mul_nonneg ac.le wn.1)
  have wm := (negative_bands W t _ _ ws).mp marker
  have wp := (negative_bands W t _ _ ws).mp point
  have modes := alternatives A W t an wn ws same side cap left low center marker high apart
  have lowerU : W.loU<W.c-(72/25)*t := by
    by_contra no
    have forbidden : W.c-(72/25)*t≤W.loU := le_of_not_gt no
    rcases modes with central | wall
    · have form : lower W (-A.s) A.c = -h*(W.loU+W.side)+k*W.loV := by
        rw [lower_negative_nonpos W t (-A.s) A.c ws
          (by dsimp [h] at hp; nlinarith only [hp])
          (by dsimp [k] at kp; nlinarith only [kp])]
        dsimp [h,k]
        ring
      rw [form] at central
      have bottom := mul_nonneg hp
        (show 0≤W.loU+W.side-(W.c-(72/25)*t+1) by
          linarith only [forbidden,width])
      have top := mul_nonneg kp
        (show 0≤(457/500)*t+2*W.c-W.loV by linarith only [wm.2.2.1])
      have scalar := transverse_margin an wn
      have identity :
          -h*(W.c-(72/25)*t+1)+k*((457/500)*t+2*W.c)-
            (2*A.c-(3/2)*A.s) =
          A.c*t*((22/25)*t-(43/500)*W.c-1)+
            A.s*(1/2+(43/500)*t^2+(22/25)*W.c*t-W.c) := by
        dsimp [h,k]
        linear_combination (2*A.c-A.s)*wn.2.2
      nlinarith only [central,bottom,top,identity,scalar,left.2.2.2]
    · have form : lower A W.c W.s=k*A.loU-h*(A.loV+A.side) := by
        rw [ws,lower_in_bands]
        have u : W.c*A.c+(-t)*A.s=k := by dsimp [k]; ring
        have v : -W.c*A.s+(-t)*A.c=-h := by dsimp [h]; ring
        rw [u,v,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
        ring
      rw [form] at wall
      have upperU := mul_nonneg kp
        (show 0≤2*(A.c+A.s)-1-A.loU by linarith only [cap,side])
      have upperV := mul_nonneg hp
        (show 0≤A.loV+A.side-(2*A.c-(3/2)*A.s) by
          linarith only [left.2.2.2])
      have scalar := longitudinal_margin an wn
      have identity :
          W.c-(72/25)*t+1-
            (k*(2*(A.c+A.s)-1)-h*(2*A.c-(3/2)*A.s)) =
          1-W.c*(1-A.c)^2/2-t*(22/25+A.s*(1-A.c/2)) := by
        dsimp [h,k]
        linear_combination (2*t-(3/2)*W.c)*an.2.2
      nlinarith only [wall,upperU,upperV,identity,scalar,forbidden,width]
  by_contra no
  apply missing
  apply (negative_bands W t 1 (72/25) ws).mpr
  refine ⟨lowerU,?_,?_,?_⟩ <;>
    nlinarith only [wp.2.1,wp.2.2.1,no,wn.1,wc]

/-- Actual separation from A prevents the lower U face from excluding
the lower singleton's far seed. Its exclusion must therefore use V. -/
theorem lower_face (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (same : A.side=W.side) (side : 1<A.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (left : A.Inside (3/2) 2) (low : A.Inside 2 (3/2))
    (center : A.Inside (33/20) (33/20))
    (marker : W.Inside (457/500) 2) (high : W.Inside 1 (12/5))
    (missing : ¬W.Inside (19/25) (187/100))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) :
    (19/25)*t+(187/100)*W.c≤W.loV := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have ac : 0<A.c := by linarith only [ab.1]
  have wc : 0<W.c := by linarith only [wb.1]
  have width : 1<W.side := by rwa [←same]
  let k := A.c*W.c-A.s*t
  let h := A.s*W.c+A.c*t
  have kp : 0≤k := by
    have first := mul_nonneg wc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 wc.le) (mul_nonneg ac.le wn.1)
  have wm := (negative_bands W t _ _ ws).mp marker
  have modes := alternatives A W t an wn ws same side cap left low center marker high apart
  have lowerU : W.loU<(19/25)*W.c-(187/100)*t := by
    by_contra no
    have forbidden : (19/25)*W.c-(187/100)*t≤W.loU := le_of_not_gt no
    rcases modes with central | wall
    · have form : lower W (-A.s) A.c = -h*(W.loU+W.side)+k*W.loV := by
        rw [lower_negative_nonpos W t (-A.s) A.c ws
          (by dsimp [h] at hp; nlinarith only [hp])
          (by dsimp [k] at kp; nlinarith only [kp])]
        dsimp [h,k]
        ring
      rw [form] at central
      have bottom := mul_nonneg hp
        (show 0≤W.loU+W.side-((19/25)*W.c-(187/100)*t+1) by
          linarith only [forbidden,width])
      have top := mul_nonneg kp
        (show 0≤(457/500)*t+2*W.c-W.loV by linarith only [wm.2.2.1])
      have dsquare := mul_nonneg wc.le (sub_nonneg.mpr wb.2.1)
      have dt := mul_nonneg wc.le wn.1
      have coefficient : 37/50-(77/500)*t^2-(13/100)*W.c*t-W.c≤0 := by
        nlinarith only [dsquare,dt,wn.2.2,wb.1]
      have first := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ac.le wn.1)
        (show (77/500)*W.c-(13/100)*t-1≤0 by
          linarith only [wb.2.1,wn.1])
      have second := mul_nonpos_of_nonneg_of_nonpos an.1 coefficient
      have identity :
          -h*((19/25)*W.c-(187/100)*t+1)+k*((457/500)*t+2*W.c)-
            (2*A.c-(3/2)*A.s) =
          A.c*t*((77/500)*W.c-(13/100)*t-1)+
            A.s*(37/50-(77/500)*t^2-(13/100)*W.c*t-W.c) := by
        dsimp [h,k]
        linear_combination (2*A.c-(19/25)*A.s)*wn.2.2
      nlinarith only [central,bottom,top,identity,first,second,left.2.2.2]
    · have form : lower A W.c W.s=k*A.loU-h*(A.loV+A.side) := by
        rw [ws,lower_in_bands]
        have u : W.c*A.c+(-t)*A.s=k := by dsimp [k]; ring
        have v : -W.c*A.s+(-t)*A.c=-h := by dsimp [h]; ring
        rw [u,v,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
        ring
      rw [form] at wall
      have upperU := mul_nonneg kp
        (show 0≤2*(A.c+A.s)-1-A.loU by linarith only [cap,side])
      have upperV := mul_nonneg hp
        (show 0≤A.loV+A.side-(2*A.c-(3/2)*A.s) by
          linarith only [left.2.2.2])
      have sb := sine_bound an
      have tb := sine_bound wn
      have square : (1-A.c)^2≤9/100 := by
        have p := mul_nonneg (show 0≤A.c-7/10 by linarith only [ab.1])
          (show 0≤13/10-A.c by linarith only [ab.2.1])
        nlinarith only [p]
      have weighted := mul_nonneg (sub_nonneg.mpr wb.2.1) (sq_nonneg (1-A.c))
      have inner : A.s*(1-A.c/2)≤923/2000 := by
        have p := mul_nonneg an.1
          (show 0≤A.c/2-7/20 by linarith only [ab.1])
        nlinarith only [p,sb]
      have replacement := mul_nonneg wn.1 (sub_nonneg.mpr inner)
      have scalar : 0<1-(6/25)*W.c-W.c*(1-A.c)^2/2+
          t*(13/100-A.s*(1-A.c/2)) := by
        nlinarith only [square,weighted,replacement,tb,wb.2.1]
      have identity :
          (19/25)*W.c-(187/100)*t+1-
            (k*(2*(A.c+A.s)-1)-h*(2*A.c-(3/2)*A.s)) =
          1-(6/25)*W.c-W.c*(1-A.c)^2/2+
            t*(13/100-A.s*(1-A.c/2)) := by
        dsimp [h,k]
        linear_combination (2*t-(3/2)*W.c)*an.2.2
      nlinarith only [wall,upperU,upperV,identity,scalar,forbidden,width]
  by_contra no
  apply missing
  apply (negative_bands W t (19/25) (187/100) ws).mpr
  refine ⟨lowerU,?_,?_,?_⟩ <;>
    nlinarith only [wm.2.1,wm.2.2.2,no,wn.1,wn.2.1,wc]

/-- The two explicit face bounds confine the negative wall to a single
continuous small-tilt range. -/
theorem tilt {d t a lo hi : ℝ} (normal : Normal d t) (side : 1<a)
    (width : hi=lo+a) (bottom : (19/25)*t+(187/100)*d≤lo)
    (top : hi≤t+(72/25)*d) : t<51/100 := by
  have b := normal_bounds normal
  have span : a≤(101/100)*d+(6/25)*t := by linarith only [width,bottom,top]
  have dotSquare : ((4/5)*d+(3/5)*t)^2≤1 := by
    nlinarith only [normal.2.2,sq_nonneg (3*d-4*t)]
  have dot : (4/5)*d+(3/5)*t≤1 := by
    nlinarith only [dotSquare,sq_nonneg ((4/5)*d+(3/5)*t-1)]
  by_contra no
  have high : 51/100≤t := le_of_not_gt no
  linarith only [span,dot,side,high]

end N12Compact.NegativeWallTopSeed
