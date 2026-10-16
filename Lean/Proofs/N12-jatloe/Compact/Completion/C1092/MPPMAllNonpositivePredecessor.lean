import Compact.Completion.C1092.MPPMAllNonpositiveProfiles
import Compact.Completion.C1092.MPPMAllNonpositiveAlternatingScalars

/-! The same actual missing predecessor supplies the retaining square's
upper transverse support. All eight signed SAT axes are retained before
the two strict point comparisons remove six of them. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C977CornerSectorBounds C1092WholeSupports
set_option Elab.async false
noncomputable section

private theorem vertical_axes (C W : OpenSquare) (h : Core C)
    (wn : Normal W.c (-W.s)) (same : C.side=W.side)
    (marker : W.Inside (-7/20) (7/20))
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) :
    C.loV+C.side≤lower W (-C.s) C.c ∨ upper C (-W.s) W.c≤W.loV := by
  have cp : 0<C.c := by linarith only [(normal_bounds h.normal).1]
  have wp : 0<W.c := by linarith only [(normal_bounds wn).1]
  have choices := CongruentSAT.faceSeparation_of_disjoint C W same apart
  change pairRadius C W≤|C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W≤|-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C≤|W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C≤|-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at choices
  have separateAxis (nx ny R : ℝ)
      (radius : supportRadius C nx ny+supportRadius W nx ny=R)
      (sep : R≤|nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [radius])
  rcases choices with cu|cv|wu|wv
  · have cm := strict_bounds C _ _ C.c C.s C.unit_normal h.marker
    have wm := strict_bounds W _ _ C.c C.s C.unit_normal marker
    have p := strict_bounds C _ _ C.c C.s C.unit_normal h.ordinary
    rcases separateAxis _ _ _ (parallel_radius C W) cu with forward|reverse
    · linarith only [forward,cm.2,wm.1,h.normal.1]
    · linarith only [reverse,p.1,wm.2,cp,h.normal.2.1]
  · have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
    have cm := strict_bounds C _ _ (-C.s) C.c unit h.marker
    have wm := strict_bounds W _ _ (-C.s) C.c unit marker
    rcases separateAxis _ _ _ (transverse_radius C W) cv with forward|reverse
    · exact Or.inl (by simpa only [(ownV C).2] using forward)
    · linarith only [reverse,cm.1,wm.2,cp]
  · have radius : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]; exact parallel_radius W C
    have cm := strict_bounds C _ _ W.c W.s W.unit_normal h.marker
    have wm := strict_bounds W _ _ W.c W.s W.unit_normal marker
    have p := strict_bounds C _ _ W.c W.s W.unit_normal h.ordinary
    rcases separateAxis _ _ _ radius wu with forward|reverse
    · linarith only [forward,cm.2,wm.1,wn.1]
    · linarith only [reverse,p.1,wm.2,wp,wn.2.1]
  · have radius : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]; exact transverse_radius W C
    have unit : (-W.s)^2+W.c^2=1 := by nlinarith only [W.unit_normal]
    have cm := strict_bounds C _ _ (-W.s) W.c unit h.marker
    have wm := strict_bounds W _ _ (-W.s) W.c unit marker
    rcases separateAxis _ _ _ radius wv with forward|reverse
    · exact Or.inr (by simpa only [(ownV W).1] using forward)
    · linarith only [reverse,cm.1,wm.2,wp]

/-- Sections 5.1--5.2: the predecessor's own transverse normal and the
wrong relative order both fail. The remaining actual C-face gives the
strict cap, using only the genuine missing predecessor's derived faces. -/
theorem predecessor_cap (C W : OpenSquare) (h : Core C) (w : MissingPredecessor W)
    (same : C.side=W.side) (marker : W.Inside (-7/20) (7/20))
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) :
    C.loV+C.side<(43/500)*C.c+(12/25)*C.s := by
  let c := C.c
  let s := -C.s
  let b := W.c
  let r := -W.s
  let k := c*b+s*r
  let z := c*r-s*b
  have cn : Normal c s := h.normal
  have bn : Normal b r := w.normal
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have bp : 0<b := by linarith only [(normal_bounds bn).1]
  have f := faces C h
  have sp : 0<s := by dsimp only [s]; linarith only [f.negative]
  have kp : 0<k := by
    have first := mul_pos cp bp
    have last := mul_nonneg cn.1 bn.1
    dsimp only [k]
    nlinarith only [first,last]
  have kh : k≤1 := dot_le_one cn bn
  have sb := sine_small cn
  have wb := missing_bounds bn w.large
  have Apos : 0<C.loU+C.side := by
    linarith only [f.lowerU,h.side,(normal_bounds cn).2.1]
  have Uneg : C.loU<0 := by
    dsimp only [c,s] at cp
    linarith only [h.ordinary.1,cp,h.normal.2.1]
  have Hlow : -(13/50)*s<C.loV+C.side := by
    dsimp only [s]
    linarith only [h.forward.2.2.2]
  have Klow : W.loV< -(131/500) := by
    have sideW : 1<W.side := by rw [←same]; exact h.side
    have bound := wb.cosine
    change W.c<369/500 at bound
    linarith only [w.upperV,sideW,bound]
  have wu : (-W.s)*C.c+W.c*C.s=z := by dsimp only [z,c,s,b,r]; ring
  have wv : -(-W.s)*C.s+W.c*C.c=k := by dsimp only [k,c,s,b,r]; ring
  have cu : (-C.s)*W.c+C.c*W.s= -z := by dsimp only [z,c,s,b,r]; ring
  have cv : -(-C.s)*W.s+C.c*W.c=k := by dsimp only [k,c,s,b,r]; ring
  rcases vertical_axes C W h w.normal same marker apart with current|foreign
  · have zp : 0<z := by
      apply lt_of_not_ge
      intro zn
      have formula := lower_nn W (-C.s) C.c (-z) k cu cv (neg_nonneg.mpr zn) kp.le
      have Lneg : W.loU<0 := by
        have sideW : 1<W.side := by rw [←same]; exact h.side
        linarith only [w.upperU,sideW,w.normal.1]
      have first := mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr zn) Lneg.le
      have small0 := mul_nonneg (sub_nonneg.mpr cn.2.1) bn.1
      have small1 := mul_nonneg (show 0≤71/100-s by linarith only [sb])
        (sub_nonneg.mpr bn.2.1)
      have zlow : -1/20<z := by
        dsimp only [z] at *
        nlinarith only [small0,small1,wb.difference]
      have circle : k^2+z^2=1 := by
        dsimp only [k,z]
        linear_combination (b^2+r^2)*cn.2.2+bn.2.2
      have zs := mul_pos (show 0<z+1/20 by linarith only [zlow])
        (show 0<1/20-z by linarith only [zn])
      have klarge : 99/100<k := by
        apply lt_of_not_ge
        intro small
        have ks := mul_nonneg (show 0≤99/100-k by linarith only [small])
          (show 0≤99/100+k by linarith only [kp])
        nlinarith only [circle,zs,ks]
      have last := mul_lt_mul_of_pos_left Klow kp
      rw [formula] at current
      nlinarith only [current,first,last,klarge,Hlow,sb]
    have formula := lower_np W (-C.s) C.c (-z) k cu cv (neg_nonpos.mpr zp.le) kp.le
    have lowerJ : W.side-b-r≤W.loU+W.side := by
      dsimp only [b,r]
      linarith only [w.lowerU]
    have upperK : W.loV≤b-W.side := by dsimp only [b]; linarith only [w.upperV]
    have first := mul_le_mul_of_nonneg_left lowerJ zp.le
    have last := mul_le_mul_of_nonneg_left upperK kp.le
    have sideW : 1<W.side := by rw [←same]; exact h.side
    have excess := mul_pos (sub_pos.mpr sideW) (show 0<k+z by linarith only [kp,zp])
    have identity : -z*(1-b-r)+k*(b-1)=c*predecessorF b r-s*predecessorG b r := by
      dsimp only [z,k,predecessorF,predecessorG]
      linear_combination c*bn.2.2
    have coefficients := predecessor_coefficients bn w.large
    have fWeight := mul_lt_mul_of_pos_left coefficients.1 cp
    have gWeight := mul_le_mul_of_nonneg_left coefficients.2.le cn.1
    rw [formula] at current
    have cap : C.loV+C.side<(43/500)*c-(12/25)*s := by
      nlinarith only [current,first,last,excess,identity,fWeight,gWeight]
    simpa only [c, s, mul_neg, sub_neg_eq_add] using cap
  · have lowerSupport : -(13/50)*k*s<upper C (-W.s) W.c := by
      have last := mul_lt_mul_of_pos_left Hlow kp
      by_cases order : 0≤z
      · have first := mul_nonneg order Apos.le
        have formula := C1092MMMPEndingAxes.upper_nn C (-W.s) W.c z k wu wv order kp.le
        nlinarith only [formula,first,last]
      · have zn : z≤0 := (lt_of_not_ge order).le
        have first := mul_nonneg (neg_nonneg.mpr zn) (neg_nonneg.mpr Uneg.le)
        have formula := upper_np C (-W.s) W.c z k wu wv zn kp.le
        nlinarith only [formula,first,last]
    have product := mul_nonneg cn.1 (show 0≤1-k by linarith only [kh])
    nlinarith only [foreign,lowerSupport,product,Klow,sb]

end
#print axioms predecessor_cap
end N12Compact.C1092MPPMAllNonpositive
