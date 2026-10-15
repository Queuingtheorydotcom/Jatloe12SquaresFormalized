import Compact.Geometry.C696CornerMargins
import Compact.Geometry.C977NegativeCorner

/-! A complete signed corner sector from actual disjoint squares. The
bottom singleton has a positive canonical frame and the central square a
negative one. The extra central point (3/2,2) is a genuine geometric
consequence of the original marker triangle and the foreign singleton
segments; it is kept explicit here for reuse in other representatives. -/
namespace N12Compact.C696PositiveCorner

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

theorem corner_faces (O : OpenSquare) (normal : Normal O.c O.s)
    (side : 1<O.side) (box : InsideContainer O)
    (marker : O.Inside 1 (457/500)) (near : O.Inside (28/25) 1)
    (missing : ¬O.Inside 1 1) (missingM : ¬O.Inside 2 (457/500)) :
    0<O.s ∧ O.loV+O.side≤O.c-O.s ∧
      O.loU+O.side≤2*O.c+(457/500)*O.s ∧
      0≤O.s*O.loU+O.c*O.loV ∧
      C696CornerMargins.boundary O.c O.s < O.loV+O.side := by
  have b := normal_bounds normal
  have hc : 0<O.c := by linarith only [b.1]
  have m := marker
  have n := near
  dsimp [OpenSquare.Inside,InBands] at m n
  have cap : O.loV+O.side≤O.c-O.s := by
    by_contra no
    apply missing
    dsimp [OpenSquare.Inside,InBands]
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [no,m.1,n.2.1,n.2.2.1,hc,normal.1]
  have capU : O.loU+O.side≤2*O.c+(457/500)*O.s := by
    by_contra no
    apply missingM
    dsimp [OpenSquare.Inside,InBands]
    have smax : O.s≤5/7 := by linarith only [normal.2.1,b.2.2.2.2.2]
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [no,m.1,m.2.2.2,cap,side,hc,normal.1,b.2.1,smax]
  have bottom := ThreeSquare.bottom_wall O hc.le box
  rw [abs_of_nonneg normal.1] at bottom
  dsimp [centerY] at bottom
  have wall : 0≤O.s*O.loU+O.c*O.loV := by nlinarith only [bottom]
  have tilt : 0<O.s := by
    by_contra no
    have zero : O.s=0 := le_antisymm (le_of_not_gt no) normal.1
    have wall' := wall
    rw [zero,zero_mul,zero_add] at wall'
    have vlo := nonneg_of_mul_nonneg_right wall' hc
    rw [zero,sub_zero] at cap
    linarith only [vlo,cap,side,b.2.1]
  have uprod := mul_nonneg normal.1 (sub_nonneg.mpr capU)
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<O.c+O.s by linarith only [hc,normal.1])
  have formula : O.c*C696CornerMargins.boundary O.c O.s =
      O.c+O.s-2*O.c*O.s-(457/500)*O.s^2 := by
    unfold C696CornerMargins.boundary
    field_simp [ne_of_gt hc]
    <;> ring
  have scaled : 0<O.c*(O.loV+O.side-C696CornerMargins.boundary O.c O.s) := by
    nlinarith only [uprod,wall,strict,formula]
  have gap := pos_of_mul_pos_right scaled hc.le
  exact ⟨tilt,cap,capU,wall,by linarith only [gap]⟩

private theorem relative {c s C T : ℝ} (h : Normal c s) (H : Normal C T) :
    0≤c*C-s*T ∧ 0≤c*T+s*C := by
  have hc : 0≤c := le_trans h.1 h.2.1
  have hC : 0≤C := le_trans H.1 H.2.1
  have first := mul_nonneg hc (sub_nonneg.mpr H.2.1)
  have second := mul_nonneg H.1 (sub_nonneg.mpr h.2.1)
  constructor
  · nlinarith only [first,second]
  · exact add_nonneg (mul_nonneg hc H.1) (mul_nonneg h.1 hC)

/-- The new central crosspoint removes the only longitudinal axis not
already ruled out by the original singleton and central marker points. -/
theorem transverse (O A : OpenSquare) (T : ℝ) (hs : A.s=-T)
    (on : Normal O.c O.s) (an : Normal A.c T) (tilt : 0<O.s)
    (same : O.side=A.side) (side : 1<A.side)
    (oN : O.Inside (28/25) 1) (oF : O.Inside (187/100) (19/25))
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aNew : A.Inside (3/2) 2)
    (top : A.loV+A.side≤2*(A.c+T))
    (apart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y)) :
    O.loV+O.side≤lower A (-O.s) O.c ∨
      upper O T A.c≤A.loV := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have oc : 0<O.c := by linarith only [ob.1]
  have ac : 0<A.c := by linarith only [ab.1]
  have rel := relative on an
  let K := O.c*A.c-O.s*T
  let D := O.c*T+O.s*A.c
  have kp : 0≤K := rel.1
  have dp : 0<D := by
    have p := mul_pos tilt ac
    have n := mul_nonneg oc.le an.1
    dsimp [D]; nlinarith only [p,n]
  have new := (negative_bands A T _ _ hs).mp aNew
  have ownLong : ¬(upper O O.c O.s≤lower A O.c O.s ∨
      upper A O.c O.s≤lower O O.c O.s) := by
    have ofar := strict_bounds O _ _ O.c O.s O.unit_normal oF
    have anear := strict_bounds A _ _ O.c O.s O.unit_normal aD
    have onear := strict_bounds O _ _ O.c O.s O.unit_normal oN
    rintro (sep | sep)
    · have form : lower A O.c O.s=K*A.loU+D*A.loV := by
        exact lower_negative_pos A T _ _ hs kp dp.le
      have up := mul_nonneg kp (sub_nonneg.mpr new.1.le)
      have vp := mul_nonneg dp.le (sub_nonneg.mpr top)
      have strict := mul_pos dp (sub_pos.mpr side)
      have scalar := C696CornerMargins.longitudinal on an
      have identity :
          K*((3/2)*A.c-2*T)+D*(2*(A.c+T)-1)=
            O.c*(3/2+(1/2)*T^2-T)+O.s*(2+(1/2)*A.c*T-A.c) := by
        dsimp [K,D]
        linear_combination ((3/2)*O.c+2*O.s)*an.2.2
      nlinarith only [sep,form,up,vp,strict,scalar,identity,ofar.2]
    · nlinarith only [sep,anear.2,onear.1,oc,on.1]
  have centralLong : ¬(upper O A.c (-T)≤lower A A.c (-T) ∨
      upper A A.c (-T)≤lower O A.c (-T)) := by
    have unit : A.c^2+(-T)^2=1 := by nlinarith only [an.2.2]
    have ofar := strict_bounds O _ _ A.c (-T) unit oF
    have ap := strict_bounds A _ _ A.c (-T) unit aP
    have ad := strict_bounds A _ _ A.c (-T) unit aD
    have onear := strict_bounds O _ _ A.c (-T) unit oN
    rintro (sep | sep) <;>
      nlinarith only [sep,ofar.2,ap.1,ad.2,onear.1,ac,an.1,an.2.1]
  have reverseO : ¬upper A (-O.s) O.c≤lower O (-O.s) O.c := by
    have unit : (-O.s)^2+O.c^2=1 := by nlinarith only [O.unit_normal]
    have ap := strict_bounds A _ _ (-O.s) O.c unit aP
    have op := strict_bounds O _ _ (-O.s) O.c unit oN
    intro sep
    nlinarith only [sep,ap.2,op.1,oc,on.1,on.2.1]
  have reverseA : ¬upper A T A.c≤lower O T A.c := by
    have unit : T^2+A.c^2=1 := by nlinarith only [an.2.2]
    have ap := strict_bounds A _ _ T A.c unit aP
    have op := strict_bounds O _ _ T A.c unit oN
    intro sep
    nlinarith only [sep,ap.2,op.1,ac,an.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint O A same apart
  change pairRadius O A ≤ |O.c*(centerX A-centerX O)+O.s*(centerY A-centerY O)| ∨
    pairRadius O A ≤ |-O.s*(centerX A-centerX O)+O.c*(centerY A-centerY O)| ∨
    pairRadius A O ≤ |A.c*(centerX A-centerX O)+A.s*(centerY A-centerY O)| ∨
    pairRadius A O ≤ |-A.s*(centerX A-centerX O)+A.c*(centerY A-centerY O)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius O nx ny+supportRadius A nx ny=R)
      (sep : R≤|nx*(centerX A-centerX O)+ny*(centerY A-centerY O)|) :=
    separated O A nx ny (by rwa [identity])
  rcases axes with ou | ov | au | av
  · exact False.elim (ownLong (separateAxis _ _ _ (parallel_radius O A) ou))
  · have sep := separateAxis _ _ _ (transverse_radius O A) ov
    rcases sep with sep | sep
    · left; simpa only [(ownV O).2] using sep
    · exact False.elim (reverseO sep)
  · have identity : supportRadius O A.c A.s+supportRadius A A.c A.s=pairRadius A O := by
      rw [add_comm]; exact parallel_radius A O
    have sep := separateAxis _ _ _ identity au
    rw [hs] at sep
    exact False.elim (centralLong sep)
  · have identity : supportRadius O (-A.s) A.c+supportRadius A (-A.s) A.c=pairRadius A O := by
      rw [add_comm]; exact transverse_radius A O
    have sep := separateAxis _ _ _ identity av
    rw [hs,neg_neg] at sep
    rcases sep with sep | sep
    · right
      have own := (ownV A).1
      rw [hs,neg_neg] at own
      simpa only [own] using sep
    · exact False.elim (reverseA sep)

/-- Full positive-corner/negative-central sector. Strictness comes from
the genuine owned points and side greater than one, including all touching
face cases in the separating-axis theorem. -/
theorem point (O A L : OpenSquare) (T : ℝ) (hs : A.s=-T)
    (on : Normal O.c O.s) (an : Normal A.c T)
    (same : O.side=A.side) (side : 1<A.side) (box : InsideContainer O)
    (oM : O.Inside 1 (457/500)) (oN : O.Inside (28/25) 1)
    (oF : O.Inside (187/100) (19/25))
    (missing : ¬O.Inside 1 1) (missingM : ¬O.Inside 2 (457/500))
    (aP : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aE : A.Inside (87/50) 2) (aNew : A.Inside (3/2) 2)
    (lN : L.Inside 1 (28/25)) (lW : L.Inside 1 (87/50))
    (oa : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y))
    (al : ∀ x y, ¬(A.Inside x y ∧ L.Inside x y)) : A.Inside 2 2 := by
  by_contra no
  have ob := normal_bounds on
  have ab := normal_bounds an
  have oc : 0<O.c := by linarith only [ob.1]
  have ac : 0<A.c := by linarith only [ab.1]
  have oside : 1<O.side := by simpa only [same] using side
  obtain ⟨tilt,cap,capU,wall,face⟩ := corner_faces O on oside box oM oN missing missingM
  have p := (negative_bands A T _ _ hs).mp aP
  have d := (negative_bands A T _ _ hs).mp aD
  have e := (negative_bands A T _ _ hs).mp aE
  have top : A.loV+A.side≤2*(A.c+T) := by
    by_contra escape
    apply no
    apply (negative_bands A T 2 2 hs).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [escape,p.1,p.2.2.1,d.2.1,ac,an.1,an.2.1]
  have aTilt : 0<T := by
    by_contra failure
    have zero : T=0 := le_antisymm (le_of_not_gt failure) an.1
    rw [zero] at e top
    nlinarith only [e.2.2.2,top]
  let K := O.c*A.c-O.s*T
  let D := O.c*T+O.s*A.c
  have rel := relative on an
  have kp : 0≤K := rel.1
  have dp : 0<D := by
    have positive := mul_pos tilt ac
    have nonnegative := mul_nonneg oc.le an.1
    dsimp [D]; nlinarith only [positive,nonnegative]
  have relO : O.c*D-O.s*K=T := by
    dsimp [D,K]; linear_combination T*on.2.2
  have relA : A.c*K+T*D=O.c := by
    dsimp [D,K]; linear_combination O.c*an.2.2
  have sep := transverse O A T hs on an tilt same side oN oF aP aD aNew top oa
  have bottomSep : O.loV+O.side≤-D*(A.loU+A.side)+K*A.loV := by
    rcases sep with lowerSep | upperSep
    · have form : lower A (-O.s) O.c=-D*(A.loU+A.side)+K*A.loV := by
        have hu : -O.s*A.c-O.c*T≤0 := by dsimp [D] at dp; linarith only [dp]
        have hv : 0≤-O.s*T+O.c*A.c := by dsimp [K] at kp; linarith only [kp]
        have f := lower_negative_nonpos A T (-O.s) O.c hs hu hv
        dsimp [D,K]; nlinarith only [f]
      simpa only [form] using lowerSep
    · have form : upper O T A.c=D*(O.loU+O.side)+K*(O.loV+O.side) := by
        rw [upper_in_bands]
        have hu : T*O.c+A.c*O.s=D := by dsimp [D]; ring
        have hv : -T*O.s+A.c*O.c=K := by dsimp [K]; ring
        rw [hu,hv,abs_of_nonneg dp.le,abs_of_nonneg kp]
        ring
      have scalar := C696CornerMargins.central_axis on an tilt
      have cornerScaled := mul_le_mul_of_nonneg_left cap oc.le
      have uGap : 0≤O.s*O.loU-O.c*(O.side-O.c+O.s) := by
        nlinarith only [cornerScaled,wall]
      have first := mul_nonneg an.1 uGap
      have second := mul_nonneg (mul_nonneg tilt.le kp) wall
      have coefficient : 0<O.c*(T+O.s*(D+K+1)) := by
        have inside : 0<T+O.s*(D+K+1) := by
          have positive := mul_pos tilt (show 0<D+K+1 by linarith only [dp,kp])
          linarith only [positive,an.1]
        exact mul_pos oc inside
      have strict := mul_pos (sub_pos.mpr oside) coefficient
      have identity :
          O.c*O.s*(upper O T A.c+O.side)=
            O.s*T*O.loU+O.s*K*(O.s*O.loU+O.c*O.loV)+
              O.side*O.c*O.s*(D+K+1) := by
        rw [form]
        linear_combination O.s*O.loU*relO
      have scalarScaled := mul_le_mul_of_nonneg_left scalar (mul_pos oc tilt).le
      have formula : O.c*O.s*((T/O.s)*(1-O.c+O.s)+D+K+1)=
          O.c*T*(1-O.c+O.s)+O.c*O.s*(D+K+1) := by
        field_simp [ne_of_gt tilt]
        <;> ring
      have width := mul_le_mul_of_nonneg_left top (mul_pos oc tilt).le
      have separated := mul_le_mul_of_nonneg_left upperSep (mul_pos oc tilt).le
      rw [same] at first identity strict
      dsimp [D,K] at scalarScaled
      dsimp [D,K] at formula identity first second strict width separated ⊢
      exfalso
      nlinarith only [identity,formula,first,second,strict,scalarScaled,width,separated]
  let R := -D*(A.loU+A.side)+K*A.loV
  have reach : C696CornerMargins.boundary O.c O.s < R :=
    lt_of_lt_of_le face bottomSep
  have left : A.c*A.loU+T*A.loV<1 := by
    by_contra failure
    have leftProd := mul_nonneg dp.le (sub_nonneg.mpr (le_of_not_gt failure))
    have topProd := mul_nonneg oc.le (sub_nonneg.mpr top)
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<O.c+A.c*D by
        have product := mul_nonneg ac.le dp.le
        linarith only [oc,product])
    have identity : A.c*R=O.c*A.loV-D*(A.c*A.loU+T*A.loV)-A.c*D*A.side := by
      dsimp [R]
      linear_combination A.loV*relA
    have formula :
        A.c*(O.c*(2+(T-1)/A.c-T)-O.s*(1+A.c))=
          O.c*(2*(A.c+T)-1)-D-A.c*D := by
      dsimp [D]
      field_simp [ne_of_gt ac]
      <;> ring
    have compare := C696CornerMargins.left_comparison on an
    have high := mul_le_mul_of_nonneg_left compare ac.le
    have low := mul_lt_mul_of_pos_left reach ac
    nlinarith only [identity,formula,leftProd,topProd,strict,high,low]
  have near : A.loU<A.c-(28/25)*T := by
    by_contra failure
    have lowerProd := mul_nonneg dp.le (sub_nonneg.mpr (le_of_not_gt failure))
    have topProd := mul_nonneg kp (sub_nonneg.mpr top)
    have strict := mul_pos (sub_pos.mpr side) (show 0<D+K by linarith only [dp,kp])
    have identity :
        -D*(A.c-(28/25)*T+1)+K*(2*(A.c+T)-1)=
          O.c*(2-(22/25)*T^2+A.c*T-A.c-T)-
            O.s*(1+T^2+(22/25)*A.c*T+A.c-T) := by
      dsimp [D,K]
      linear_combination (2*O.c-O.s)*an.2.2
    have compare := C696CornerMargins.near_comparison on an
    dsimp [R] at reach
    nlinarith only [identity,lowerProd,topProd,strict,compare,reach]
  obtain ⟨x,y,ha,hl⟩ := foreign_segment_overlap A L T hs an aTilt side aD aE top left near lN lW
  exact al x y ⟨ha,hl⟩

end N12Compact.C696PositiveCorner
