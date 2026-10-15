import Compact.Geometry.PositiveCentralEscapeLeft

/-! A whole signed missing-west-point sector. The bottom singleton has a
positive canonical frame and the actual left singleton a strictly negative
one. The proof retains the left square's full support and container wall;
the weaker bottom/central/wall-only implication is false. -/
namespace N12Compact.PositiveCentralNegativeLeft

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds PositiveCentralEscapeOrder
set_option Elab.async false

private noncomputable def transpose (q : OpenSquare) : OpenSquare where
  c := q.c
  s := -q.s
  loU := q.loV
  loV := q.loU
  side := q.side
  unit_normal := by nlinarith only [q.unit_normal]
  side_pos := q.side_pos

private theorem inside_transpose (q : OpenSquare) (x y : ℝ) :
    (transpose q).Inside x y ↔ q.Inside y x := by
  dsimp [transpose, OpenSquare.Inside, InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

private theorem lower_transpose (q : OpenSquare) (x y : ℝ) :
    lower (transpose q) x y=lower q y x := by
  rw [lower_in_bands,lower_in_bands]
  dsimp [transpose]
  ring_nf

private theorem upper_transpose (q : OpenSquare) (x y : ℝ) :
    upper (transpose q) x y=upper q y x := by
  rw [upper_in_bands,upper_in_bands]
  dsimp [transpose]
  ring_nf

/-- The actual left/central separation is longitudinal in these opposite
signed frames. This is the coordinate transpose of the proved corner
transverse reduction, retaining its strict original seeds. -/
theorem left_alternatives (L A : OpenSquare) (r : ℝ)
    (ln : Normal L.c r) (ls : L.s=-r) (rp : 0<r)
    (an : Normal A.c A.s) (same : L.side=A.side) (side : 1<A.side)
    (lNear : L.Inside 1 (28/25)) (lFar : L.Inside (19/25) (187/100))
    (aMarker : A.Inside (33/20) (33/20)) (aE : A.Inside (87/50) 2)
    (aLow : A.Inside 2 (3/2)) (cap : A.loU+A.side≤2*(A.c+A.s))
    (apart : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y)) :
    L.loU+L.side≤lower A L.c L.s ∨ upper L A.c A.s≤A.loU := by
  have tn : Normal (transpose L).c (transpose L).s := by
    simpa only [transpose,ls,neg_neg] using ln
  have normalTransposeA : Normal (transpose A).c A.s := an
  have sep := C696PositiveCorner.transverse (transpose L) (transpose A) A.s
    rfl tn normalTransposeA (by simpa only [transpose,ls,neg_neg] using rp) same side
    ((inside_transpose _ _ _).mpr lNear) ((inside_transpose _ _ _).mpr lFar)
    ((inside_transpose _ _ _).mpr aMarker) ((inside_transpose _ _ _).mpr aE)
    ((inside_transpose _ _ _).mpr aLow) cap
    (fun x y h => apart y x
      ⟨(inside_transpose _ _ _).mp h.1,(inside_transpose _ _ _).mp h.2⟩)
  rcases sep with own | central
  · left
    change L.loU+L.side≤lower (transpose A) (-(-L.s)) L.c at own
    simpa only [neg_neg,lower_transpose] using own
  · right
    change upper (transpose L) A.s A.c≤A.loU at central
    simpa only [upper_transpose] using central

/-- The surviving bottom support places the upper-left vertex of A
strictly northwest of the actual left singleton's corner. This uses a
variable vertex, rather than any false fixed compulsory point. -/
theorem northwest_vertex (A : OpenSquare)
    (an : Normal A.c A.s) (side : 1<A.side) (small : A.side≤1001/1000)
    (marker : A.Inside (33/20) (33/20))
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (floor : 1+(A.c+A.s)*(1-2*A.s)<A.c*(A.loV+A.side))
    (cosine : 81/100<A.c) :
    A.c*A.loU-A.s*(A.loV+A.side)<1 ∧
      1<A.s*A.loU+A.c*(A.loV+A.side) := by
  have ab := normal_bounds an
  have cp : 0<A.c := by linarith only [ab.1]
  have sine : A.s<3/5 := by
    by_contra no
    have cprod := mul_pos (sub_pos.mpr cosine)
      (show 0<A.c+81/100 by linarith only [cp])
    have sprod := mul_nonneg (show 0≤A.s-3/5 by linarith only [no])
      (show 0≤A.s+3/5 by linarith only [an.1])
    nlinarith only [cprod,sprod,an.2.2]
  have ustrict : A.loU<2*(A.c+A.s)-1 := by linarith only [cap,side]
  have first := mul_pos (mul_pos cp cp) (sub_pos.mpr ustrict)
  have second := mul_nonneg an.1 (sub_nonneg.mpr floor.le)
  have identity :
      A.c-A.c^2*(2*(A.c+A.s)-1)+
        A.s*(1+(A.c+A.s)*(1-2*A.s)) = (A.c+A.s-1)^2/2 := by
    linear_combination (1/2-2*(A.c+A.s))*an.2.2
  have xgap : 0<A.c*(1-(A.c*A.loU-A.s*(A.loV+A.side))) := by
    nlinarith only [identity,first,second,sq_nonneg (A.c+A.s-1)]
  have x := pos_of_mul_pos_right xgap cp.le
  have markerU : (33/20)*(A.c+A.s)<A.loU+A.side := by
    nlinarith only [marker.2.1]
  have markerV : (33/20)*(A.c-A.s)<A.loV+A.side := by
    nlinarith only [marker.2.2.2]
  have mU := mul_nonneg an.1 (sub_nonneg.mpr markerU.le)
  have mV := mul_pos cp (sub_pos.mpr markerV)
  have size := mul_nonneg an.1 (sub_nonneg.mpr small)
  have y : 1<A.s*A.loU+A.c*(A.loV+A.side) := by
    nlinarith only [mU,mV,size,sine,an.2.2]
  exact ⟨by linarith only [x],y⟩

private theorem vertex_closed (A : OpenSquare) :
    ClosedInside A (A.c*A.loU-A.s*(A.loV+A.side))
      (A.s*A.loU+A.c*(A.loV+A.side)) := by
  have u : A.c*(A.c*A.loU-A.s*(A.loV+A.side))+
      A.s*(A.s*A.loU+A.c*(A.loV+A.side))=A.loU := by
    linear_combination A.loU*A.unit_normal
  have v : -A.s*(A.c*A.loU-A.s*(A.loV+A.side))+
      A.c*(A.s*A.loU+A.c*(A.loV+A.side))=A.loV+A.side := by
    linear_combination (A.loV+A.side)*A.unit_normal
  change A.loU≤_ ∧ _≤A.loU+A.side ∧ A.loV≤_ ∧ _≤A.loV+A.side
  rw [u,v]
  exact ⟨le_rfl,by linarith only [A.side_pos],by linarith only [A.side_pos],le_rfl⟩

private theorem left_axis_impossible (L A : OpenSquare) (r : ℝ)
    (ln : Normal L.c r) (ls : L.s=-r) (corner : L.Inside 1 1)
    (vertex : A.c*A.loU-A.s*(A.loV+A.side)<1 ∧
      1<A.s*A.loU+A.c*(A.loV+A.side)) :
    ¬L.loU+L.side≤lower A L.c L.s := by
  have lb := normal_bounds ln
  have lp : 0<L.c := by linarith only [lb.1]
  have low := (closed_bounds A _ _ L.c L.s (vertex_closed A)).1
  have high := corner.2.1
  rw [ls] at low high
  have first := mul_pos lp (sub_pos.mpr vertex.1)
  have second := mul_nonneg ln.1 (sub_nonneg.mpr vertex.2.le)
  intro sep
  nlinarith only [low,high,first,second,sep]

private theorem circle_chord {l r : ℝ} (ln : Normal l r) :
    1-l≤(3/7)*r := by
  have lb := normal_bounds ln
  have rmax : r≤5/7 := by linarith only [ln.2.1,lb.2.2.2.2.2]
  have positive : 0<1+l := by linarith only [lb.1]
  have scalar : 0≤(3/7)*(1+l)-r := by linarith only [lb.1,rmax]
  have weighted := mul_nonneg ln.1 scalar
  have identity : (1+l)*((3/7)*r-(1-l))=r*((3/7)*(1+l)-r) := by
    linear_combination ln.2.2
  have gap : 0≤(1+l)*((3/7)*r-(1-l)) := by linarith only [identity,weighted]
  have unscaled := nonneg_of_mul_nonneg_right gap positive
  linarith only [unscaled]

/-- The entire negative-left arc is bounded by its axis endpoint. The
coarse bounds here are consequences of the genuine northwest cap and the
bottom support; they are not saved angle intervals. -/
theorem negative_left_margin {p q C S l r : ℝ}
    (on : Normal p q) (an : Normal C S) (ln : Normal l r)
    (shallow : 9/10<p) (cosine : 81/100<C) (order : q≤S) :
    p*(2*(C+S)-1)≤S*B p q+p*C*(l+r)+S*l*(p+q) := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [ob.1]
  have cp : 0<C := by linarith only [ab.1]
  have qn : 0≤q := on.1
  have sn : 0≤S := an.1
  have rn : 0≤r := ln.1
  have qmax : q<11/25 := by
    by_contra no
    have first := mul_pos (sub_pos.mpr shallow)
      (show 0<p+9/10 by linarith only [pp])
    have second := mul_nonneg (show 0≤q-11/25 by linarith only [no])
      (show 0≤q+11/25 by linarith only [on.1])
    nlinarith only [first,second,on.2.2]
  have smax : S<3/5 := by
    by_contra no
    have first := mul_pos (sub_pos.mpr cosine)
      (show 0<C+81/100 by linarith only [cp])
    have second := mul_nonneg (show 0≤S-3/5 by linarith only [no])
      (show 0≤S+3/5 by linarith only [an.1])
    nlinarith only [first,second,an.2.2]
  have qratio : q≤p/2 := by linarith only [qmax,shallow]
  have sratio : S≤(3/4)*C := by linarith only [smax,cosine]
  have first := mul_nonneg an.1 (sub_nonneg.mpr qratio)
  have second := mul_nonneg (show 0≤(3/2)*p by positivity)
    (sub_nonneg.mpr sratio)
  have coefficient : p*C+S*(p+q)≤(17/8)*p*C := by
    nlinarith only [first,second]
  have coeffNonnegative : 0≤p*C+S*(p+q) := by positivity
  have chord := circle_chord ln
  have chordWeight := mul_nonneg coeffNonnegative (sub_nonneg.mpr chord)
  have coeffWeight := mul_nonneg (show 0≤(3/7)*r by positivity)
    (sub_nonneg.mpr coefficient)
  have product : 0≤p*C*r := by positivity
  have arc : p*(C+S)+S*q≤p*C*(l+r)+S*l*(p+q) := by
    nlinarith only [chordWeight,coeffWeight,product]
  have cosineOrder := cosine_order an on order
  have radial := mul_nonneg (sq_nonneg p) (sub_nonneg.mpr cosineOrder)
  have coefficientGap : 0≤p^2-S*(1-q) := by
    have square := mul_pos (sub_pos.mpr shallow)
      (show 0<p+9/10 by linarith only [pp])
    have product := mul_nonneg an.1 on.1
    nlinarith only [square,product,smax]
  have radial2 := mul_nonneg (sub_nonneg.mpr ob.2.1) coefficientGap
  have pB : p*B p q=p-2*p*q+q*(1-q) := by
    unfold B
    field_simp [pp.ne']
    <;> ring
  have endpoint :
      p*(S*B p q+p*(C+S)+S*q-p*(2*(C+S)-1))=
        p^2*(1-C)-S*(1-p)*(1-q) := by
    linear_combination S*pB-S*on.2.2
  have positive : 0≤p*(S*B p q+p*(C+S)+S*q-p*(2*(C+S)-1)) := by
    nlinarith only [endpoint,radial,radial2]
  have unscaled := nonneg_of_mul_nonneg_right positive pp
  linarith only [unscaled,arc]

/-- The two remaining actual supports are incompatible on the whole
negative-left arc. Eliminating the translation uses the left container
wall of L, rather than an assumed coordinate wall for A. -/
theorem support_impossible (O L A : OpenSquare) (r : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (ls : L.s=-r)
    (an : Normal A.c A.s) (same : L.side=A.side)
    (side : 1<A.side) (box : InsideContainer L)
    (shallow : 9/10<O.c) (cosine : 81/100<A.c) (order : O.s≤A.s)
    (bottom : B O.c O.s<O.loV+O.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (ol : O.loV+O.side≤lower L (-O.s) O.c)
    (la : upper L A.c A.s≤A.loU) : False := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have ab := normal_bounds an
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have oq : 0≤O.s := on.1
  have aq : 0≤A.s := an.1
  have rn : 0≤r := ln.1
  let H := O.s*L.c+O.c*r
  let J := O.c*L.c-O.s*r
  let K := A.c*L.c-A.s*r
  let D := A.c*r+A.s*L.c
  let E := O.c*A.c+O.s*A.s
  let T := O.c*A.c*(L.c+r)+A.s*L.c*(O.c+O.s)
  have hp : 0≤H := by dsimp [H]; positivity
  have dp : 0≤D := by dsimp [D]; positivity
  have ep : 0≤E := by dsimp [E]; positivity
  have tp : 0≤T := by dsimp [T]; positivity
  have jp : 0≤J := by
    have first := mul_nonneg op.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr on.2.1)
    dsimp [J]
    nlinarith only [first,second]
  have kp : 0≤K := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr an.2.1)
    dsimp [K]
    nlinarith only [first,second]
  have low : lower L (-O.s) O.c=-H*(L.loU+L.side)+J*L.loV := by
    rw [lower_in_bands,ls]
    have u : -O.s*L.c+O.c*(-r)=-H := by dsimp [H]; ring
    have v : -(-O.s)*(-r)+O.c*L.c=J := by dsimp [J]; ring
    rw [u,v,abs_of_nonpos (neg_nonpos.mpr hp),abs_of_nonneg jp]
    ring
  have high : upper L A.c A.s=K*(L.loU+L.side)+D*(L.loV+L.side) := by
    rw [upper_in_bands,ls]
    have u : A.c*L.c+A.s*(-r)=K := by dsimp [K]; ring
    have v : -A.c*(-r)+A.s*L.c=D := by dsimp [D]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonneg dp]
    ring
  have wall := FourSquareBLBridge.left_wall L lp.le box
  rw [ls,abs_neg,abs_of_nonneg ln.1] at wall
  dsimp [centerX] at wall
  rw [ls] at wall
  have position : 0≤L.c*L.loU+r*L.loV := by nlinarith only [wall]
  have identity :
      O.c*upper L A.c A.s-A.s*lower L (-O.s) O.c-L.side*T=
        E*(L.c*L.loU+r*L.loV) := by
    rw [low,high]
    dsimp [H,J,K,D,E,T]
    ring
  have wallWeighted := mul_nonneg ep position
  have bottomWeighted := mul_nonneg an.1
    (show 0≤lower L (-O.s) O.c-B O.c O.s by linarith only [bottom,ol])
  have sideWeighted := mul_nonneg tp
    (show 0≤L.side-1 by rw [same]; linarith only [side])
  have transfer : A.s*B O.c O.s+T≤O.c*upper L A.c A.s := by
    nlinarith only [identity,wallWeighted,bottomWeighted,sideWeighted]
  have margin := negative_left_margin on an ln shallow cosine order
  change O.c*(2*(A.c+A.s)-1)≤A.s*B O.c O.s+T at margin
  have upper : A.loU<2*(A.c+A.s)-1 := by linarith only [cap,side]
  have strict := mul_pos op (sub_pos.mpr upper)
  have separated := mul_nonneg op.le (sub_nonneg.mpr la)
  nlinarith only [transfer,margin,strict,separated]

/-- Every hypothesis is an actual square, point, container or pairwise
separation fact. In this signed sector the genuine left singleton forces
A to own the west point; no wall-square or top-seed premise is used. -/
theorem west (O L A : OpenSquare) (r : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (ls : L.s=-r) (rp : 0<r)
    (an : Normal A.c A.s) (sameOA : O.side=A.side) (sameLA : L.side=A.side)
    (side : 1<A.side) (small : A.side≤1001/1000)
    (oBox : InsideContainer O) (lBox : InsideContainer L)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (oMissingCorner : ¬O.Inside 1 1) (oMissingMarker : ¬O.Inside 2 (457/500))
    (lCorner : L.Inside 1 1) (lNear : L.Inside 1 (28/25))
    (lFar : L.Inside (19/25) (187/100))
    (aMarker : A.Inside (33/20) (33/20)) (aD : A.Inside 2 (87/50))
    (aE : A.Inside (87/50) 2) (aLeft : A.Inside (3/2) 2)
    (aLow : A.Inside 2 (3/2)) (cap : A.loU+A.side≤2*(A.c+A.s))
    (aMissingNW : ¬A.Inside (33/20) (47/20)) (aForeignLow : ¬A.Inside 1 (8/5))
    (oaApart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y))
    (olApart : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y))
    (laApart : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y)) : A.Inside 1 2 := by
  by_contra missing
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have ab := normal_bounds an
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<A.c := by linarith only [ab.1]
  have oq : 0≤O.s := on.1
  have aq : 0≤A.s := an.1
  have canonical : |O.s|≤O.c := by rw [abs_of_nonneg on.1]; exact on.2.1
  have oa := PositiveCentralTransverse.only_bottom_axis O A op canonical an sameOA
    side oBox oMarker oNear oFar oMissingCorner oMissingMarker
    aMarker aD aLeft aLow cap missing oaApart
  have westCap := PositiveCentralLeftBand.upper_face A side cp an.1 cap aMarker aLeft missing
  have order := PositiveCentralPositiveBottom.own_axis_angle O A on an sameOA
    side oBox oMarker oNear oMissingCorner oMissingMarker aLeft westCap oa
  have northwest := PositiveCentralLeftBand.northwest_cap A side cp an.1 an.2.1
    aLeft aLow aMissingNW aForeignLow
  have faces := C696PositiveCorner.corner_faces O on
    (by rwa [sameOA]) oBox oMarker oNear oMissingCorner oMissingMarker
  have pB : O.c*B O.c O.s=O.c-2*O.c*O.s+O.s-O.s^2 := by
    unfold B
    field_simp [op.ne']
    <;> ring
  have oldBoundary : O.c*C696CornerMargins.boundary O.c O.s=
      O.c+O.s-2*O.c*O.s-(457/500)*O.s^2 := by
    unfold C696CornerMargins.boundary
    field_simp [op.ne']
    <;> ring
  have weaker : B O.c O.s≤C696CornerMargins.boundary O.c O.s := by
    have scaled : 0≤O.c*(C696CornerMargins.boundary O.c O.s-B O.c O.s) := by
      nlinarith only [pB,oldBoundary,sq_nonneg O.s]
    have gap := nonneg_of_mul_nonneg_right scaled op
    linarith only [gap]
  have bottom := lt_of_le_of_lt weaker faces.2.2.2.2
  let D := O.c*A.s-O.s*A.c
  let K := O.c*A.c+O.s*A.s
  have cosineOrder := cosine_order an on order.le
  have dp : 0≤D := by
    have first := mul_nonneg on.1 (sub_nonneg.mpr cosineOrder)
    have second := mul_nonneg op.le (sub_nonneg.mpr order.le)
    dsimp [D]
    nlinarith only [first,second]
  have kp : 0≤K := by dsimp [K]; positivity
  have form : lower A (-O.s) O.c=D*A.loU+K*A.loV := by
    rw [lower_in_bands]
    have u : -O.s*A.c+O.c*A.s=D := by dsimp [D]; ring
    have v : -(-O.s)*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [u,v,abs_of_nonneg dp,abs_of_nonneg kp]
    ring
  have support : B O.c O.s <
      (O.c*A.s-O.s*A.c)*(2*(A.c+A.s)-1)+
        (O.c*A.c+O.s*A.s)*(A.loV+A.side-1) := by
    have first := mul_nonneg dp
      (show 0≤2*(A.c+A.s)-1-A.loU by linarith only [cap,side])
    have second := mul_nonneg kp (sub_nonneg.mpr side.le)
    rw [form] at oa
    dsimp [D,K] at first second oa
    nlinarith only [bottom,oa,first,second]
  have shallow := PositiveCentralEscapeLeft.bottom_cosine on an order.le support northwest
  have floor := base_bound on an order.le support
  have cosine := (northwest_threshold an floor northwest).1
  have vertex := northwest_vertex A an side small aMarker cap floor cosine
  have la : upper L A.c A.s≤A.loU := by
    rcases left_alternatives L A r ln ls rp an sameLA side lNear lFar
        aMarker aE aLow cap laApart with leftAxis | centralAxis
    · exact False.elim ((left_axis_impossible L A r ln ls lCorner vertex) leftAxis)
    · exact centralAxis
  have ol : O.loV+O.side≤lower L (-O.s) O.c := by
    rcases CornerSingletonPair.alternatives O L op lp (sameOA.trans sameLA.symm)
        oMarker oNear oFar lCorner olApart with own | left
    · rcases own with h | h
      · simpa only [(ownV O).2] using h.2
      · exact False.elim ((not_lt_of_ge on.1) h.1)
    · rcases left with h | h
      · rw [ls] at h
        exfalso
        linarith only [h.1,rp]
      · exact False.elim ((PositiveCentralEscapeLeft.negative_left_axis_impossible
          O L r on ln ls shallow.le (by rwa [sameOA]) oBox faces.2.2.1 lCorner) h.2)
  exact support_impossible O L A r on ln ls an sameLA side lBox shallow cosine order.le
    bottom cap ol la

#print axioms west

end N12Compact.PositiveCentralNegativeLeft
