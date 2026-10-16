import Compact.Geometry.PositiveBottomNextAxes
import Compact.Geometry.C977CornerSectorBounds

/-! One full three-square support cycle. The actual positive singleton
precedes a negative bottom wall on the singleton axis, and that wall
precedes the negative central square on the central transverse axis.
Real bottom containment and the genuine central upper face close this
entire selector for every three canonical angles. -/
namespace N12Compact.PositiveBottomNegativeWallCycle

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
set_option Elab.async false

private theorem defect {c s : ℝ} (h : Normal c s) :
    s^2/2≤1-c ∧ 1-c≤(3/5)*s^2 := by
  have b := normal_bounds h
  have first := sq_nonneg (1-c)
  have last := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤(3/5)*c-2/5 by linarith only [b.1])
  constructor <;> nlinarith only [h.2.2,first,last]

private theorem quadratic_between (a b k low high x : ℝ)
    (kp : 0≤k) (lo : low≤x) (hi : x≤high)
    (left : 0≤a+b*low-k*low^2)
    (right : 0≤a+b*high-k*high^2) : 0≤a+b*x-k*x^2 := by
  by_cases eq : low=high
  · have xe : x=low := by linarith only [lo,hi,eq]
    simpa only [xe] using left
  · have gap : 0<high-low := by
      have le : low≤high := le_trans lo hi
      exact sub_pos.mpr (lt_of_le_of_ne le eq)
    have first := mul_nonneg (sub_nonneg.mpr hi) left
    have last := mul_nonneg (sub_nonneg.mpr lo) right
    have correction := mul_nonneg (mul_nonneg kp (sub_nonneg.mpr lo))
      (mul_nonneg (sub_nonneg.mpr hi) gap.le)
    have identity : (high-low)*(a+b*x-k*x^2)=
        (high-x)*(a+b*low-k*low^2)+(x-low)*(a+b*high-k*high^2)+
          k*(x-low)*(high-x)*(high-low) := by ring
    have nonnegative : 0≤(high-low)*(a+b*x-k*x^2) := by
      linarith only [identity,first,last,correction]
    exact nonneg_of_mul_nonneg_right nonnegative gap

private theorem parallel_endpoint {p q c t w : ℝ}
    (on : Normal p q) (bn : Normal c t) (wp : 0≤w) (wh : w≤10/7) :
    0≤p*(1-2*c-3*t)+2*t+p*(1+c*t)-q*t^2-
      p*w*((3/5)*t^2-(1-c)) := by
  have ob := normal_bounds on
  have bb := normal_bounds bn
  have pp : 0≤p := by linarith only [ob.1]
  have od := defect on
  have bd := defect bn
  have upperCorrection :
      p*w*((3/5)*t^2-(1-c))≤p*t^2/7 := by
    have first := mul_nonneg (mul_nonneg pp wp)
      (show 0≤(1/10)*t^2-((3/5)*t^2-(1-c)) by linarith only [bd.1])
    have last := mul_nonneg (mul_nonneg pp (sq_nonneg t))
      (show 0≤1/7-w/10 by linarith only [wh])
    nlinarith only [first,last]
  have cWeight := mul_nonneg (mul_nonneg pp
      (show 0≤2-t by linarith only [bb.2.2.2.1]))
    (show 0≤1-c-t^2/2 by linarith only [bd.1])
  have qWeight := mul_nonneg bn.1
    (show 0≤2*(1-p)-q^2 by linarith only [od.1])
  have pWeight := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr ob.1) (sq_nonneg t))
    (show 0≤6/7-t/2 by linarith only [bb.2.2.2.1])
  have squareWeight := mul_nonneg bn.1 (sq_nonneg (q-t/2))
  have last := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr bb.2.2.2.1)
  have identity : p*(1-2*c-3*t)+2*t+p*(1+c*t)-q*t^2=
      p*(1-c)*(2-t)+t*(2*(1-p)-q*t) := by ring
  nlinarith only [identity,upperCorrection,cWeight,qWeight,pWeight,squareWeight,last]

/-- The scalar after eliminating the actual negative wall's two offsets.
Only the sign of its relative angle with the central square is split. -/
theorem margin {p q d r c t : ℝ}
    (on : Normal p q) (dn : Normal d r) (bn : Normal c t) :
    0≤p*(1-2*c-3*t)+2*t+(p*c-q*t)*r+
      p*(t*r+c*d)+p*max (t*d-c*r) 0 := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have pp : 0≤p := by linarith only [ob.1]
  have cp : 0≤c := by linarith only [bb.1]
  have dd := defect dn
  by_cases order : r≤t
  · have cosine := cosine_order bn dn order
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have last := mul_nonneg cp (sub_nonneg.mpr order)
    have relative : 0≤t*d-c*r := by nlinarith only [first,last]
    rw [max_eq_left relative]
    let a := p*(1-c-2*t)+2*t
    let b := t*(p-q)
    let k := (3/5)*p*(c+t)
    have kp : 0≤k := by
      dsimp [k]
      exact mul_nonneg (mul_nonneg (by norm_num) pp)
        (by linarith only [bb.1,bn.1])
    have atZero : 0≤a+b*0-k*0^2 := by
      have first := mul_nonneg pp (sub_nonneg.mpr bb.2.1)
      have last := mul_nonneg bn.1 (sub_nonneg.mpr ob.2.1)
      dsimp [a]; nlinarith only [first,last]
    have atTop : 0≤a+b*t-k*t^2 := by
      have endpoint := parallel_endpoint on bn
        (show 0≤c+t by linarith only [bb.1,bn.1]) bb.2.2.2.2.2
      have identity : a+b*t-k*t^2=
          p*(1-2*c-3*t)+2*t+p*(1+c*t)-q*t^2-
            p*(c+t)*((3/5)*t^2-(1-c)) := by
        dsimp [a,b,k]
        linear_combination p*bn.2.2
      clear_value a b k
      linarith only [identity,endpoint]
    have inside := quadratic_between a b k 0 t r kp dn.1 order atZero atTop
    have replace := mul_nonneg (mul_nonneg pp
      (show 0≤c+t by linarith only [bb.1,bn.1]))
      (show 0≤d-(1-(3/5)*r^2) by linarith only [dd.2])
    dsimp [a,b,k] at inside
    nlinarith only [inside,replace]
  · have order' : t≤r := le_of_not_ge order
    have cosine := cosine_order dn bn order'
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have last := mul_nonneg cp (sub_nonneg.mpr order')
    have relative : t*d-c*r≤0 := by nlinarith only [first,last]
    rw [max_eq_right relative]
    let a := p*(1-c-3*t)+2*t
    let b := p*(t+c)-q*t
    let k := (3/5)*p*c
    have kp : 0≤k := by
      dsimp [k]
      exact mul_nonneg (mul_nonneg (by norm_num) pp) cp
    have atLow : 0≤a+b*t-k*t^2 := by
      have endpoint := parallel_endpoint on bn cp (by linarith only [bb.2.1])
      have identity : a+b*t-k*t^2=
          p*(1-2*c-3*t)+2*t+p*(1+c*t)-q*t^2-
            p*c*((3/5)*t^2-(1-c)) := by
        dsimp [a,b,k]
        linear_combination p*bn.2.2
      clear_value a b k
      linarith only [identity,endpoint]
    have linearBound : (9/5)*p+(5/7)*q≤2 := by
      nlinarith only [on.2.2,sq_nonneg ((5/7)*p-(9/5)*q),
        sq_nonneg ((9/5)*p+(5/7)*q-2)]
    have tBound : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
    have atHigh : 0≤a+b*(5/7)-k*(5/7)^2 := by
      have first := mul_nonneg bn.1 (sub_nonneg.mpr linearBound)
      have last := mul_nonneg pp
        (show 0≤1-(29/49)*c-(17/35)*t by linarith only [bb.2.1,tBound])
      dsimp [a,b,k]
      nlinarith only [first,last]
    have rBound : r≤5/7 := by linarith only [dn.2.1,db.2.2.2.2.2]
    have inside := quadratic_between a b k t (5/7) r kp order' rBound atLow atHigh
    have replace := mul_nonneg (mul_nonneg pp cp)
      (show 0≤d-(1-(3/5)*r^2) by linarith only [dd.2])
    dsimp [a,b,k] at inside
    nlinarith only [inside,replace]

theorem singleton_upper (O : OpenSquare) (on : Normal O.c O.s)
    (side : 1<O.side) (floor : 0≤O.s*O.loU+O.c*O.loV)
    (cap : O.loV+O.side≤O.c-O.s) : 2<O.loU+O.side := by
  have ob := normal_bounds on
  have cp : 0<O.c := by linarith only [ob.1]
  have capWeight := mul_nonneg cp.le (sub_nonneg.mpr cap)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<O.c+O.s by linarith only [cp,on.1])
  have defectWeight := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (sub_nonneg.mpr on.2.1)
  have identity : O.s*(O.loU+O.side-2)=
      (O.s*O.loU+O.c*O.loV)+O.c*(O.c-O.s-(O.loV+O.side))+
      (O.side-1)*(O.c+O.s)+(1-O.c)*(O.c-O.s) := by ring
  have strict : 0<O.s*(O.loU+O.side-2) := by
    linarith only [identity,floor,capWeight,width,defectWeight]
  have result := pos_of_mul_pos_right strict on.1
  linarith only [result]

theorem own_transverse (O D B : OpenSquare) (r t : ℝ)
    (ds : D.s=-r) (bs : B.s=-t)
    (on : Normal O.c O.s) (dn : Normal D.c r) (bn : Normal B.c t)
    (sameOD : O.side=D.side) (sameDB : D.side=B.side) (side : 1<D.side)
    (oFloor : 0≤O.s*O.loU+O.c*O.loV)
    (oCap : O.loV+O.side≤O.c-O.s) (dBox : InsideContainer D)
    (bCap : B.loV+B.side≤2*B.c+3*t)
    (incoming : O.loU+O.side≤lower D O.c O.s)
    (outgoing : upper D t B.c≤B.loV) : False := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have op : 0<O.c := by linarith only [ob.1]
  have dp : 0<D.c := by linarith only [db.1]
  have bp : 0<B.c := by linarith only [bb.1]
  have above := singleton_upper O on (by simpa only [sameOD] using side) oFloor oCap
  let K := O.c*D.c-O.s*r
  let H := O.c*r+O.s*D.c
  let P := t*D.c-B.c*r
  let Q := t*r+B.c*D.c
  let M := O.c*B.c-O.s*t
  have kp : 0≤K := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr on.2.1)
    have last := mul_nonneg on.1 (sub_nonneg.mpr dn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]; exact add_nonneg (mul_nonneg op.le dn.1) (mul_nonneg on.1 dp.le)
  have qp : 0<Q := by
    dsimp [Q]; exact add_pos_of_nonneg_of_pos (mul_nonneg bn.1 dn.1) (mul_pos bp dp)
  have mp : 0≤M := by
    have first := mul_nonneg bp.le (sub_nonneg.mpr on.2.1)
    have last := mul_nonneg on.1 (sub_nonneg.mpr bn.2.1)
    dsimp [M]; nlinarith only [first,last]
  have lowerForm : lower D O.c O.s=K*D.loU+H*D.loV :=
    lower_negative_pos D r _ _ ds kp hp
  have upperForm : upper D t B.c=P*D.loU+Q*D.loV+D.side*(Q+max P 0) := by
    rw [upper_in_bands,ds]
    have u : t*D.c+B.c*(-r)=P := by dsimp [P]; ring
    have v : -t*(-r)+B.c*D.c=Q := by dsimp [Q]; ring
    rw [u,v,abs_of_nonneg qp.le]
    by_cases sign : 0≤P
    · rw [abs_of_nonneg sign,max_eq_left sign]; ring
    · have negative : P≤0 := le_of_not_ge sign
      rw [abs_of_nonpos negative,max_eq_right negative]; ring
  have dBottom := ThreeSquare.bottom_wall D dp.le dBox
  rw [ds,abs_neg,abs_of_nonneg dn.1] at dBottom
  dsimp [centerY] at dBottom
  rw [ds] at dBottom
  have floor : 0≤D.c*D.loV-r*(D.loU+D.side) := by nlinarith only [dBottom]
  let Z := M*r+O.c*(Q+max P 0)
  have zp : 0<Z+O.c := by
    have first := mul_nonneg mp dn.1
    have last := mul_nonneg op.le (le_max_right P 0)
    dsimp [Z]
    nlinarith only [first,last,op,mul_pos op qp]
  have width := mul_pos (sub_pos.mpr side) zp
  have first := mul_nonneg bn.1
    (show 0≤lower D O.c O.s-2 by linarith only [above,incoming])
  have middle := mul_nonneg mp floor
  have last := mul_nonneg op.le (sub_nonneg.mpr bCap)
  have scalar := margin on dn bn
  have identity : O.c*(upper D t B.c-B.loV)=
      t*(lower D O.c O.s-2)+M*(D.c*D.loV-r*(D.loU+D.side))+
      O.c*(2*B.c+3*t-(B.loV+B.side))+(D.side-1)*(Z+O.c)+
      (O.c*(1-2*B.c-3*t)+2*t+Z) := by
    rw [upperForm,lowerForm,←sameDB]
    dsimp [K,H,P,Q,M,Z]
    ring
  have strict : 0<O.c*(upper D t B.c-B.loV) := by
    dsimp [Z,M,Q,P] at identity width middle
    nlinarith only [identity,width,first,middle,last,scalar]
  have notSeparated := mul_nonpos_of_nonneg_of_nonpos op.le (sub_nonpos.mpr outgoing)
  linarith only [strict,notSeparated]

end N12Compact.PositiveBottomNegativeWallCycle
