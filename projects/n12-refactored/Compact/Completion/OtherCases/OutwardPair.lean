import Compact.Completion.OtherCases.OutwardPairFaces
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! Complete coupled-support theorem for the actual outward southeast
square and inward northeast square. Both physical northeast orientations
and every forward/reverse face normal are included. -/
namespace N12Compact.Completion.OtherCases.OutwardPair
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C1092WallProfileScalars
set_option Elab.async false

theorem impossible (A N : OpenSquare) (t : ℝ)
    (side : 1<A.side) (sameSide : A.side=N.side)
    (signed : A.s = -t) (cp : 0<A.c) (tn : 0≤t) (order : t≤A.c)
    (halfLow : 13/87<half A.c t) (halfHigh : half A.c t<143/500)
    (southUpperU : A.loU+A.side≤A.c+t)
    (southLowerV : -A.c+(4/5)*t≤A.loV)
    (southMarker : A.Inside (7/20) (-7/20))
    (southY : A.Inside (21/40) (1/8))
    (northMarker : N.Inside (7/20) (7/20))
    (northF : N.Inside 0 (13/50)) (northG : N.Inside (13/50) 1)
    (missingL : ¬N.Inside (-7/20) (7/20))
    (missingP0 : ¬N.Inside 0 1) (missingP1 : ¬N.Inside 1 1)
    (apart : ∀ x y,¬(A.Inside x y ∧ N.Inside x y)) : False := by
  have unit : A.c^2+t^2=1 := by simpa only [signed,neg_sq] using A.unit_normal
  have northSide : 1<N.side := by simpa only [←sameSide] using side
  have missingY : ¬N.Inside (21/40) (1/8) := fun h => apart _ _ ⟨southY,h⟩
  obtain ⟨n,np,nn,norder,nshape,ninside,nLowerU,nUpperV⟩ :=
    OutwardPairFaces.frame N northSide northMarker northF northG missingL missingP0 missingP1 missingY
  have same : A.side=n.side := sameSide.trans nshape.symm
  have nV : n.loV+A.side≤n.c := by simpa only [same] using nUpperV
  have nMarker := (ninside _ _).mpr northMarker
  have nF := (ninside _ _).mpr northF
  have nApart : ∀ x y,¬(A.Inside x y ∧ n.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(ninside x y).mp h.2⟩
  have tp : 0<t := by
    by_contra failed
    have zero : t=0 := le_antisymm (le_of_not_gt failed) tn
    simp only [zero,half,zero_div] at halfLow
    norm_num at halfLow
  have upperCross := SharpPointScalars.half_before A.c t (229551/270449) (143000/270449)
    (143/500) cp tn unit (by norm_num) (by norm_num) (by norm_num) halfHigh.le
  have strictOrder : t<A.c := by linarith only [upperCross,cp]
  have lowerCross := SharpPointScalars.half_after A.c t (3700/3869) (1131/3869)
    (13/87) cp tn unit (by norm_num) (by norm_num) (by norm_num) halfLow.le
  have slope : 1131*A.c≤3700*t := by linarith only [lowerCross]
  let d := A.c*n.c-t*n.s
  let k := A.c*n.s+t*n.c
  have dp : 0<d := by
    have first := mul_pos np (sub_pos.mpr strictOrder)
    have last := mul_nonneg tn (sub_nonneg.mpr norder)
    dsimp only [d]
    nlinarith only [first,last]
  have kp : 0<k := by
    have first := mul_nonneg cp.le nn
    have last := mul_pos tp np
    dsimp only [k]
    nlinarith only [first,last]
  have coefficient : 0<1+k+d := by linarith only [dp,kp]
  have cutoff : half A.c t<3/10 := by linarith only [halfHigh]
  have firstSupport : upper A (-n.s) n.c = -k*A.loU+d*(A.loV+A.side) := by
    have alpha : (-n.s)*A.c+n.c*A.s = -k := by rw [signed]; dsimp only [k]; ring
    have beta : -(-n.s)*A.s+n.c*A.c = d := by rw [signed]; dsimp only [d]; ring
    rw [WallProfile.upper_in_bands,alpha,beta,
      abs_of_nonpos (by linarith only [kp]),abs_of_nonneg dp.le]
    ring
  have secondSupport : upper n A.c A.s = d*(n.loU+n.side)-k*n.loV := by
    have alpha : A.c*n.c+A.s*n.s=d := by rw [signed]; dsimp only [d]; ring
    have beta : -A.c*n.s+A.s*n.c = -k := by rw [signed]; dsimp only [k]; ring
    rw [WallProfile.upper_in_bands,alpha,beta,
      abs_of_nonneg dp.le,abs_of_nonpos (by linarith only [kp])]
    ring
  have rejectFirst : ¬ upper A (-n.s) n.c ≤ lower n (-n.s) n.c := by
    intro separator
    rw [(ownV n).1,firstSupport] at separator
    have uWeight := mul_nonneg kp.le (sub_nonneg.mpr southUpperU)
    have vWeight := mul_nonneg dp.le (sub_nonneg.mpr southLowerV)
    have necessary : A.side*(1+k+d)≤k*(A.c+t)+d*(A.c-(4/5)*t)+n.c := by
      nlinarith only [separator,uWeight,vWeight,nV]
    have margin : 0<1+k+d-k*(A.c+t)-d*(A.c-(4/5)*t)-n.c := by
      simpa only [d,k] using OutwardPairScalars.first_margin A.c t n.c n.s
        cp tp unit n.unit_normal cutoff
    have strict := mul_pos (sub_pos.mpr side) coefficient
    nlinarith only [necessary,margin,strict]
  have rejectSecond : ¬ upper n A.c A.s ≤ lower A A.c A.s := by
    intro separator
    rw [(ownU A).1,secondSupport,←same] at separator
    have uWeight := mul_nonneg dp.le (sub_nonneg.mpr nLowerU)
    have vWeight := mul_nonneg kp.le (sub_nonneg.mpr nV)
    have necessary : A.side*(1+d+k)+(7/20)*d*(n.s-n.c)-k*n.c-A.c-t≤0 := by
      nlinarith only [separator,uWeight,vWeight,southUpperU]
    have margin : 0<1+d+k+(7/20)*d*(n.s-n.c)-k*n.c-A.c-t := by
      simpa only [d,k] using OutwardPairScalars.second_margin A.c t n.c n.s
        cp tn order unit np nn norder n.unit_normal cutoff
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<1+d+k by linarith only [dp,kp])
    nlinarith only [necessary,margin,strict]
  have cone (nx ny : ℝ) (normal : nx^2+ny^2=1)
      (separator : upper A nx ny≤lower n nx ny) :
      0<ny ∧ 0< -(21/40)*nx+(27/200)*ny := by
    have sm := strict_bounds A _ _ nx ny normal southMarker
    have nm := strict_bounds n _ _ nx ny normal nMarker
    have sy := strict_bounds A _ _ nx ny normal southY
    have nf := strict_bounds n _ _ nx ny normal nF
    constructor <;> nlinarith only [sm.2,nm.1,sy.2,nf.1,separator]
  have reverse (nx ny : ℝ)
      (separator : upper n nx ny≤lower A nx ny) :
      upper A (-nx) (-ny)≤lower n (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [separator]
  have axes := CongruentSAT.faceSeparation_of_disjoint A n same nApart
  change pairRadius A n≤|A.c*(centerX n-centerX A)+A.s*(centerY n-centerY A)| ∨
    pairRadius A n≤|-A.s*(centerX n-centerX A)+A.c*(centerY n-centerY A)| ∨
    pairRadius n A≤|n.c*(centerX n-centerX A)+n.s*(centerY n-centerY A)| ∨
    pairRadius n A≤|-n.s*(centerX n-centerX A)+n.c*(centerY n-centerY A)| at axes
  have separateAxis (nx ny R : ℝ)
      (radius : supportRadius A nx ny+supportRadius n nx ny=R)
      (axis : R≤|nx*(centerX n-centerX A)+ny*(centerY n-centerY A)|) :=
    separated A n nx ny (by rwa [radius])
  rcases axes with au | av | nu | nv
  · rcases separateAxis _ _ _ (parallel_radius A n) au with forward | backward
    · have con := (cone A.c A.s A.unit_normal forward).1
      rw [signed] at con
      linarith only [con,tn]
    · exact rejectSecond backward
  · rcases separateAxis _ _ _ (transverse_radius A n) av with forward | backward
    · have con := (cone (-A.s) A.c (by nlinarith only [A.unit_normal]) forward).2
      rw [signed] at con
      linarith only [con,slope,cp]
    · have con := (cone (-(-A.s)) (-A.c) (by nlinarith only [A.unit_normal])
        (reverse _ _ backward)).1
      linarith only [con,cp]
  · have radius : supportRadius A n.c n.s+supportRadius n n.c n.s=pairRadius n A := by
      rw [add_comm]
      exact parallel_radius n A
    rcases separateAxis _ _ _ radius nu with forward | backward
    · have con := (cone n.c n.s n.unit_normal forward).2
      linarith only [con,norder,np]
    · have con := (cone (-n.c) (-n.s) (by nlinarith only [n.unit_normal])
        (reverse _ _ backward)).1
      linarith only [con,nn]
  · have radius : supportRadius A (-n.s) n.c+supportRadius n (-n.s) n.c=pairRadius n A := by
      rw [add_comm]
      exact transverse_radius n A
    rcases separateAxis _ _ _ radius nv with forward | backward
    · exact rejectFirst forward
    · have con := (cone (-(-n.s)) (-n.c) (by nlinarith only [n.unit_normal])
        (reverse _ _ backward)).1
      linarith only [con,np]

#print axioms impossible
end N12Compact.Completion.OtherCases.OutwardPair

