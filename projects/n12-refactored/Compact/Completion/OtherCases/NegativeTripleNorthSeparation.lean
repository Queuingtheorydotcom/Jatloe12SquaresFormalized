import Compact.Completion.OtherCases.RightTripleData
import Compact.Completion.OtherCases.SupportBands

/-! The full northeast/right separating-axis reduction. The two actual
strict point pairs force a cone; its remaining right transverse direction
fails against the complete northeast support, in either northeast sign. -/
namespace N12Compact.Completion.OtherCases.NegativeTripleNorthSeparation
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false

private theorem upper_pp (q : OpenSquare) (nx ny : ℝ)
    (u : 0≤nx*q.c+ny*q.s) (v : 0≤ -nx*q.s+ny*q.c) :
    upper q nx ny=(nx*q.c+ny*q.s)*(q.loU+q.side)+
      (-nx*q.s+ny*q.c)*(q.loV+q.side) := by
  rw [C981CompletionSupportForms.upper_in_bands,abs_of_nonneg u,abs_of_nonneg v]
  ring

theorem cone (N R : OpenSquare) (sharp : N.Inside (21/40) (1/8))
    (top : N.Inside (1/2) 1) (right : RightTripleData.RightProfile R)
    (nx ny : ℝ) (unit : nx^2+ny^2=1) (sep : upper N nx ny≤lower R nx ny) :
    0<nx ∧ ny<(1/2)*nx ∧ 0<(19/40)*nx+(87/200)*ny := by
  have first := (strict_bounds N _ _ nx ny unit top).2
  have last := (strict_bounds R _ _ nx ny unit right.origin).1
  have otherFirst := (strict_bounds N _ _ nx ny unit sharp).2
  have otherLast := (strict_bounds R _ _ nx ny unit right.upperPoint).1
  constructor
  · linarith only [first,last,otherFirst,otherLast,sep]
  constructor <;> linarith only [first,last,otherFirst,otherLast,sep]

private theorem no_right_v (N R : OpenSquare) (side : 1<N.side)
    (north : TopOnlyQuadrantProfile.Data N) (right : RightTripleData.RightProfile R)
    (sharp : N.Inside (21/40) (1/8)) (top : N.Inside (1/2) 1)
    (sep : upper N (-R.s) R.c≤lower R (-R.s) R.c) : False := by
  let r := -N.s
  let t := -R.s
  have rp : 0<r := by dsimp only [r]; linarith only [north.sine_neg]
  have tn : 0≤t := by dsimp only [t]; linarith only [right.sineNonpositive]
  have unit : (-R.s)^2+R.c^2=1 := by nlinarith only [R.unit_normal]
  have normal := cone N R sharp top right (-R.s) R.c unit sep
  have tp : 0<t := normal.1
  have slope : R.c<(1/2)*t := normal.2.1
  have data := TopOnlyQuadrantScalars.profile_bounds N side north
  have dLarge := data.2.2.1
  have rSmall := data.2.2.2.1
  have alphaPositive : 0<N.c*t-r*R.c := by
    have first := mul_pos tp
      (show 0<N.c-(1/2)*r by dsimp only [r]; linarith only [dLarge,rSmall])
    have last := mul_nonneg rp.le (sub_nonneg.mpr slope.le)
    nlinarith only [first,last]
  have deltaPositive : 0<r*t+N.c*R.c := by
    have first := mul_pos rp tp
    have last := mul_pos north.cosine_pos right.cosinePositive
    nlinarith only [first,last]
  have formula := upper_pp N (-R.s) R.c
    (by dsimp only [r,t] at alphaPositive; nlinarith only [alphaPositive])
    (by dsimp only [r,t] at deltaPositive; nlinarith only [deltaPositive])
  have highU : 1-r<N.loU+N.side := by
    dsimp only [r]
    linarith only [north.lowerU,side]
  have highV : 1+(13/50)*N.c<N.loV+N.side := by
    linarith only [north.lowerV,side]
  have first := mul_pos alphaPositive (sub_pos.mpr highU)
  have last := mul_pos deltaPositive (sub_pos.mpr highV)
  have identity : (N.c*t-r*R.c)*(1-r)+(r*t+N.c*R.c)*(1+(13/50)*N.c)=
      t*(N.c+r-(37/50)*N.c*r)+R.c*(N.c-r+13/50+(37/50)*r^2) := by
    dsimp only [r]
    linear_combination (13/50)*R.c*N.unit_normal
  have support : t*(N.c+r-(37/50)*N.c*r)+
      R.c*(N.c-r+13/50+(37/50)*r^2)<upper N (-R.s) R.c := by
    rw [formula]
    dsimp only [r,t] at first last identity ⊢
    nlinarith only [first,last,identity]
  have aMargin := mul_pos tp
    (show 0<N.c+r-(37/50)*N.c*r-1 by
      dsimp only [r]
      nlinarith only [data.2.2.2.2.2.2.1])
  have bMargin := mul_pos right.cosinePositive
    (show 0<N.c-r+13/50+(37/50)*r^2 by
      dsimp only [r]
      nlinarith only [data.2.2.2.2.2.2.2])
  have origin := (strict_bounds R 1 0 (-R.s) R.c unit right.origin).1
  dsimp only [t] at support aMargin
  nlinarith only [support,aMargin,bMargin,origin,sep]

theorem separators (N R : OpenSquare) (side : 1<N.side) (same : N.side=R.side)
    (north : TopOnlyQuadrantProfile.Data N) (right : RightTripleData.RightProfile R)
    (sharp : N.Inside (21/40) (1/8)) (top : N.Inside (1/2) 1)
    (apart : ∀ x y,¬(N.Inside x y ∧ R.Inside x y)) :
    upper N N.c N.s≤lower R N.c N.s ∨
      upper N R.c R.s≤lower R R.c R.s := by
  have data := TopOnlyQuadrantScalars.profile_bounds N side north
  have reverse (nx ny : ℝ) (sep : upper R nx ny≤lower N nx ny) :
      upper N (-nx) (-ny)≤lower R (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have reverseU (q : OpenSquare) (cp : 0<q.c)
      (sep : upper R q.c q.s≤lower N q.c q.s) : False := by
    have normal := cone N R sharp top right (-q.c) (-q.s)
      (by simpa only [neg_sq] using q.unit_normal) (reverse _ _ sep)
    linarith only [normal.1,cp]
  have noNV (sep : upper N (-N.s) N.c≤lower R (-N.s) N.c ∨
      upper R (-N.s) N.c≤lower N (-N.s) N.c) : False := by
    have unit : (-N.s)^2+N.c^2=1 := by nlinarith only [N.unit_normal]
    rcases sep with forward | backward
    · have normal := cone N R sharp top right (-N.s) N.c unit forward
      linarith only [normal.2.1,data.2.2.1,data.2.2.2.1]
    · have opposite : upper N N.s (-N.c)≤lower R N.s (-N.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      have normal := cone N R sharp top right N.s (-N.c)
        (by nlinarith only [N.unit_normal]) opposite
      linarith only [normal.1,north.sine_neg]
  have noRV (sep : upper N (-R.s) R.c≤lower R (-R.s) R.c ∨
      upper R (-R.s) R.c≤lower N (-R.s) R.c) : False := by
    rcases sep with forward | backward
    · exact no_right_v N R side north right sharp top forward
    · have opposite : upper N R.s (-R.c)≤lower R R.s (-R.c) := by
        simpa only [neg_neg] using reverse _ _ backward
      have normal := cone N R sharp top right R.s (-R.c)
        (by nlinarith only [R.unit_normal]) opposite
      linarith only [normal.1,right.sineNonpositive]
  have axes := CongruentSAT.faceSeparation_of_disjoint N R same apart
  change pairRadius N R≤|N.c*(centerX R-centerX N)+N.s*(centerY R-centerY N)| ∨
    pairRadius N R≤|-N.s*(centerX R-centerX N)+N.c*(centerY R-centerY N)| ∨
    pairRadius R N≤|R.c*(centerX R-centerX N)+R.s*(centerY R-centerY N)| ∨
    pairRadius R N≤|-R.s*(centerX R-centerX N)+R.c*(centerY R-centerY N)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius N nx ny+supportRadius R nx ny=radius)
      (axis : radius≤|nx*(centerX R-centerX N)+ny*(centerY R-centerY N)|) :=
    separated N R nx ny (by rwa [eq])
  rcases axes with nu | nv | ru | rv
  · rcases separate _ _ _ (parallel_radius N R) nu with forward | backward
    · exact Or.inl forward
    · exact False.elim (reverseU N north.cosine_pos backward)
  · exact False.elim (noNV (separate _ _ _ (transverse_radius N R) nv))
  · have radius : supportRadius N R.c R.s+supportRadius R R.c R.s=pairRadius R N := by
      rw [add_comm]
      exact parallel_radius R N
    rcases separate _ _ _ radius ru with forward | backward
    · exact Or.inr forward
    · exact False.elim (reverseU R right.cosinePositive backward)
  · have radius : supportRadius N (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R N := by
      rw [add_comm]
      exact transverse_radius R N
    exact False.elim (noRV (separate _ _ _ radius rv))

theorem right_axis_bounds (N R : OpenSquare)
    (right : RightTripleData.RightProfile R)
    (sharp : N.Inside (21/40) (1/8)) (top : N.Inside (1/2) 1)
    (sep : upper N R.c R.s≤lower R R.c R.s) :
    87*(-R.s)<95*R.c ∧ 2/3<R.c ∧ -R.s<3/4 := by
  have normal := cone N R sharp top right R.c R.s R.unit_normal sep
  have slope : 87*(-R.s)<95*R.c := by linarith only [normal.2.2]
  have product := mul_nonneg (show 0≤95*R.c-87*(-R.s) by linarith only [slope])
    (show 0≤95*R.c+87*(-R.s) by linarith only [right.cosinePositive,right.sineNonpositive])
  have cLarge : 2/3<R.c := by
    by_contra bad
    have low : R.c≤2/3 := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr low)
      (show 0≤2/3+R.c by linarith only [right.cosinePositive])
    nlinarith only [product,R.unit_normal,square]
  have tSmall : -R.s<3/4 := by
    by_contra bad
    have large : 3/4≤ -R.s := le_of_not_gt bad
    have square := mul_nonneg (show 0≤ -R.s-3/4 by linarith only [large])
      (show 0≤ -R.s+3/4 by linarith only [right.sineNonpositive])
    nlinarith only [product,R.unit_normal,square]
  exact ⟨slope,cLarge,tSmall⟩

#print axioms separators
#print axioms right_axis_bounds
end N12Compact.Completion.OtherCases.NegativeTripleNorthSeparation
