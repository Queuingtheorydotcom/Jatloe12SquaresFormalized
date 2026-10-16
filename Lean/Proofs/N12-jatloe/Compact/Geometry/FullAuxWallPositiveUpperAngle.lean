import Compact.Geometry.C977CornerCubic

/-! Uniform upper-angle obstruction for the two genuine positive C/B
support modes. The proof uses rational arc bounds and two quadratic
identities, rather than an angle grid. -/
namespace N12Compact.FullAuxWallPositiveUpperAngle

open C977CornerCubic
set_option Elab.async false

private theorem outer_bounds {b t : ℝ} (bn : Normal b t)
    (steep : 23/50≤t) : b≤89/100 ∧ 67/50≤b+t ∧ t≤5/7 := by
  have bb := normal_bounds bn
  have cap : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
  have square := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤t+23/50 by linarith only [bn.1])
  have bc : b≤89/100 := by
    nlinarith only [square,bn.2.2,sq_nonneg (b-89/100)]
  have sum : 67/50≤b+t := by
    apply le_of_not_gt
    intro small
    have first := mul_nonneg
      (show 0≤b-23/50 by linarith only [steep,bn.2.1])
      (sub_nonneg.mpr steep)
    have second := mul_nonneg (sub_nonneg.mpr small.le)
      (show 0≤b+t+21/50 by linarith only [bb.2.2.2.2.1])
    nlinarith only [first,second,bn.2.2]
  exact ⟨bc,sum,cap⟩

theorem c_axis {C S b t : ℝ} (dn : Normal C S) (bn : Normal b t)
    (small : S≤11/50) (steep : 23/50≤t) :
    C*(2-b-t+(3/5)*b*t)+S*(b-t+(3/5)*t^2)≤1 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have ob := outer_bounds bn steep
  have cp : 0≤C := le_trans dn.1 dn.2.1
  have first := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (show 0≤1-(3/10)*(b+t+67/50) by
      linarith only [bb.2.2.2.2.2])
  have acap : 2-b-t+(3/5)*b*t≤22467/25000 := by
    nlinarith only [first,bn.2.2]
  have monotone := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤1-(3/5)*(t+23/50) by linarith only [ob.2.2])
  have bcap : b-t+(3/5)*t^2≤3481/6250 := by
    nlinarith only [monotone,ob.1]
  have wa := mul_nonneg cp (sub_nonneg.mpr acap)
  have wb := mul_nonneg dn.1 (sub_nonneg.mpr bcap)
  have defect : C≤1-S^2/2 := by
    nlinarith only [dn.2.2,sq_nonneg (C-1)]
  have chord := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤(3481/6250 : ℝ)-(22467/50000)*(S+11/50) by
      linarith only [small])
  nlinarith only [wa,wb,defect,chord]

theorem b_axis {C S b t u : ℝ} (dn : Normal C S) (bn : Normal b t)
    (small : S≤11/50) (steep : 23/50≤t)
    (offset : u≤1/1000) (ordered : S*b≤C*t) :
    0≤1+b*(C-S+S^2+(2/5)*C*S-2)+
      t*(C+S+(2/5)*S^2-C*S-1)-(C*t-S*b)*u := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have ob := outer_bounds bn steep
  have cp : 0≤C := le_trans dn.1 dn.2.1
  have bp : 0≤b := le_trans bn.1 bn.2.1
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤11/50+S by linarith only [dn.1])
  have cosine : 97/100≤C := by
    apply le_of_not_gt
    intro smallCosine
    have comparison := mul_nonneg (sub_nonneg.mpr smallCosine.le)
      (show 0≤97/100+C by linarith only [db.1])
    nlinarith only [square,dn.2.2,comparison]
  have product := mul_nonneg (sub_nonneg.mpr db.2.1)
    (show 0≤(51/100)*C-49/100 by linarith only [cosine])
  have defect : 1-C≤(51/100)*S^2 := by
    nlinarith only [product,dn.2.2]
  let P := C-S+S^2+(2/5)*C*S-2
  let Q := C+S+(2/5)*S^2-C*S-1
  let beta := C*t-S*b
  have wp := mul_nonneg (sub_nonneg.mpr defect)
    (show 0≤1+(2/5)*S by linarith only [dn.1])
  have coefficient := mul_nonneg (sq_nonneg S)
    (show 0≤49/100-(51/250)*S-89/200 by linarith only [small])
  have pLower : -1-(3/5)*S+(89/200)*S^2≤P := by
    dsimp [P]; nlinarith only [wp,coefficient]
  have wq := mul_nonneg (sub_nonneg.mpr defect)
    (show 0≤1-S by linarith only [small])
  have cubic := mul_nonneg dn.1 (sq_nonneg S)
  have qLower : -(11/100)*S^2≤Q := by
    dsimp [Q]; nlinarith only [wq,cubic]
  have weightP := mul_nonneg bp (sub_nonneg.mpr pLower)
  have weightQ := mul_nonneg bn.1 (sub_nonneg.mpr qLower)
  have lowerCoefficient : (23/100 : ℝ)≤(89/200)*b-(11/100)*t := by
    linarith only [bb.1,ob.2.2]
  have weightSquare := mul_nonneg (sq_nonneg S) (sub_nonneg.mpr lowerCoefficient)
  have upperCosine := mul_nonneg (sub_nonneg.mpr ob.1)
    (show 0≤1+(3/5)*S by linarith only [dn.1])
  have betap : 0≤beta := by dsimp [beta]; linarith only [ordered]
  have betaCap : beta≤t := by
    have first := mul_nonneg bn.1 (sub_nonneg.mpr db.2.1)
    have second := mul_nonneg dn.1 bp
    dsimp [beta]; nlinarith only [first,second]
  have weightedOffset := mul_nonneg betap (sub_nonneg.mpr offset)
  have chord := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤(267/500 : ℝ)-(23/100)*(S+11/50) by
      linarith only [small])
  change 0≤1+b*P+t*Q-beta*u
  clear_value P Q beta
  nlinarith only [weightP,weightQ,weightSquare,upperCosine,betaCap,
    weightedOffset,chord,ob.2.2]

#print axioms c_axis
#print axioms b_axis
end N12Compact.FullAuxWallPositiveUpperAngle
