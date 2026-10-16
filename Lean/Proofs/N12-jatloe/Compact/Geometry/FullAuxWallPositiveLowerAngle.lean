import Compact.Geometry.C977CornerSectorBounds

/-! The two genuine transverse central-square separators both exclude
a very small opposite angle. These are exact continuous scalar bounds;
the actual support selectors are bound separately. -/
namespace N12Compact.FullAuxWallPositiveLowerAngle
open C977CornerCubic
set_option Elab.async false

theorem c_axis {C S b t : ℝ} (dn : Normal C S) (bn : Normal b t)
    (small : S≤1/20) (steep : 3/10<t) :
    C*(2-b-t+(3/5)*b*t)+S*(b-t+(3/5)*t^2)≤1 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have bp : 0≤b := by linarith only [bb.1]
  have arcProduct := mul_nonneg
    (show 0≤b+t-1 by linarith only [bb.2.2.2.2.1])
    (show 0≤3/2-(b+t) by linarith only [bb.2.2.2.2.2])
  have arc : (4/5)*b*t≤b+t-1 := by
    nlinarith only [arcProduct,bn.2.2]
  have first := mul_nonneg bn.1 (sub_nonneg.mpr bb.1)
  have product : 21/100<b*t := by nlinarith only [first,steep]
  have tBound : t≤5/7 := by linarith only [bn.2.1,bb.2.2.2.2.2]
  have square := mul_nonneg bn.1 (sub_nonneg.mpr tBound)
  let P := 2-b-t+(3/5)*b*t
  let Q := b-t+(3/5)*t^2
  have pp : 0≤P := by
    have cross := mul_nonneg bp bn.1
    dsimp [P]
    nlinarith only [bb.2.2.2.2.2,cross]
  have pCap : P<479/500 := by dsimp [P]; nlinarith only [arc,product]
  have qCap : Q≤29/35 := by
    dsimp [Q]
    nlinarith only [square,bb.2.1,steep]
  have pWeight := mul_nonneg (sub_nonneg.mpr db.2.1) pp
  have qWeight := mul_nonneg dn.1 (sub_nonneg.mpr qCap)
  change C*P+S*Q≤1
  clear_value P Q
  nlinarith only [pWeight,qWeight,pCap,small]

theorem b_axis {C S b t u : ℝ} (dn : Normal C S) (bn : Normal b t)
    (small : S≤1/20) (steep : 3/10<t) (offset : u≤1/112)
    (ordered : 0≤C*t-S*b) :
    0≤1+b*(C-S+S^2+(2/5)*C*S-2)+
      t*(C+S+(2/5)*S^2-C*S-1)-(C*t-S*b)*u := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have cp : 0≤C := by linarith only [db.1]
  have bp : 0≤b := by linarith only [bb.1]
  have defect : 1-C≤S^2 := by
    have product := mul_nonneg cp (sub_nonneg.mpr db.2.1)
    nlinarith only [product,dn.2.2]
  let G := C-S+S^2+(2/5)*C*S-2
  let H := C+S+(2/5)*S^2-C*S-1
  have gLower : -1-(18/25)*S≤G := by
    have product := mul_nonneg dn.1 (sub_nonneg.mpr db.1)
    dsimp [G]
    nlinarith only [product,defect]
  have hLower : -(3/5)*S^2≤H := by
    have product := mul_nonneg dn.1 (sub_nonneg.mpr db.2.1)
    dsimp [H]
    nlinarith only [product,defect]
  have gWeight := mul_nonneg bp (sub_nonneg.mpr gLower)
  have bReplace := mul_nonneg dn.1 (sub_nonneg.mpr bb.2.1)
  have hWeight := mul_nonneg bn.1 (sub_nonneg.mpr hLower)
  have sSquare := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/20+S by linarith only [dn.1])
  have tWeight := mul_nonneg bn.1
    (show 0≤1/400-S^2 by nlinarith only [sSquare])
  let beta := C*t-S*b
  have betaCap : beta≤t := by
    have first := mul_nonneg bn.1 (sub_nonneg.mpr db.2.1)
    have second := mul_nonneg dn.1 bp
    dsimp [beta]
    nlinarith only [first,second]
  have offsetWeight := mul_nonneg ordered
    (show 0≤1/100-u by linarith only [offset])
  have defectB : t^2/2≤1-b := by
    nlinarith only [bn.2.2,sq_nonneg (1-b)]
  have tSquare := mul_nonneg bn.1
    (show 0≤t-3/10 by linarith only [steep])
  change 0≤1+b*G+t*H-beta*u
  change 0≤beta*(1/100-u) at offsetWeight
  clear_value G H beta
  nlinarith only [gWeight,bReplace,hWeight,tWeight,betaCap,offsetWeight,
    defectB,tSquare,steep,small,bn.1]

#print axioms c_axis
#print axioms b_axis
end N12Compact.FullAuxWallPositiveLowerAngle
