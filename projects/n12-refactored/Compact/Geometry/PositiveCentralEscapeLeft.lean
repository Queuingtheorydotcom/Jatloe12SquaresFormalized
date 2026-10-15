import Compact.Geometry.PositiveCentralEscapeOrder
import Compact.Geometry.CornerSingletonPair

/-! Genuine left-singleton restrictions in the missing-west-point sector.
The O/A/W-only angle-order statement cannot use the true marker cap as a
replacement for the unavailable 2.88 point. These reductions retain the
actual left square instead. No complete angle-order claim is made here. -/
namespace N12Compact.PositiveCentralEscapeLeft
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds PositiveCentralEscapeOrder
set_option Elab.async false

/-- The original northwest-marker cap and surviving O/A support force
the bottom square into a shallow sector, uniformly in the central angle. -/
theorem bottom_cosine {p q C S v : ℝ}
    (on : Normal p q) (an : Normal C S) (order : q≤S)
    (support : B p q < (p*S-q*C)*(2*(C+S)-1)+(p*C+q*S)*(v-1))
    (northwest : v≤(47/20)*C-(33/20)*S) : 9/10<p := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0<C := by linarith only [ab.1]
  have floor := strong_base_bound on an order support
  have cap := mul_nonneg cp.le (sub_nonneg.mpr northwest)
  have gap : C*(1-p)<1+(7/20)*C*(C+S)-(C+S) := by
    nlinarith only [floor,cap,an.2.2]
  by_contra no
  have pmax : p≤9/10 := le_of_not_gt no
  have cosine := cosine_order an on order
  have cmax : C≤9/10 := le_trans cosine pmax
  have csquare := mul_nonneg (sub_nonneg.mpr cmax)
    (show 0≤9/10+C by linarith only [cp])
  have sine : 13/30≤S := by
    by_contra noS
    have square := mul_nonneg
      (show 0≤13/30-S by linarith only [noS])
      (show 0≤13/30+S by linarith only [an.1])
    nlinarith only [square,csquare,an.2.2]
  have difference := mul_nonneg
    (show 0≤7/15-(C-S) by linarith only [cmax,sine])
    (show 0≤7/15+(C-S) by linarith only [an.2.1])
  have sum : 4/3≤C+S := by
    by_contra noSum
    have square := mul_nonneg
      (show 0≤4/3-(C+S) by linarith only [noSum])
      (show 0≤4/3+C+S by linarith only [cp,an.1])
    nlinarith only [difference,square,an.2.2]
  have lower := mul_nonneg cp.le (sub_nonneg.mpr pmax)
  have upper := mul_nonneg (sub_nonneg.mpr sum)
    (show 0≤1-(7/20)*C by linarith only [ab.2.1])
  nlinarith only [gap,lower,upper,cmax]

private theorem corner_margin {p q : ℝ} (on : Normal p q) (shallow : 9/10≤p) :
    0≤(1-p)^2+q*(p-457/500) := by
  have ob := normal_bounds on
  by_cases large : 457/500≤p
  · have product := mul_nonneg on.1 (sub_nonneg.mpr large)
    nlinarith only [sq_nonneg (1-p),product]
  · have square := mul_nonneg (sub_nonneg.mpr shallow)
      (show 0≤p+9/10 by linarith only [ob.1])
    have sine : q≤11/25 := by
      by_contra no
      have product := mul_pos
        (show 0<q-11/25 by linarith only [no])
        (show 0<q+11/25 by linarith only [on.1])
      nlinarith only [product,square,on.2.2]
    have replace := mul_nonneg (sub_nonneg.mpr sine)
      (show 0≤457/500-p by linarith only [large])
    have factor := mul_nonneg (sub_nonneg.mpr shallow)
      (show 0≤p-33/50 by linarith only [shallow])
    have identity : (1-p)^2+(11/25)*(p-457/500)=
        12/3125+(p-9/10)*(p-33/50) := by ring
    nlinarith only [replace,factor,identity]

/-- The left square's negative U axis cannot separate the two original
corner singletons in this shallow positive-bottom sector. The strict
corner in L and the full bottom-wall support of O are essential. -/
theorem negative_left_axis_impossible (O L : OpenSquare) (r : ℝ)
    (on : Normal O.c O.s) (ln : Normal L.c r) (ls : L.s=-r)
    (shallow : 9/10≤O.c) (side : 1<O.side)
    (box : InsideContainer O)
    (cap : O.loU+O.side≤2*O.c+(457/500)*O.s)
    (corner : L.Inside 1 1) :
    ¬upper L L.c L.s≤lower O L.c L.s := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have op : 0<O.c := by linarith only [ob.1]
  have lp : 0<L.c := by linarith only [lb.1]
  let J := O.c*L.c-O.s*r
  let H := O.s*L.c+O.c*r
  have jp : 0≤J := by
    have first := mul_nonneg op.le (sub_nonneg.mpr ln.2.1)
    have second := mul_nonneg ln.1 (sub_nonneg.mpr on.2.1)
    dsimp [J]
    nlinarith only [first,second]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg on.1 lp.le) (mul_nonneg op.le ln.1)
  have wall := ThreeSquare.bottom_wall O op.le box
  rw [abs_of_nonneg on.1] at wall
  have bottom : 0≤O.c*O.loV+O.s*O.loU := by
    dsimp [centerY] at wall
    nlinarith only [wall]
  have form : lower O L.c L.s=J*O.loU-H*(O.loV+O.side) := by
    rw [ls,lower_in_bands]
    have first : L.c*O.c+(-r)*O.s=J := by dsimp [J]; ring
    have second : -L.c*O.s+(-r)*O.c=-H := by dsimp [H]; ring
    rw [first,second,abs_of_nonneg jp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  have size := mul_pos (sub_pos.mpr side)
    (show 0<L.c+O.c*H by
      have nonnegative := mul_nonneg op.le hp
      linarith only [lp,nonnegative])
  have capped := mul_nonneg lp.le (sub_nonneg.mpr cap)
  have walled := mul_nonneg hp bottom
  have margin := corner_margin on shallow
  have first := mul_nonneg lp.le margin
  have second := mul_nonneg (mul_nonneg op.le (sub_nonneg.mpr ln.2.1))
    (sub_nonneg.mpr ob.2.1)
  have identity :
      O.c*((L.c-r)-lower O L.c L.s)=
        L.c*(2*O.c+(457/500)*O.s-(O.loU+O.side))+
        H*(O.c*O.loV+O.s*O.loU)+
        (O.side-1)*(L.c+O.c*H)+
        L.c*((1-O.c)^2+O.s*(O.c-457/500))+
        O.c*(L.c-r)*(1-O.c) := by
    rw [form]
    dsimp [J,H]
    linear_combination (-L.c*O.loU)*on.2.2
  have strict : 0<O.c*((L.c-r)-lower O L.c L.s) := by
    linarith only [identity,size,capped,walled,first,second]
  have low := pos_of_mul_pos_right strict op.le
  have un : L.c^2+L.s^2=1 := L.unit_normal
  have high := (strict_bounds L 1 1 L.c L.s un corner).2
  rw [ls] at high
  intro sep
  nlinarith only [low,high,sep]

#print axioms bottom_cosine
#print axioms negative_left_axis_impossible
end N12Compact.PositiveCentralEscapeLeft
