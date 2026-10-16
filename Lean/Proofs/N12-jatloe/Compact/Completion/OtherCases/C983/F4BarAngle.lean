import Compact.Completion.OtherCases.C983.F4BarAngleScalars
import Compact.Completion.OtherCases.BottomBarSupport
import S12.ShortCluster.Projections

/-! C983-F4-BAR-ANGLE-REDUCTION, Theorem 1, for both actual northeast
cap points. The whole-bar alternative is the existing closed-vertex
support theorem; it retains every point of the foreign segment and all
tangent edge and vertex cases from the manuscript. -/
namespace N12Compact.Completion.OtherCases.C983.F4BarAngle
open S12 S12Pilot
set_option Elab.async false

theorem bounds (E : OpenSquare) (t alpha beta : ℝ) (signed : E.s= -t)
    (side : 1<E.side) (cp : 0<E.c) (tn : 0≤t) (order : t≤E.c)
    (marker : E.Inside (7/20) (-7/20)) (elbow : E.Inside (13/50) 0)
    (outer : E.Inside 1 (-13/50)) (missingF : ¬E.Inside 0 (-13/50))
    (missingK : ¬E.Inside alpha beta)
    (avoid : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1))
    (parameters : (alpha=21/40 ∧ beta=1/8) ∨ (alpha=21/50 ∧ beta=4/25)) :
    (13/50)*t≤E.loU ∧ (4/5)*t-E.c≤E.loV ∧
      E.loV+E.side≤alpha*t+beta*E.c ∧ t/(1+E.c)<3/20 := by
  have unit : E.c^2+t^2=1 := by simpa only [signed,neg_sq] using E.unit_normal
  have an : 0≤alpha := by rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  have ahi : alpha≤21/40 := by rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  have bp : 0<beta := by rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  have bhi : beta≤4/25 := by rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  have increment : beta≤alpha-13/50 := by
    rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  have balance : alpha+3*beta=9/10 := by
    rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  have m := marker
  have d := elbow
  have a := outer
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,
    mul_one,mul_neg,add_zero,zero_add] at m d a
  have cap : E.loV+E.side≤alpha*t+beta*E.c := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr increment)
    have second := mul_nonneg bp.le (sub_nonneg.mpr order)
    have third := mul_nonneg tn (show 0≤alpha-13/50 by linarith only [increment,bp])
    have fourth := mul_pos cp bp
    have fifth := mul_pos cp (show 0<1-alpha by linarith only [ahi])
    have sixth := mul_nonneg tn (show 0≤beta+13/50 by linarith only [bp])
    apply le_of_not_gt
    intro high
    apply missingK
    simp only [OpenSquare.Inside,InBands,signed,neg_neg]
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [d.1,d.2.2.1,a.2.1,high,first,second,third,fourth,fifth,sixth]
  have short := (short_projections E (21/50) (-21/40) (by norm_num)).2.1
  rw [signed] at short
  have first := mul_nonneg tn (sub_nonneg.mpr ahi)
  have second := mul_nonneg cp.le (sub_nonneg.mpr bhi)
  have lowV : E.loV< -(13/50)*E.c := by
    nlinarith only [cap,side,short,first,second]
  have lowU : (13/50)*t≤E.loU := by
    apply le_of_not_gt
    intro low
    apply missingF
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,lowV,d.2.1,d.2.2.2,cp,tn,order]
  have bar := BottomBarSupport.negative E t signed side cp tn order
    (by linarith only [lowU,tn]) marker elbow avoid
  have last : (4/5)*t-E.c≤E.loV := by
    apply le_of_not_gt
    intro missingLast
    have vertex : -1≤ -t*(E.loU+E.side)+E.c*E.loV :=
      bar.2.resolve_left (by linarith only [missingLast])
    have lastCap : E.loU+E.side≤(4/5)*E.c+t := by
      apply le_of_not_gt
      intro high
      apply avoid (4/5) (by norm_num) le_rfl
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg_one]
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [m.1,m.2.2.2,high,missingLast,cp,tn,order]
    have width : 1<(4/5)*E.c+(37/50)*t := by linarith only [lastCap,lowU,side]
    have steep := F4BarAngleScalars.slope E.c t cp tn unit width
    have gap := F4BarAngleScalars.vertex_gap E.c t alpha beta cp tn order unit
      steep an ahi bp.le balance
    have first := mul_nonneg tn (sub_nonneg.mpr lowU)
    have second := mul_nonneg cp.le (sub_nonneg.mpr cap)
    have third := mul_pos (sub_pos.mpr side) (show 0<E.c+t by linarith only [cp,tn])
    nlinarith only [vertex,gap,first,second,third]
  have half := F4BarAngleScalars.half E.c t alpha beta cp tn order unit parameters
    (by nlinarith only [side,last,cap])
  exact ⟨lowU,last,cap,half⟩

#print axioms bounds
end N12Compact.Completion.OtherCases.C983.F4BarAngle
