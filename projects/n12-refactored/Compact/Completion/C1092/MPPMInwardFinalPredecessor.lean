import Compact.Completion.C1092.MPPMInwardFinalScalars
import Compact.Completion.C1092.TwoFifthsSupport

/-! CENTERED-INWARD-OIOI §§1--3. The normal cover and all supports
belong to the same actual C/W pair. The listed preceding profile is a
separate producer; this local theorem does not assert an original case
entrance. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

theorem upward_axes (C W : OpenSquare) (same : C.side=W.side)
    (cp : 0<C.c) (cn : C.s≤0) (wp : 0<W.c) (wn : W.s≤0)
    (M : C.Inside (-7/20) (-7/20)) (N : W.Inside (-7/20) (7/20))
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) :
    upper C (-C.c) (-C.s)≤lower W (-C.c) (-C.s) ∨
      C.loV+C.side≤lower W (-C.s) C.c ∨
      upper C (-W.c) (-W.s)≤-(W.loU+W.side) ∨
      upper C (-W.s) W.c≤W.loV := by
  have choices := CongruentSAT.faceSeparation_of_disjoint C W same apart
  change pairRadius C W≤|C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W≤|-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C≤|W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C≤|-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at choices
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [eq])
  have upward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower W nx ny) : 0<ny := by
    have first := (strict_bounds C _ _ nx ny unit M).2
    have last := (strict_bounds W _ _ nx ny unit N).1
    linarith only [first,last,sep]
  rcases choices with cu|cv|wu|wv
  · rcases split _ _ _ (parallel_radius C W) cu with direct|back
    · have no := upward C.c C.s C.unit_normal direct
      exact False.elim (by linarith only [no,cn])
    · exact Or.inl (reverse C W _ _ back)
  · rcases split _ _ _ (transverse_radius C W) cv with direct|back
    · exact Or.inr (Or.inl (by simpa only [(ownV C).2] using direct))
    · have no := upward C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using reverse C W _ _ back)
      exact False.elim (by linarith only [no,cp])
  · have radius : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]; exact parallel_radius W C
    rcases split _ _ _ radius wu with direct|back
    · have no := upward W.c W.s W.unit_normal direct
      exact False.elim (by linarith only [no,wn])
    · have formula : lower W (-W.c) (-W.s)=-(W.loU+W.side) := by
        rw [lower_neg,(ownU W).2]
      right; right; left
      simpa only [formula] using reverse C W _ _ back
  · have radius : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]; exact transverse_radius W C
    rcases split _ _ _ radius wv with direct|back
    · right; right; right
      simpa only [(ownV W).1] using direct
    · have no := upward W.s (-W.c) (by nlinarith only [W.unit_normal])
        (by simpa only [neg_neg] using reverse C W _ _ back)
      exact False.elim (by linarith only [no,wp])

structure CenteredPredecessor (C W : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=W.side
  central : Normal C.c (-C.s)
  centralNegative : C.s<0
  predecessor : Normal W.c (-W.s)
  center : C.Inside 0 0
  marker : C.Inside (-7/20) (-7/20)
  previousMarker : W.Inside (-7/20) (7/20)
  markerCap : C.loU+C.side≤(7/20)*(C.c-C.s)
  firstCap : C.loU+C.side≤(7/50)*C.c-C.s/2
  halfSmall : half C.c (-C.s)<21/100
  lowerU : -W.c+W.s≤W.loU
  lowerV : (2/5)*W.c+W.s≤W.loV
  upperV : W.loV+W.side≤W.c
  apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)

/-- The only surviving normal is C's actual upward normal. Its bound
keeps the predecessor's two faces coupled through the same W angle. -/
theorem centered_predecessor_bound (C W : OpenSquare) (h : CenteredPredecessor C W) :
    C.loV+C.side<C.c*f W.c (-W.s)+C.s*g W.c (-W.s) := by
  have cb := normal_bounds h.central
  have wb := normal_bounds h.predecessor
  have cp : 0<C.c := by linarith only [cb.1]
  have wp : 0<W.c := by linarith only [wb.1]
  have angle := predecessor_angle h.predecessor
    (show 1< -W.s+(3/5)*W.c by linarith only [h.lowerV,h.upperV,h.side,h.same])
  let k := C.c*W.c+C.s*W.s
  let delta := C.s*W.c-C.c*W.s
  have kp : 0<k := by
    have first := mul_pos cp wp
    have last := mul_nonneg h.central.1 h.predecessor.1
    dsimp [k]
    nlinarith only [first,last]
  have dp : 0<delta := by
    have order := relative_order h.central h.predecessor
      (show half C.c (-C.s)<half W.c (-W.s) by linarith only [h.halfSmall,angle.1])
    dsimp [delta]
    nlinarith only [order]
  have Ap : 0<C.loU+C.side := by linarith only [h.center.2.1]
  have Hp : 0<C.loV+C.side := by linarith only [h.center.2.2.2]
  have choices := upward_axes C W h.same cp h.centralNegative.le wp
    (by linarith only [h.predecessor.1]) h.marker h.previousMarker h.apart
  have own : C.loV+C.side≤lower W (-C.s) C.c := by
    rcases choices with first|own|last|lastV
    · have formula : upper C (-C.c) (-C.s)= -C.loU := by rw [upper_neg,(ownU C).1]
      have mark := (strict_bounds W _ _ (-C.c) (-C.s)
        (by nlinarith only [C.unit_normal]) h.previousMarker).1
      rw [formula] at first
      exact False.elim (by nlinarith only [first,mark,h.markerCap,h.side,cb.2.2.2.2.2])
    · exact own
    · have formula := upper_np C (-W.c) (-W.s) (-k) delta
        (by dsimp [k]; ring) (by dsimp [delta]; ring)
        (by linarith only [kp]) dp.le
      have cap := mul_nonneg kp.le
        (show 0≤(7/50)*C.c-C.s/2-(C.loU+C.side) by linarith only [h.firstCap])
      have height := mul_pos dp Hp
      have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k by linarith only [kp])
      have margin := predecessor_margin h.central h.predecessor h.halfSmall
      dsimp [k,delta] at formula cap height strict
      exact False.elim (by nlinarith only [last,formula,cap,height,strict,margin,h.lowerU,h.same])
    · have formula := upper_pos_pos C (-W.s) W.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) dp.le kp.le
      have first := mul_pos dp Ap
      have last := mul_pos kp Hp
      exact False.elim (by nlinarith only [lastV,formula,first,last,h.upperV,h.same,h.side,wb.2.1])
  have formula := lower_np W (-C.s) C.c (-delta) k
    (by dsimp [delta]; ring) (by dsimp [k]; ring)
    (by linarith only [dp]) kp.le
  have first := mul_nonneg dp.le
    (show 0≤W.loU+W.c-W.s by linarith only [h.lowerU])
  have last := mul_nonneg kp.le
    (show 0≤W.c-C.side-W.loV by linarith only [h.upperV,h.same])
  have strict := mul_pos (sub_pos.mpr h.side) (add_pos dp kp)
  have bound : C.loV+C.side<delta*(W.c-W.s-1)+k*(W.c-1) := by
    rw [←h.same] at formula
    nlinarith only [own,formula,first,last,strict]
  have identity : delta*(W.c-W.s-1)+k*(W.c-1)=
      C.c*f W.c (-W.s)+C.s*g W.c (-W.s) := by
    dsimp [delta,k,f,g]
    linear_combination (C.c/2)*W.unit_normal
  rwa [identity] at bound

theorem centered_predecessor (C W : OpenSquare) (h : CenteredPredecessor C W) :
    C.loV+C.side<C.c/11+C.s/2 ∧
      49/50<C.c ∧ -C.s<9/50 ∧ half C.c (-C.s)<91/1000 := by
  have angle := predecessor_angle h.predecessor
    (show 1< -W.s+(3/5)*W.c by linarith only [h.lowerV,h.upperV,h.side,h.same])
  have bound := centered_predecessor_bound C W h
  have sharp := centered_height h.central h.predecessor
    (show 0< -W.s by linarith only [angle.2.2])
    (show 0<C.loV+C.side by linarith only [h.center.2.2.2])
    (by nlinarith only [bound])
  have small := centered_small h.central (by linarith only [h.centralNegative]) sharp.2
  exact ⟨by linarith only [sharp.1],small⟩

#print axioms upward_axes
#print axioms centered_predecessor
end N12Compact.C1092MPPMInwardFinal
