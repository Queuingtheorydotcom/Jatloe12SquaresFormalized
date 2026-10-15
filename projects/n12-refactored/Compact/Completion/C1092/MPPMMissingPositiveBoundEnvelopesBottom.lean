import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopesScalars
import Compact.Completion.C1092.MixedCornerSupports

/-! The actual bottom-square envelope, with every signed separating
normal retained. The two literal anchors and the real bottom wall are
the whole boundary input; no independent support position is assumed. -/
namespace N12Compact.C1092MPPMMissingPositiveBoundaries
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowBoundarySupport C1092ShallowCentralScalars
set_option Elab.async false

namespace Envelopes
theorem face_neg (Q : OpenSquare) (x y : ℝ) (h : FaceNormal Q x y) :
    FaceNormal Q (-x) (-y) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
  · exact Or.inl ⟨by ring,by ring⟩
  · exact Or.inr (Or.inr (Or.inr ⟨by ring,rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl,by ring⟩))

/-- Exhaustive weak separation: no canonical orientation of either
boundary square is selected or discarded. -/
theorem directed_faces (A B : OpenSquare) (same : A.side=B.side)
    (apart : ∀ x y,¬(A.Inside x y ∧ B.Inside x y)) :
    ∃ nx ny : ℝ,nx^2+ny^2=1 ∧ (FaceNormal A nx ny ∨ FaceNormal B nx ny) ∧
      upper A nx ny≤lower B nx ny := by
  have choose (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (face : FaceNormal A nx ny ∨ FaceNormal B nx ny)
      (sep : upper A nx ny≤lower B nx ny ∨ upper B nx ny≤lower A nx ny) :
      ∃ nx ny : ℝ,nx^2+ny^2=1 ∧ (FaceNormal A nx ny ∨ FaceNormal B nx ny) ∧
        upper A nx ny≤lower B nx ny := by
    rcases sep with forward|reverse
    · exact ⟨nx,ny,unit,face,forward⟩
    · refine ⟨-nx,-ny,by nlinarith only [unit],?_,?_⟩
      · exact face.elim (fun h => Or.inl (face_neg A nx ny h))
          (fun h => Or.inr (face_neg B nx ny h))
      · rw [(C1092MixedCornerSupports.negative_support A nx ny).2,
          (C1092MixedCornerSupports.negative_support B nx ny).1]
        exact neg_le_neg reverse
  have all := CongruentSAT.faceSeparation_of_disjoint A B same apart
  change pairRadius A B≤|A.c*(centerX B-centerX A)+A.s*(centerY B-centerY A)| ∨
    pairRadius A B≤|-A.s*(centerX B-centerX A)+A.c*(centerY B-centerY A)| ∨
    pairRadius B A≤|B.c*(centerX B-centerX A)+B.s*(centerY B-centerY A)| ∨
    pairRadius B A≤|-B.s*(centerX B-centerX A)+B.c*(centerY B-centerY A)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius B nx ny=radius)
      (sep : radius≤|nx*(centerX B-centerX A)+ny*(centerY B-centerY A)|) :=
    separated A B nx ny (by rwa [identity])
  rcases all with au|av|bu|bv
  · exact choose A.c A.s A.unit_normal (Or.inl (Or.inl ⟨rfl,rfl⟩))
      (split _ _ _ (parallel_radius A B) au)
  · exact choose (-A.s) A.c (by nlinarith only [A.unit_normal])
      (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))
      (split _ _ _ (transverse_radius A B) av)
  · have radius : supportRadius A B.c B.s+supportRadius B B.c B.s=pairRadius B A := by
      rw [add_comm]; exact parallel_radius B A
    exact choose B.c B.s B.unit_normal (Or.inr (Or.inl ⟨rfl,rfl⟩)) (split _ _ _ radius bu)
  · have radius : supportRadius A (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B A := by
      rw [add_comm]; exact transverse_radius B A
    exact choose (-B.s) B.c (by nlinarith only [B.unit_normal])
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))) (split _ _ _ radius bv)

theorem northeast_coefficients (C : OpenSquare) (side : 1<C.side) (d : Data C) :
    -C.c+C.s+7/50-(37/50)*C.s^2<0 ∧
    1-C.c-C.s+(37/50)*C.c*C.s<0 ∧
    0<C.c-C.s+(11/25)*C.s^2 ∧
    0<C.c+C.s-1-(11/25)*C.c*C.s := by
  have p := profile C side d
  have cb := normal_bounds d.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have cross := mul_pos cp p.positive
  have sum : C.c+C.s≤3/2 := by
    nlinarith only [C.unit_normal,sq_nonneg (C.c-C.s),cp,d.normal.1]
  have first := mul_nonneg (sub_nonneg.mpr d.normal.2.1)
    (show 0≤1-(37/100)*(C.c+C.s) by linarith only [sum])
  have curved := C1092ShallowCentralScalars.arc d.normal
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [first,C.unit_normal]
  · nlinarith only [curved,cross]
  · nlinarith only [d.normal.2.1,sq_pos_of_pos p.positive]
  · nlinarith only [curved,cross]
end Envelopes

theorem bottom_order (C B : OpenSquare) (side : 1<C.side) (cap : C.side≤1001/1000)
    (same : C.side=B.side) (d : Data C)
    (marker : B.Inside 0 (-543/500)) (outer : B.Inside (-2/5) (-1))
    (wall : ∀ x y,B.Inside x y→-2≤y)
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) :
    b C.side C.c C.s (C.loV+C.side)≤centerX B := by
  classical
  apply le_of_not_gt
  intro below
  have p := profile C side d
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have sp := p.positive
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper B nx ny≤lower C nx ny) : 0<ny ∧ nx<(413/500)*ny := by
    have a := (strict_bounds B _ _ nx ny unit marker).2
    have b := (strict_bounds C _ _ nx ny unit d.ordinaryP).1
    have c := (strict_bounds B _ _ nx ny unit outer).2
    have e := (strict_bounds C _ _ nx ny unit d.marker).1
    constructor <;> linarith only [a,b,c,e,sep]
  have central : ¬upper B (-C.s) C.c≤lower C (-C.s) C.c := by
    intro sep
    have height := bottom_center B wall
    have width := (width_bounds B d.normal).1
    rw [←same] at height width
    have heightWeight := mul_nonneg cp.le (sub_nonneg.mpr height)
    have widthGap := sub_nonneg.mpr width
    have strict := mul_pos sp (sub_pos.mpr below)
    have coordinate : C.s*b C.side C.c C.s (C.loV+C.side)=
        C.side*(3/2+C.c*(C.c+C.s)/2)-(C.loV+C.side)-2*C.c := by
      dsimp [b]; field_simp [sp.ne']
    have identity : upper B (-C.s) C.c-C.loV=
        C.s*(b C.side C.c C.s (C.loV+C.side)-centerX B)+
        C.c*(centerY B+2-C.side*width0 B/2)+
        (C.c*(C.side*width0 B/2)+supportRadius B (-C.s) C.c-
          C.side*(1+C.c*(C.c+C.s))/2) := by
      dsimp [upper]; linear_combination -coordinate
    have heightGap : 0≤C.c*(centerY B+2-C.side*width0 B/2) := by
      convert heightWeight using 1 <;> ring
    have positive : 0<upper B (-C.s) C.c-C.loV := by
      rw [identity]
      exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg strict heightGap) widthGap
    rw [(ownV C).1] at sep
    exact (not_lt_of_ge (sub_nonpos.mpr sep)) positive
  have northeast (nx ny : ℝ) (unit : nx^2+ny^2=1) (east : 0≤nx)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    have direction := cone nx ny unit sep
    let lambda := C.c*nx+C.s*ny
    let mu := C.c*ny-C.s*nx
    have lp : 0<lambda := add_pos_of_nonneg_of_pos (mul_nonneg cp.le east) (mul_pos sp direction.1)
    have mp : 0<mu := by
      have first := mul_nonneg (sub_nonneg.mpr d.normal.2.1) direction.1.le
      have last := mul_pos sp (show 0<ny-nx by linarith only [direction.1,direction.2])
      dsimp [mu]; nlinarith only [first,last]
    have support := lower_nn C nx ny lambda mu (by dsimp [lambda]; ring)
      (by dsimp [mu]; ring) lp.le mp.le
    have uWeight := mul_le_mul_of_nonneg_left
      (show C.loU≤-(13/50)*C.c-C.side by linarith only [p.upperU]) lp.le
    have vWeight := mul_le_mul_of_nonneg_left
      (show C.loV≤C.s-C.side by linarith only [p.upperV]) mp.le
    have extra := mul_pos (sub_pos.mpr side) (add_pos lp mp)
    have bound : lower C nx ny<lambda*(-(13/50)*C.c-1)+mu*(C.s-1) := by
      calc
        _ = lambda*C.loU+mu*C.loV := support
        _ ≤ lambda*(-(13/50)*C.c-C.side)+mu*(C.s-C.side) := add_le_add uWeight vWeight
        _ < lambda*(-(13/50)*C.c-1)+mu*(C.s-1) := by
          apply sub_pos.mp; convert extra using 1 <;> ring
    have coefficients := Envelopes.northeast_coefficients C side d
    have first := mul_nonpos_of_nonneg_of_nonpos east coefficients.1.le
    have last := mul_neg_of_pos_of_neg direction.1 coefficients.2.1
    have margin : lambda*(-(13/50)*C.c-1)+mu*(C.s-1)-((-2/5)*nx-ny)<0 := by
      have identity : lambda*(-(13/50)*C.c-1)+mu*(C.s-1)-((-2/5)*nx-ny)=
          nx*(-C.c+C.s+7/50-(37/50)*C.s^2)+ny*(1-C.c-C.s+(37/50)*C.c*C.s) := by
        dsimp [lambda,mu]; linear_combination -(13/50)*nx*C.unit_normal
      rw [identity]; exact add_neg_of_nonpos_of_neg first last
    have point := (strict_bounds B _ _ nx ny unit outer).2
    have comparison : lambda*(-(13/50)*C.c-1)+mu*(C.s-1)<nx*(-2/5)+ny*(-1) := by
      convert sub_neg.mp margin using 1 <;> ring
    exact (not_lt_of_ge sep) ((bound.trans comparison).trans point)
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal B nx ny)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    by_cases east : 0≤nx
    · exact northeast nx ny unit east sep
    have direction := cone nx ny unit sep
    let h := -nx
    have hp : 0<h := by dsimp [h]; linarith only [east]
    have face' : FaceNormal B (-h) ny := by simpa only [h,neg_neg] using face
    have bottom := bottom_face B h ny hp.le direction.1.le wall face'
    rw [←same] at bottom
    let delta := C.s*ny-C.c*h
    let kappa := C.s*h+C.c*ny
    have kp : 0<kappa := add_pos_of_nonneg_of_pos (mul_nonneg sp.le hp.le) (mul_pos cp direction.1)
    have formula : lower C (-h) ny=delta*(C.loU+C.side)+kappa*C.loV-C.side*max delta 0 := by
      by_cases sign : 0≤delta
      · rw [lower_nn C (-h) ny delta kappa (by dsimp [delta]; ring)
          (by dsimp [kappa]; ring) sign kp.le,max_eq_left sign]; ring
      · have sign' : delta≤0 := (lt_of_not_ge sign).le
        rw [lower_np C (-h) ny delta kappa (by dsimp [delta]; ring)
          (by dsimp [kappa]; ring) sign' kp.le,max_eq_right sign']; ring
    have margin := (Envelopes.margins C side cap d h ny hp.le direction.1.le
      (by dsimp [h]; nlinarith only [unit])).1
    have strict := mul_pos hp (sub_pos.mpr below)
    have physical : Envelopes.bottomGap C.side C.c C.s (C.loU+C.side) (C.loV+C.side) h ny+
        h*(b C.side C.c C.s (C.loV+C.side)-centerX B)≤upper B (-h) ny-lower C (-h) ny := by
      calc
        _ = -h*centerX B-2*ny+(C.side/2)*(1+ny^2+h*ny)-lower C (-h) ny := by
          rw [formula]; dsimp [Envelopes.bottomGap,delta,kappa]; ring
        _ ≤ _ := sub_le_sub_right bottom _
    have positive := (add_pos_of_nonneg_of_pos margin strict).trans_le physical
    have sep' : upper B (-h) ny≤lower C (-h) ny := by simpa only [h,neg_neg] using sep
    exact (not_lt_of_ge (sub_nonpos.mpr sep')) positive
  obtain ⟨nx,ny,unit,face,sep⟩ := Envelopes.directed_faces B C same.symm
    (fun x y own => apart x y ⟨own.2,own.1⟩)
  rcases face with foreign|own
  · exact boundary nx ny unit foreign sep
  · rcases own with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have bad := (cone _ _ unit sep).2
      linarith only [bad,d.normal.2.1,sp]
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,sp]
    · exact central sep
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,cp]

#print axioms bottom_order
end N12Compact.C1092MPPMMissingPositiveBoundaries
