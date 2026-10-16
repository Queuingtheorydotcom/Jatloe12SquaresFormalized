import Compact.Completion.C1092.MPPMMissingNegativeCentersSupport

/-! MISSING-NEGATIVE-BOUNDARIES Theorems 2--3 for the actual neighboring
squares. Both directions of every face separation and weak face contact
are retained. Only each stated real wall is used. -/
namespace N12Compact.C1092MPPMMissingNegativeCenters
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports C1092ShallowBoundarySupport
open C1092MPPMMissingPositiveBoundaries.Envelopes
set_option Elab.async false

theorem bottom_order (C B : OpenSquare) (side : 1<C.side) (same : C.side=B.side)
    (d : Data C) (marker : B.Inside 0 (-543/500)) (outer : B.Inside (-2/5) (-1))
    (wall : ∀ x y,B.Inside x y→-2≤y)
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) : -1/5<centerX B := by
  classical
  apply lt_of_not_ge
  intro below
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have sp : 0< -C.s := by linarith only [d.faces.negative]
  have large := Data.large C side d
  have cb := bounds d.normal large
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper B nx ny≤lower C nx ny) : 0<ny ∧ nx<(413/500)*ny := by
    have a := (strict_bounds B _ _ nx ny unit marker).2
    have b := (strict_bounds C _ _ nx ny unit d.ordinaryP).1
    have c := (strict_bounds B _ _ nx ny unit outer).2
    have e := (strict_bounds C _ _ nx ny unit d.marker).1
    constructor <;> linarith only [a,b,c,e,sep]
  have central : ¬upper B (-C.c) (-C.s)≤lower C (-C.c) (-C.s) := by
    intro sep
    have height := bottom_center B wall
    have width := (negative_widths B d.normal).1
    rw [←same] at height width
    have heightWeight := mul_le_mul_of_nonneg_left height sp.le
    have centerWeight := mul_le_mul_of_nonpos_left below (by linarith only [cp] : -C.c≤0)
    have own : lower C (-C.c) (-C.s)=-(C.loU+C.side) := by
      rw [(C1092MixedCornerSupports.negative_support C C.c C.s).1,(ownU C).2]
    rw [own] at sep
    have margin := (central_margins d.normal large).1
    have coefficient : 0<3/2+(-C.s)*(C.c-C.s)/2 := by
      have product := mul_nonneg sp.le (show 0≤C.c-C.s by linarith only [cp,sp])
      nlinarith only [product]
    have extra := mul_pos (sub_pos.mpr side) coefficient
    dsimp [upper] at sep
    dsimp [Fb] at margin
    nlinarith only [sep,heightWeight,centerWeight,width,d.faces.lowerU,margin,extra]
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal B nx ny)
      (sep : upper B nx ny≤lower C nx ny) : False := by
    have direction := cone nx ny unit sep
    by_cases east : 0≤nx
    · have bound := (northeast C side d nx ny east direction.1 direction.2).1
      have point := (strict_bounds B _ _ nx ny unit outer).2
      nlinarith only [bound,point,sep]
    · let h := -nx
      have hn : 0≤h := by dsimp [h]; linarith only [east]
      have face' : FaceNormal B (-h) ny := by simpa only [h,neg_neg] using face
      have physical := bottom_face B h ny hn direction.1.le wall face'
      rw [←same] at physical
      have centerWeight := mul_le_mul_of_nonpos_left below (neg_nonpos.mpr hn)
      have margin := (northwest C side d h ny
        ⟨hn,direction.1.le,by dsimp [h]; nlinarith only [unit]⟩).1
      have sep' : upper B (-h) ny≤lower C (-h) ny := by simpa only [h,neg_neg] using sep
      nlinarith only [physical,centerWeight,margin,sep']
  obtain ⟨nx,ny,unit,face,sep⟩ := directed_faces B C same.symm
    (fun x y own => apart x y ⟨own.2,own.1⟩)
  rcases face with foreign|own
  · exact boundary nx ny unit foreign sep
  · rcases own with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,sp]
    · exact central sep
    · have bad := (cone _ _ unit sep).2
      linarith only [bad,cb.2.1,cb.2.2.1]
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,cp]

theorem left_order (C L : OpenSquare) (side : 1<C.side) (same : C.side=L.side)
    (d : Data C) (marker : L.Inside (-543/500) 0) (origin : L.Inside (-1) 0)
    (wall : ∀ x y,L.Inside x y→-2≤x)
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) : 1/5<centerY L := by
  classical
  apply lt_of_not_ge
  intro below
  have cp : 0<C.c := by linarith only [(normal_bounds d.normal).1]
  have sp : 0< -C.s := by linarith only [d.faces.negative]
  have large := Data.large C side d
  have cb := bounds d.normal large
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower L nx ny) : 0<ny ∧ nx<(175/368)*ny := by
    have a := (strict_bounds C _ _ nx ny unit d.ordinaryP).2
    have b := (strict_bounds L _ _ nx ny unit origin).1
    have c := (strict_bounds C _ _ nx ny unit d.marker).2
    have e := (strict_bounds L _ _ nx ny unit marker).1
    constructor <;> linarith only [a,b,c,e,sep]
  have central : ¬upper C (-C.c) (-C.s)≤lower L (-C.c) (-C.s) := by
    intro sep
    have horizontal := left_center L wall
    have width := (negative_widths L d.normal).2
    rw [←same] at horizontal width
    have horizontalWeight := mul_le_mul_of_nonneg_left horizontal cp.le
    have centerWeight := mul_le_mul_of_nonneg_left below sp.le
    have own : upper C (-C.c) (-C.s)=-C.loU := by
      rw [(C1092MixedCornerSupports.negative_support C C.c C.s).2,(ownU C).1]
    rw [own] at sep
    have margin := (central_margins d.normal large).2
    have coefficient : 0<3/2+C.c*(C.c-C.s)/2 := by
      have product := mul_nonneg cp.le (show 0≤C.c-C.s by linarith only [cp,sp])
      nlinarith only [product]
    have extra := mul_pos (sub_pos.mpr side) coefficient
    dsimp [lower] at sep
    dsimp [Fl] at margin
    nlinarith only [sep,horizontalWeight,centerWeight,width,d.faces.upperU,margin,extra]
  have boundary (nx ny : ℝ) (unit : nx^2+ny^2=1) (face : FaceNormal L nx ny)
      (sep : upper C nx ny≤lower L nx ny) : False := by
    have direction := cone nx ny unit sep
    by_cases east : 0≤nx
    · have bound := (northeast C side d nx ny east direction.1
        (by linarith only [direction.1,direction.2])).2
      have point := (strict_bounds L _ _ nx ny unit origin).1
      nlinarith only [bound,point,sep]
    · let h := -nx
      have hn : 0≤h := by dsimp [h]; linarith only [east]
      have face' : FaceNormal L (-h) ny := by simpa only [h,neg_neg] using face
      have physical := left_face L h ny hn direction.1.le wall face'
      rw [←same] at physical
      have centerWeight := mul_le_mul_of_nonneg_left below direction.1.le
      have margin := (northwest C side d h ny
        ⟨hn,direction.1.le,by dsimp [h]; nlinarith only [unit]⟩).2
      have sep' : upper C (-h) ny≤lower L (-h) ny := by simpa only [h,neg_neg] using sep
      nlinarith only [physical,centerWeight,margin,sep']
  obtain ⟨nx,ny,unit,face,sep⟩ := directed_faces C L same apart
  rcases face with own|foreign
  · rcases own with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,sp]
    · exact central sep
    · have bad := (cone _ _ unit sep).2
      linarith only [bad,cb.2.1,cb.2.2.1]
    · have bad := (cone _ _ unit sep).1
      linarith only [bad,cp]
  · exact boundary nx ny unit foreign sep

#print axioms bottom_order
#print axioms left_order
end N12Compact.C1092MPPMMissingNegativeCenters
