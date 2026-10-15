import Compact.Geometry.WallSignChordPositive
import Compact.Geometry.WallSignChordNegative

/-! Theorem 1 of C1092-WALL-SIGN-CHORD: a single actual left wall,
one actual marker, one omitted central marker and the closed center sign
force the entire strict chord. No enclosure, side cap or auxiliary owner
is assumed. Source translation only; compiler replay remains pending. -/
namespace N12Compact.WallSignChord
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- Closing the single real wall at its extreme vertex. No lower wall
or other coordinate bound is inserted into the hypotheses. -/
private theorem positive_left_wall (q : OpenSquare)
    (wall : ∀ x y,q.Inside x y → -1≤x) :
    q.side*(q.c+q.s)/2-1≤centerX q := by
  have endpoint : 0≤1+q.c*q.loU-q.s*(q.loV+q.side) := by
    apply affine_endpoint_nonnegative q.side (q.c+q.s) _ q.side_pos
    intro t positive small
    let u := q.loU+t
    let v := q.loV+q.side-t
    have own : q.Inside (q.c*u-q.s*v) (q.s*u+q.c*v) := by
      apply (inside_iff_rotated_box q _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      exact ⟨by linarith only [positive],by linarith only [small],
        by linarith only [small],by linarith only [positive]⟩
    have bound := wall _ _ own
    dsimp only [u,v] at bound
    nlinarith only [bound]
  dsimp only [centerX]
  nlinarith only [endpoint]

/-- The translated physical theorem, before returning to the original
coordinates. Face reindexing preserves the actual center and ownership. -/
theorem local_point (q : OpenSquare) (ha : 1<q.side)
    (wall : ∀ x y,q.Inside x y → -1≤x)
    (marker : q.Inside (-43/500) 0)
    (missing : ¬q.Inside (13/20) (7/20))
    (sign : 0≤centerY q) (r : ℝ)
    (rlow : 11/50≤r) (rhigh : r≤39/100) : q.Inside 0 r := by
  obtain ⟨p,cn,sn,side,_,cy,same⟩ := exists_positive_frame q
  have pwall : ∀ x y,p.Inside x y → -1≤x :=
    fun x y own => wall x y ((same x y).mp own)
  have bound := positive_left_wall p pwall
  have pside : 1<p.side := by simpa only [side] using ha
  have psign : 0≤centerY p := by simpa only [cy] using sign
  have pmarker := (same _ _).mpr marker
  have pmissing : ¬p.Inside (13/20) (7/20) :=
    fun own => missing ((same _ _).mp own)
  apply (same _ _).mp
  by_cases order : p.s≤p.c
  · exact positive_point p r pside cn sn order bound psign pmarker pmissing rlow rhigh
  · let t := turnFrame (turnFrame (turnFrame p))
    have tc : t.c=p.s := by dsimp only [t,turnFrame]; ring
    have ts : t.s= -p.c := by dsimp only [t,turnFrame]; ring
    have ta : t.side=p.side := rfl
    have tx : centerX t=centerX p := by simp only [t,turnFrame_centerX]
    have ty : centerY t=centerY p := by simp only [t,turnFrame_centerY]
    have inside (x y : ℝ) : t.Inside x y↔p.Inside x y := by
      simp only [t,turnFrame_inside]
    have tbound : t.side*(t.c+p.c)/2-1≤centerX t := by
      rw [ta,tc,tx]
      nlinarith only [bound]
    have result := negative_point t p.c r ts
      (by simpa only [ta] using pside) (by simpa only [tc] using sn) cn
      (by rw [tc]; exact (lt_of_not_ge order).le) tbound
      (by simpa only [ty] using psign) ((inside _ _).mpr pmarker)
      (fun own => pmissing ((inside _ _).mp own)) rlow rhigh
    exact (inside _ _).mp result

/-- The literal whole closed chord in the original coordinate system.
Every point is strictly owned, including both chord endpoints, every
orientation endpoint, and equality in the actual center sign. -/
theorem chord (q : OpenSquare) (ha : 1<q.side)
    (wall : ∀ x y,q.Inside x y → 0≤x)
    (marker : q.Inside (457/500) 2)
    (missing : ¬q.Inside (33/20) (47/20))
    (sign : 2≤centerY q) (r : ℝ)
    (rlow : 111/50≤r) (rhigh : r≤239/100) : q.Inside 1 r := by
  have shiftedWall : ∀ x y,(q.translated 1 2).Inside x y → -1≤x := by
    intro x y own
    have bound := wall _ _ ((inside_translated_iff _ _ _ _ _).mp own)
    linarith only [bound]
  have shiftedMarker : (q.translated 1 2).Inside (-43/500) 0 := by
    norm_num only [inside_translated_iff]
    exact marker
  have shiftedMissing : ¬(q.translated 1 2).Inside (13/20) (7/20) := by
    norm_num only [inside_translated_iff]
    exact missing
  have centerShift : centerY (q.translated 1 2)=centerY q-2 := by
    dsimp only [centerY,OpenSquare.translated]
    nlinarith only [q.unit_normal]
  have result := local_point (q.translated 1 2) ha shiftedWall shiftedMarker
    shiftedMissing (by rw [centerShift]; linarith only [sign]) (r-2)
    (by linarith only [rlow]) (by linarith only [rhigh])
  simpa only [inside_translated_iff,add_zero,show 2+(r-2)=r by ring] using result

end
#print axioms chord
end N12Compact.WallSignChord
