import S12.SingletonForcing

/-! The seven-triangle missing-corner fan in Appendix A.3 of
05_C580_MATH_DONE__FORMAL_PENDING. The fixed four triangles are reused
from SingletonTriangles; the added vertex is the genuinely excluded (1,1).
The planar covers below are proved by linear inequalities, with boundary
centers retained throughout. -/
namespace N12Compact.CommonCases.SingletonMissing
open S12 S12Pilot
set_option Elab.async false

private theorem lower_fan (q : OpenSquare) (ha : 1<q.side)
    (hx0 : 457/500≤centerX q) (hx1 : centerX q≤2)
    (hy0 : 457/500≤centerY q) (hy1 : centerY q≤2)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i) :
    rep0tri0w2 (centerX q) (centerY q)<0 ∧
      rep0tri3w1 (centerX q) (centerY q)<0 := by
  have b : ¬q.Inside (457/500) 1 := by simpa [Owns,marker] using hout 1 (by decide)
  have s : ¬q.Inside (33/20) (33/20) := by simpa [Owns,marker] using hout 8 (by decide)
  have e : ¬q.Inside (47/20) (33/20) := by simpa [Owns,marker] using hout 9 (by decide)
  have d : ¬q.Inside (33/20) (47/20) := by simpa [Owns,marker] using hout 11 (by decide)
  have c : ¬q.Inside (457/500) 2 := by simpa [Owns,marker] using hout 12 (by decide)
  have f : ¬q.Inside 2 (457/500) := by simpa [Owns,marker] using hout 13 (by decide)
  have h0 (h₀ : 0≤rep0tri0w0 (centerX q) (centerY q))
      (h₁ : 0≤rep0tri0w1 (centerX q) (centerY q))
      (h₂ : 0≤rep0tri0w2 (centerX q) (centerY q)) : False :=
    (rep0tri0_hit q ha h₀ h₁ h₂).elim s (fun h => h.elim b c)
  have h1 (h₀ : 0≤rep0tri1w0 (centerX q) (centerY q))
      (h₁ : 0≤rep0tri1w1 (centerX q) (centerY q))
      (h₂ : 0≤rep0tri1w2 (centerX q) (centerY q)) : False :=
    (rep0tri1_hit q ha h₀ h₁ h₂).elim s (fun h => h.elim c d)
  have h2 (h₀ : 0≤rep0tri2w0 (centerX q) (centerY q))
      (h₁ : 0≤rep0tri2w1 (centerX q) (centerY q))
      (h₂ : 0≤rep0tri2w2 (centerX q) (centerY q)) : False :=
    (rep0tri2_hit q ha h₀ h₁ h₂).elim s (fun h => h.elim d e)
  have h3 (h₀ : 0≤rep0tri3w0 (centerX q) (centerY q))
      (h₁ : 0≤rep0tri3w1 (centerX q) (centerY q))
      (h₂ : 0≤rep0tri3w2 (centerX q) (centerY q)) : False :=
    (rep0tri3_hit q ha h₀ h₁ h₂).elim s (fun h => h.elim e f)
  dsimp [rep0tri0w0,rep0tri0w1,rep0tri0w2,rep0tri1w0,rep0tri1w1,rep0tri1w2,
    rep0tri2w0,rep0tri2w1,rep0tri2w2,rep0tri3w0,rep0tri3w1,rep0tri3w2] at h0 h1 h2 h3 ⊢
  constructor
  · by_contra bad
    have bad := le_of_not_gt bad
    by_cases hx : centerX q≤33/20
    · by_cases hu : 0≤(-175/368)*centerX q-centerY q+17919/7360
      · exact h0 (by linarith only [hx0]) (by linarith only [hu]) bad
      · exact h1 (by linarith only [hx0,hy1]) (by linarith only [hx]) (by linarith only [hu])
    · exact h2 (by linarith only [hx1,hy1]) (by linarith only [hx,bad]) (by linarith only [hx])
  · by_contra bad
    have bad := le_of_not_gt bad
    by_cases hy : centerY q≤33/20
    · exact h3 (by linarith only [hx1,hy0]) bad (by linarith only [hy])
    · by_cases hx : 33/20≤centerX q
      · exact h2 (by linarith only [hx1,hy1]) (by linarith only [hy]) (by linarith only [hx])
      · exact h1 (by linarith only [hx0,hy1]) (by linarith only [hx]) (by linarith only [hx,hy,bad])

private theorem below_diagonal (q : OpenSquare) (ha : 1<q.side)
    (hy : 1≤centerY q) (fan : rep0tri0w2 (centerX q) (centerY q)<0)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i) (missing : ¬q.Inside 1 1) :
    centerY q<centerX q := by
  by_contra bad
  have bad : centerX q≤centerY q := le_of_not_gt bad
  let m := (20/13)*(centerY q-1)
  let b := (500/43)*(centerY q-centerX q)
  have mn : 0≤m := by dsimp [m]; linarith only [hy]
  have bn : 0≤b := by dsimp [b]; linarith only [bad]
  have en : 0≤1-m-b := by
    dsimp [m,b,rep0tri0w2] at fan ⊢
    linarith only [fan]
  have hit := triangle_nonavoidance q ha 1 1 (457/500) 1 (33/20) (33/20)
    (1-m-b) b m en bn mn (by ring)
    (by dsimp [m,b]; ring) (by dsimp [m,b]; ring)
    (by norm_num) (by norm_num) (by norm_num)
  have noB : ¬q.Inside (457/500) 1 := by simpa [Owns,marker] using hout 1 (by decide)
  have noM : ¬q.Inside (33/20) (33/20) := by simpa [Owns,marker] using hout 8 (by decide)
  exact hit.elim missing (fun h => h.elim noB noM)

private theorem target182_right_triangle (q : OpenSquare) (ha : 1<q.side)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i)
    (wF wM : ℝ) (f : 0≤wF) (m : 0≤wM) (t : 0≤1-wF-wM)
    (hx : (1-wF-wM)*(91/50)+wF*2+wM*(33/20)=centerX q)
    (hy : (1-wF-wM)+wF*(457/500)+wM*(33/20)=centerY q) :
    q.Inside (91/50) 1 := by
  have hit := triangle_nonavoidance q ha (91/50) 1 2 (457/500) (33/20) (33/20)
    (1-wF-wM) wF wM t f m (by ring) hx (by simpa only [mul_one] using hy)
    (by norm_num) (by norm_num) (by norm_num)
  have noF : ¬q.Inside 2 (457/500) := by simpa [Owns,marker] using hout 13 (by decide)
  have noM : ¬q.Inside (33/20) (33/20) := by simpa [Owns,marker] using hout 8 (by decide)
  exact hit.resolve_right (fun h => h.elim noF noM)

theorem replacement182_left (q : OpenSquare) (ha : 1<q.side)
    (hx0 : 457/500≤centerX q) (hx1 : centerX q≤91/50)
    (hy0 : 1≤centerY q) (hy1 : centerY q≤2)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i) (missing : ¬q.Inside 1 1) :
    q.Inside (91/50) 1 := by
  obtain ⟨fanL,fanR⟩ := lower_fan q ha hx0 (by linarith only [hx1])
    (by linarith only [hy0]) hy1 hout
  have diagonal := below_diagonal q ha hy0 fanL hout missing
  let wt := (50/41)*(centerX q-centerY q)
  let wm := (20/13)*(centerY q-1)
  by_cases wi : 0≤1-wt-wm
  · have tn : 0≤wt := by dsimp [wt]; linarith only [diagonal]
    have mn : 0≤wm := by dsimp [wm]; linarith only [hy0]
    have hit := triangle_nonavoidance q ha (91/50) 1 (33/20) (33/20) 1 1
      wt wm (1-wt-wm) tn mn wi (by ring)
      (by dsimp [wt,wm]; ring) (by dsimp [wt,wm]; ring)
      (by norm_num) (by norm_num) (by norm_num)
    have noM : ¬q.Inside (33/20) (33/20) := by simpa [Owns,marker] using hout 8 (by decide)
    exact hit.resolve_right (fun h => h.elim noM missing)
  · let wf := (50000/5119)*((13/20)*(centerX q-91/50)+(17/100)*(centerY q-1))
    let wm' := (50000/5119)*((9/50)*(centerY q-1)+(43/500)*(centerX q-91/50))
    apply target182_right_triangle q ha hout wf wm'
    · dsimp [wf,wt,wm] at wi ⊢; linarith only [wi]
    · dsimp [wm',wt,wm] at wi ⊢; linarith only [wi,hy0]
    · dsimp [wf,wm',rep0tri3w1] at fanR ⊢; linarith only [fanR]
    · dsimp [wf,wm']; ring
    · dsimp [wf,wm']; ring

theorem replacement182_right (q : OpenSquare) (ha : 1<q.side)
    (hx0 : 91/50≤centerX q) (hx1 : centerX q≤2)
    (hy0 : 1≤centerY q) (hy1 : centerY q≤2)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i) : q.Inside (91/50) 1 := by
  have fan := (lower_fan q ha (by linarith only [hx0]) hx1
    (by linarith only [hy0]) hy1 hout).2
  let wf := (50000/5119)*((13/20)*(centerX q-91/50)+(17/100)*(centerY q-1))
  let wm := (50000/5119)*((9/50)*(centerY q-1)+(43/500)*(centerX q-91/50))
  apply target182_right_triangle q ha hout wf wm
  · dsimp [wf]; linarith only [hx0,hy0]
  · dsimp [wm]; linarith only [hx0,hy0]
  · dsimp [wf,wm,rep0tri3w1] at fan ⊢; linarith only [fan]
  · dsimp [wf,wm]; ring
  · dsimp [wf,wm]; ring

private theorem target196_right_triangle (q : OpenSquare) (ha : 1<q.side)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i)
    (wF wM : ℝ) (f : 0≤wF) (m : 0≤wM) (t : 0≤1-wF-wM)
    (hx : (1-wF-wM)*(49/25)+wF*2+wM*(33/20)=centerX q)
    (hy : (1-wF-wM)*(19/25)+wF*(457/500)+wM*(33/20)=centerY q) :
    q.Inside (49/25) (19/25) := by
  have hit := triangle_nonavoidance q ha (49/25) (19/25) 2 (457/500) (33/20) (33/20)
    (1-wF-wM) wF wM t f m (by ring) hx hy
    (by norm_num) (by norm_num) (by norm_num)
  have noF : ¬q.Inside 2 (457/500) := by simpa [Owns,marker] using hout 13 (by decide)
  have noM : ¬q.Inside (33/20) (33/20) := by simpa [Owns,marker] using hout 8 (by decide)
  exact hit.resolve_right (fun h => h.elim noF noM)

theorem replacement196_left (q : OpenSquare) (ha : 1<q.side)
    (hx0 : 457/500≤centerX q) (hx1 : centerX q≤49/25)
    (hy0 : 1≤centerY q) (hy1 : centerY q≤2)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i) (missing : ¬q.Inside 1 1) :
    q.Inside (49/25) (19/25) := by
  obtain ⟨fanL,fanR⟩ := lower_fan q ha hx0 (by linarith only [hx1])
    (by linarith only [hy0]) hy1 hout
  have diagonal := below_diagonal q ha hy0 fanL hout missing
  let wt := (5/6)*(centerX q-centerY q)
  let wm := (20/13)*(centerY q-1+(6/25)*wt)
  by_cases wi : 0≤1-wt-wm
  · have tn : 0≤wt := by dsimp [wt]; linarith only [diagonal]
    have mn : 0≤wm := by dsimp [wm]; linarith only [hy0,tn]
    have hit := triangle_nonavoidance q ha (49/25) (19/25) (33/20) (33/20) 1 1
      wt wm (1-wt-wm) tn mn wi (by ring)
      (by dsimp [wm,wt]; ring) (by dsimp [wm,wt]; ring)
      (by norm_num) (by norm_num) (by norm_num)
    have noM : ¬q.Inside (33/20) (33/20) := by simpa [Owns,marker] using hout 8 (by decide)
    exact hit.resolve_right (fun h => h.elim noM missing)
  · let wf := (50000/4167)*((89/100)*(centerX q-49/25)+(31/100)*(centerY q-19/25))
    let wm' := (50000/4167)*((1/25)*(centerY q-19/25)-(77/500)*(centerX q-49/25))
    apply target196_right_triangle q ha hout wf wm'
    · dsimp [wf,wm,wt] at wi ⊢; linarith only [wi]
    · dsimp [wm']; linarith only [hx1,hy0]
    · dsimp [wf,wm',rep0tri3w1] at fanR ⊢; linarith only [fanR]
    · dsimp [wf,wm']; ring
    · dsimp [wf,wm']; ring

theorem replacement196_right (q : OpenSquare) (ha : 1<q.side)
    (hx0 : 49/25≤centerX q) (hx1 : centerX q≤2)
    (hy0 : 457/500≤centerY q) (hy1 : centerY q≤2)
    (hout : ∀ i : Marker,i≠0 → ¬Owns q i) : q.Inside (49/25) (19/25) := by
  have fan := (lower_fan q ha (by linarith only [hx0]) hx1 hy0 hy1 hout).2
  let wf := (50000/4167)*((89/100)*(centerX q-49/25)+(31/100)*(centerY q-19/25))
  let wm := (50000/4167)*((1/25)*(centerY q-19/25)-(77/500)*(centerX q-49/25))
  apply target196_right_triangle q ha hout wf wm
  · dsimp [wf]; linarith only [hx0,hy0]
  · dsimp [wm]; linarith only [hx1,hy0]
  · dsimp [wf,wm,rep0tri3w1] at fan ⊢; linarith only [fan]
  · dsimp [wf,wm]; ring
  · dsimp [wf,wm]; ring

#print axioms replacement196_left
end N12Compact.CommonCases.SingletonMissing
