import Compact.Completion.OtherCases.C983.F4MergedCenterNegative
import Compact.Completion.OtherCases.C983.F4MergedCenterMonotone

/-! Assembly of the completed argument in `C983-F4-MERGED-CENTER.md`.
The only external manuscript entrance still required here is the strict
actual Q1 corner (1,1), proved in the cited LEFT-ORIGIN-AND-CORNER-ROOT
chapter through its local three-square theorem. No unconditional corner
ownership, full C983 ending, or whole-case theorem is asserted here.
All five new merged-center modules are source-only and uncompiled. -/
namespace N12Compact.Completion.OtherCases.C983.F4MergedCenter
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
set_option Elab.async false
noncomputable section

theorem Input.reframe_right {W K R : OpenSquare} (h : Input W K)
    (shape : R.side=K.side) (same : ∀ x y,R.Inside x y↔K.Inside x y) : Input W R := by
  exact ⟨h.sideLarge,h.sideSmall,h.sameSide.trans shape.symm,h.south,h.north,h.inner,h.west,
    (same _ _).mpr h.corner,(same _ _).mpr h.auxiliary,(same _ _).mpr h.seed,
    (same _ _).mpr h.marker,h.missingLeft,
    fun own => h.missingMarker ((same _ _).mp own),
    fun x y own => h.leftWall x y ((same x y).mp own),
    fun x y own => h.apart x y ⟨(same x y).mp own.1,own.2⟩⟩

theorem Input.reframe_left {W K R : OpenSquare} (h : Input W K)
    (shape : R.side=W.side) (same : ∀ x y,R.Inside x y↔W.Inside x y) : Input R K := by
  exact ⟨by simpa only [shape] using h.sideLarge,by simpa only [shape] using h.sideSmall,
    shape.trans h.sameSide,(same _ _).mpr h.south,(same _ _).mpr h.north,
    (same _ _).mpr h.inner,(same _ _).mpr h.west,h.corner,h.auxiliary,h.seed,h.marker,
    fun own => h.missingLeft ((same _ _).mp own),h.missingMarker,h.leftWall,
    fun x y own => h.apart x y ⟨own.1,(same x y).mp own.2⟩⟩

/-- The two allowed normals for a nonnegative canonical singleton,
and their reverses, are exactly those of manuscript §3. -/
theorem nonnegative_singleton_impossible (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c)
    (missing : ¬W.Inside 0 0) (bp : 0<K.c) (tn : 0≤K.s)
    (canonical : K.s≤K.c) : False := by
  obtain ⟨zl,zu,zrel,dc,rl,ru,sum,gap⟩ := angle_window W K h cp sn order missing
  have rp : 0<W.s := by linarith only [rl]
  have relation : (W.s/(1+W.c))*(1+W.c)=W.s :=
    div_mul_cancel₀ _ (by linarith only [cp])
  have scalars := positive_comparisons W.c W.s (W.s/(1+W.c)) cp rp order W.unit_normal
    zrel relation zl zu dc rl ru sum gap
  have reverse (nx ny : ℝ) (sep : upper W nx ny≤lower K nx ny) :
      upper K (-nx) (-ny)≤lower W (-nx) (-ny) := by
    rw [WallProfile.upper_neg,WallProfile.lower_neg]
    linarith only [sep]
  have noReverse (nx ny : ℝ) (unit : nx^2+ny^2=1) (xn : 0≤nx)
      (sep : upper W nx ny≤lower K nx ny) : False := by
    have cone := separator_cone W K h (-nx) (-ny)
      (by simpa only [neg_sq] using unit) (reverse nx ny sep)
    linarith only [cone.1,xn]
  have noV (q : OpenSquare) (qn : 0≤q.s) (qo : q.s≤q.c)
      (sep : upper K (-q.s) q.c≤lower W (-q.s) q.c ∨
        upper W (-q.s) q.c≤lower K (-q.s) q.c) : False := by
    rcases sep with forward | backward
    · have cone := separator_cone W K h (-q.s) q.c
        (by nlinarith only [q.unit_normal]) forward
      linarith only [cone.1,qn]
    · have cone := separator_cone W K h q.s (-q.c)
        (by nlinarith only [q.unit_normal]) (by simpa only [neg_neg] using reverse _ _ backward)
      linarith only [cone.2,qo]
  have axes := CongruentSAT.faceSeparation_of_disjoint K W h.sameSide.symm h.apart
  change pairRadius K W≤|K.c*(centerX W-centerX K)+K.s*(centerY W-centerY K)| ∨
    pairRadius K W≤|-K.s*(centerX W-centerX K)+K.c*(centerY W-centerY K)| ∨
    pairRadius W K≤|W.c*(centerX W-centerX K)+W.s*(centerY W-centerY K)| ∨
    pairRadius W K≤|-W.s*(centerX W-centerX K)+W.c*(centerY W-centerY K)| at axes
  have separate (nx ny radius : ℝ)
      (eq : supportRadius K nx ny+supportRadius W nx ny=radius)
      (axis : radius≤|nx*(centerX W-centerX K)+ny*(centerY W-centerY K)|) :=
    separated K W nx ny (by rwa [eq])
  rcases axes with ku | kv | wu | wv
  · rcases separate _ _ _ (parallel_radius K W) ku with forward | backward
    · exact singleton_positive_u W K h cp sn order missing bp tn canonical scalars forward
    · exact noReverse K.c K.s K.unit_normal bp.le backward
  · exact noV K tn canonical (separate _ _ _ (transverse_radius K W) kv)
  · have radius : supportRadius K W.c W.s+supportRadius W W.c W.s=pairRadius W K := by
      rw [add_comm]
      exact parallel_radius W K
    rcases separate _ _ _ radius wu with forward | backward
    · exact singleton_positive_w W K h cp sn order missing bp tn canonical scalars forward
    · exact noReverse W.c W.s W.unit_normal cp.le backward
  · have radius : supportRadius K (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W K := by
      rw [add_comm]
      exact transverse_radius W K
    exact noV W sn order (separate _ _ _ radius wv)

/-- The manuscript's new positive merged-angle sector, with the whole
actual singleton retained through both canonical signs. -/
theorem positive_sector (W K : OpenSquare) (h : Input W K)
    (cp : 0<W.c) (sn : 0≤W.s) (order : W.s≤W.c) : W.Inside 0 0 := by
  by_contra missing
  obtain ⟨R,bp,range,shape,same,_⟩ := ClosedFrames.canonical_frame K
  have actual := h.reframe_right shape same
  by_cases sign : 0≤R.s
  · exact nonnegative_singleton_impossible W R actual cp sn order missing bp sign
      ((abs_le.mp range).2)
  · exact nonpositive_singleton_impossible W R actual cp sn order missing (-R.s)
      (by ring) bp (by linarith only [sign])
      (by linarith only [(abs_le.mp range).1])

/-- The already existing nonpositive merged-sector theorem, with its
actual C983 prerequisites supplied independently of any F5 ownership. -/
theorem nonpositive_original (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (W : OpenSquare) (cp : 0<W.c) (sn : W.s≤0) (canonical : -W.s≤W.c)
    (shape : W.side=(owners p 7).side)
    (same : ∀ x y,W.Inside x y↔(owners p 7).Inside x y) : W.Inside 2 2 := by
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have leftLow : (owners p 1).Inside 1 (87/50) := by
    have h := seed_inside p hf 1 (1,87/50) (by decide +kernel)
    norm_num at h
    exact h
  have topMissing : ¬(owners p 7).Inside (8/5) 3 := by
    have h := missing_auxiliary p 7 3 (by decide +kernel) (merged_no_f3 p hf)
    simpa [auxPoints,fPoints,gPoints] using h
  have leftMarker : (owners p 8).Inside (457/500) 2 := by
    have h := seed_inside p hf 8 (457/500,2) (by decide +kernel)
    norm_num at h
    exact h
  exact MergedLeftNegative.point W (owners p 8)
    (by simpa only [shape] using owners_side p 7)
    (shape.trans (owners_same_side p 7 8)) (owners_contained p 8) cp sn canonical
    ((same _ _).mpr south) ((same _ _).mpr north)
    (fun own => owners_apart p hf 7 1 (by decide +kernel) _ _ ⟨(same _ _).mp own,leftLow⟩)
    (fun own => owners_apart p hf 7 8 (by decide +kernel) _ _ ⟨(same _ _).mp own,(left_aux p hf).1⟩)
    (fun own => topMissing ((same _ _).mp own)) leftMarker (left_aux p hf).2
    (fun x y own => owners_apart p hf 7 8 (by decide +kernel) x y ⟨(same x y).mp own.1,own.2⟩)

/-- The manuscript merged-center conclusion with its one still-unjoined
actual-owner prerequisite left explicit. This is not a whole-case ending. -/
theorem center_of_singleton_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) (corner : (owners p 1).Inside 1 1) :
    (owners p 7).Inside 2 2 := by
  obtain ⟨W,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame (owners p 7)
  apply (same 2 2).mp
  by_cases sign : 0≤W.s
  · have actual := actual_input p hf f4 corner
    have translated : ∀ x y,(W.translated 2 2).Inside x y↔
        ((owners p 7).translated 2 2).Inside x y := by
      intro x y
      rw [inside_translated_iff,inside_translated_iff]
      exact same (2+x) (2+y)
    have framed := actual.reframe_left (R := W.translated 2 2) shape translated
    have point := positive_sector (W.translated 2 2) ((owners p 1).translated 2 2)
      framed cp sign ((abs_le.mp range).2)
    norm_num only [inside_translated_iff] at point
    exact point
  · exact nonpositive_original p hf W cp (le_of_not_ge sign)
      (by linarith only [(abs_le.mp range).1]) shape same

end
#print axioms positive_sector
#print axioms center_of_singleton_corner
end N12Compact.Completion.OtherCases.C983.F4MergedCenter
