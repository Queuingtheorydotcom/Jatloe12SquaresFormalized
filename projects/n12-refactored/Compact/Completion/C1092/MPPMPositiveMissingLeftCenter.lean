import Compact.Completion.C1092.MPPMActualBoundaryOrigin
import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopes
import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf
import Compact.Completion.C1092.MPPMMissingNegativeCentersActual

/-! The full-angle scalar and literal actual left-center consequence of
POSITIVE-MISSING-LEFT-CENTER. The actual envelope is proved upstream;
the strict left origin is retained explicitly here, as supplied by a
nonpositive predecessor in the signed-edge application. Source only. -/
namespace N12Compact.C1092MPPMPositiveMissingLeftCenter
open S12 S12Pilot C977CornerCubic C1092ShallowCentralScalars C1092ShallowPositiveScalars
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
set_option Elab.async false
noncomputable section

theorem scalar_positive {c s : ℝ} (cn : Normal c s) :
    0<3/2-(6/5)*c-(36/25)*s+s*(c+s)/2 := by
  let q := C1092MPPMCrosspointSupport.half c s
  have hd := C1092MPPMCrosspointSupport.normal_half cn
  have rb := C1092MPPMCrosspointSupport.rho_bounds
  have qn : 0≤q := hd.1
  have qu : q≤5/12 := le_trans hd.2.1 rb.2.1.le
  have cosine : cosH q=c := hd.2.2.2.1
  have sine : sinH q=s := hd.2.2.2.2
  have identity : 50*(1+q^2)^2*(3/2-(6/5)*c-(36/25)*s+s*(c+s)/2)=
      135*q^4-194*q^3+250*q^2-94*q+15 := by
    rw [←cosine,←sine]
    dsimp [cosH,sinH]
    field_simp [(half_den_pos q).ne']
    <;> ring
  have cubic := mul_nonneg (sq_nonneg q) (show 0≤5/12-q by linarith only [qu])
  have square := sq_nonneg (q-282/1015)
  have fourth := pow_nonneg qn 4
  have positive : 0<135*q^4-194*q^3+250*q^2-94*q+15 := by
    nlinarith only [cubic,square,fourth]
  rw [←identity] at positive
  exact pos_of_mul_pos_right positive (by positivity)

/-- The same transverse face occurs in the geometric envelope and its
strict lower bound. Actual side>1 supplies a positive extra reserve. -/
theorem center_threshold (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (lowerV : (14/25)*C.s-C.c≤C.loV)
    (Y : ℝ) (envelope : ell C.side C.c C.s (C.loV+C.side)≤Y) : 1/5<Y := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have sum : 0≤C.c+C.s := by linarith only [cp,cn.1]
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<3/2+C.s*(C.c+C.s)/2 by positivity)
  have scalar := scalar_positive cn
  have weighted := mul_le_mul_of_nonneg_left envelope cp.le
  have coordinate : C.c*ell C.side C.c C.s (C.loV+C.side)=
      (C.loV+C.side)-2*C.s+(C.side/2)*(1+C.s*(C.c+C.s)) := by
    dsimp [ell]
    field_simp [cp.ne']
  have margin : 0<C.c*(Y-1/5) := by
    nlinarith only [weighted,coordinate,strict,scalar,lowerV]
  exact sub_pos.mp (pos_of_mul_pos_right margin cp.le)

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem actual_left_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (leftOrigin : (owners p 8).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    11/5<centerY (owners p 8) := by
  let L := (owners p 8).translated 2 2
  have actual (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 8) 2 2 x y
  have side : 1<C.side := by
    rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have cap : C.side≤1001/1000 := by
    rw [frame.side]
    change (p.square _).side≤1001/1000
    rw [p.congruent]
    exact p.side_le
  have same : C.side=L.side :=
    frame.side.trans ((p.congruent _).trans (p.congruent _).symm)
  have data := missing_data p hf hb h missing leftOrigin C frame cn
  have profile := C1092MPPMMissingPositiveBoundaries.profile C side data
  have envelope := C1092MPPMMissingPositiveBoundaries.left_order C L side cap same data
    (by
      apply (actual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 8 12 (by decide +kernel))
    (by apply (actual _ _).mpr; norm_num; exact leftOrigin)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((actual _ _).mp own)).1
      linarith only [wall])
    (fun x y both => owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(actual _ _).mp both.2⟩)
  have threshold := center_threshold C side cn profile.lowerV (centerY L) envelope
  have translated : centerY L=centerY (owners p 8)-2 := center_translate_y _ _ _
  rw [translated] at threshold
  linarith only [threshold]

/-- A nonpositive missing owner cannot precede a positive missing
owner. The two strict comparisons use the same original Q9 center,
and its one needed origin is derived from the predecessor's omission. -/
theorem negative_missing_successor_missing_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (D : OpenSquare) (nextFrame : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s)
    (missingC : ¬(owners p 4).Inside (87/50) 2)
    (missingD : ¬(owners p 5).Inside 2 (87/50)) : False := by
  have first := C1092MPPMMissingNegativeCenters.actual_bottom_order
    p hf hb h missingC C frame cn
  let g := rotation 1
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 1
  have ordinary := Ordinary.rotated p hf h 1
  have missing' : ¬(owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact missingD
  have originalOrigin : (owners p 9).Inside 2 1 :=
    bottom_origin_of_missing p hf hb
      (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
      h.southwest.1 h.southwest.2 missingC
  have origin' : (owners (g.pullPacking p) 8).Inside 1 2 := by
    rw [owners_transport g p hf 8]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact originalOrigin
  have last := actual_left_center (g.pullPacking p) family' context ordinary
    missing' origin' D nextFrame dn
  rw [owners_transport g p hf 8] at last
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    center_pullSwap_x,center_pullSwap_y,center_pullX_x,center_pullX_y] at last
  linarith only [first,last]

end
#print axioms scalar_positive
#print axioms actual_left_center
#print axioms negative_missing_successor_missing_impossible
end N12Compact.C1092MPPMPositiveMissingLeftCenter
