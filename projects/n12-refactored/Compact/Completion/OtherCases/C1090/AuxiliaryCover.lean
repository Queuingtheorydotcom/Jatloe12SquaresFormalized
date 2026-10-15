import Compact.Completion.OtherCases.C1090.AuxiliaryCoverTransport

/-! Original C1090 auxiliary covers, proved from its actual family4098.
Only two existing direct single-cover certificates are reused, under exact
whole-set coordinate permutations and the narrower true 1..2 budget.
Extra owned points remain permitted. No C1092 family theorem is applied,
and no finite component list, entrance count or case exclusion is assumed.
Source-only; these declarations have not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1090.AuxiliaryCover
open S12 S12Pilot OriginalData
set_option Elab.async false
noncomputable section

theorem southwest_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 4).Inside 1 (87/50) ∨ (owners p 4).Inside (8/5) 1 ∨
    (owners p 4).Inside 2 (87/50) := by
  have h := central_cover ⟨true,false,false⟩ (by decide +kernel) 0 swapGF swapGF_points
    4 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem southwest_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 4).Inside 1 (8/5) ∨ (owners p 4).Inside (87/50) 1 ∨
    (owners p 4).Inside (87/50) 2 := by
  have h := central_cover ⟨false,false,false⟩ (by decide +kernel) 1 (Equiv.refl (Fin 10))
    (by intro j; fin_cases j <;> rfl) 4 (by decide +kernel) (by decide +kernel) p hf
  simpa [inside_pull,Transform.apply] using h

theorem southeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 2 (87/50) ∨ (owners p 5).Inside (12/5) 1 ∨
    (owners p 5).Inside 3 (87/50) := by
  have h := central_cover ⟨true,true,false⟩ (by decide +kernel) 0 swapXGF swapXGF_points
    5 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem southeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside (113/50) 1 ∨ (owners p 5).Inside (113/50) 2 ∨
    (owners p 5).Inside 3 (8/5) := by
  have h := central_cover ⟨false,true,false⟩ (by decide +kernel) 1
    RelaxedOwnerDomain.reflectXG RelaxedOwnerDomain.reflectXG_points
    5 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 2 (113/50) ∨ (owners p 6).Inside (12/5) 3 ∨
    (owners p 6).Inside 3 (113/50) := by
  have h := central_cover ⟨true,true,true⟩ (by decide +kernel) 0 swapXYGF swapXYGF_points
    6 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (113/50) 2 ∨ (owners p 6).Inside (113/50) 3 ∨
    (owners p 6).Inside 3 (12/5) := by
  have h := central_cover ⟨false,true,true⟩ (by decide +kernel) 1
    RelaxedOwnerDomain.halfTurnPerm RelaxedOwnerDomain.halfTurnG_points
    6 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northwest_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 1 (113/50) ∨ (owners p 7).Inside (8/5) 3 ∨
    (owners p 7).Inside 2 (113/50) := by
  have h := central_cover ⟨true,false,true⟩ (by decide +kernel) 0 swapYGF swapYGF_points
    7 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northwest_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 1 (12/5) ∨ (owners p 7).Inside (87/50) 2 ∨
    (owners p 7).Inside (87/50) 3 := by
  have h := central_cover ⟨false,false,true⟩ (by decide +kernel) 1 reflectYG reflectYG_points
    7 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem bottom_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (8/5) 1 ∨ (owners p 9).Inside 2 (87/50) ∨
    (owners p 9).Inside (12/5) 1 := by
  have h := wall_cover ⟨true,false,false⟩ (by decide +kernel) 0 swapGF swapGF_points
    9 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

/-- Additional literal wall covers reuse the same small certificate. -/
theorem top_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (8/5) 3 ∨ (owners p 11).Inside 2 (113/50) ∨
    (owners p 11).Inside (12/5) 3 := by
  have h := wall_cover ⟨true,false,true⟩ (by decide +kernel) 0 swapYGF swapYGF_points
    11 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem right_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 10).Inside (113/50) 2 ∨ (owners p 10).Inside 3 (8/5) ∨
    (owners p 10).Inside 3 (12/5) := by
  have h := wall_cover ⟨false,true,false⟩ (by decide +kernel) 1
    RelaxedOwnerDomain.reflectXG RelaxedOwnerDomain.reflectXG_points
    10 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

end
#print axioms southwest_f_cover
#print axioms northeast_f_cover
#print axioms northwest_g_cover
#print axioms bottom_f_cover
#print axioms top_f_cover
end N12Compact.Completion.OtherCases.C1090.AuxiliaryCover
