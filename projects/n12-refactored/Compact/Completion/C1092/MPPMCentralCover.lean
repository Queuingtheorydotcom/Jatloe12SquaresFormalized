import Compact.Completion.C1092.MPPMOmissions

/-! The exhaustive actual southwest central cover in the zero-omission
MPPM entrance. Ordinary and inward pairs may overlap; the residual elbow
retains both genuine omissions. No combined ownership tuple is assumed. -/
namespace N12Compact.C1092MPPMCentralCover
open S12 S12Pilot C1092WallCycle C1092AuxiliaryCover C1092WallSymmetry
open C1092MPPMEntrance C1092MPPMOmissions
set_option Elab.async false

def Ordinary (q : OpenSquare) : Prop := q.Inside 1 (87/50) ∧ q.Inside 1 (8/5)
def Inward (q : OpenSquare) : Prop := q.Inside 2 (87/50) ∧ q.Inside (87/50) 2
def Elbow (q : OpenSquare) : Prop :=
  q.Inside 1 (87/50) ∧ q.Inside (87/50) 2 ∧
    ¬q.Inside 1 (8/5) ∧ ¬q.Inside 2 (87/50)

theorem cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (bottomG : (owners p 9).Inside (87/50) 1) :
    Ordinary (owners p 4) ∨ Inward (owners p 4) ∨ Elbow (owners p 4) := by
  classical
  have f : (owners p 4).Inside 1 (87/50) ∨ (owners p 4).Inside 2 (87/50) := by
    have h := central_cover_transported ⟨true,false,false⟩ p hf
    norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
    rcases h with foreign | ordinary | inward
    · exact (owners_disjoint p hf 4 9 (by decide) _ _ ⟨foreign,bottomF⟩).elim
    · exact Or.inl ordinary
    · exact Or.inr inward
  have g : (owners p 4).Inside 1 (8/5) ∨ (owners p 4).Inside (87/50) 2 := by
    rcases southwest_g_cover p hf with ordinary | foreign | inward
    · exact Or.inl ordinary
    · exact (owners_disjoint p hf 4 9 (by decide) _ _ ⟨foreign,bottomG⟩).elim
    · exact Or.inr inward
  by_cases ordinaryF : (owners p 4).Inside 1 (87/50)
  · by_cases ordinaryG : (owners p 4).Inside 1 (8/5)
    · exact Or.inl ⟨ordinaryF,ordinaryG⟩
    · have inwardG := g.resolve_left ordinaryG
      by_cases inwardF : (owners p 4).Inside 2 (87/50)
      · exact Or.inr (Or.inl ⟨inwardF,inwardG⟩)
      · exact Or.inr (Or.inr ⟨ordinaryF,inwardG,ordinaryG,inwardF⟩)
  · have inwardF := f.resolve_left ordinaryF
    by_cases inwardG : (owners p 4).Inside (87/50) 2
    · exact Or.inr (Or.inl ⟨inwardF,inwardG⟩)
    · have ordinaryG := g.resolve_right inwardG
      have side : 1<(owners p 4).side := by
        change 1<(p.square _).side
        rw [p.congruent]
        exact p.side_gt_one
      apply False.elim
      apply C1092MixedSpan.impossible (pullX (owners p 4)) side
      · norm_num [inside_pullX]; exact inwardF
      · norm_num [inside_pullX]; exact ordinaryG
      · norm_num [inside_pullX]; exact inwardG
      · norm_num [inside_pullX]; exact ordinaryF
      · norm_num [inside_pullX]
        exact fun h => owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,bottomG⟩
      · norm_num [inside_pullX]
        exact fun h => owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,bottomF⟩

theorem no_omission_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (empty : ∀ k, ¬Missing p k) :
    Ordinary (owners p 4) ∨ Inward (owners p 4) ∨ Elbow (owners p 4) := by
  have wall := (ordinary_walls p hb empty).2.1
  exact cover p hf wall.1 wall.2

#print axioms cover
end N12Compact.C1092MPPMCentralCover
