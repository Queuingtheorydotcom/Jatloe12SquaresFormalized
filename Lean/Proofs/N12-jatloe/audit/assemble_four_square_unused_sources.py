"""Emit only small concrete adapters; no certificate search or Lean invocation."""
import json
import re
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from provenance_source import read_text
ROOT=Path(__file__).resolve().parents[1]
CASES=[841,842]
source=(ROOT/'source/S12/DomainSpecData.lean').read_text()
singles={}
for no,mask,kind,lo,hi,allowed in re.findall(r'def singleSpec(\d+) : SingleSpec := ⟨(\d+),(\d+),(\d+),(\d+),\[([^\]]*)\]',source):
 if lo==hi=='1':
  singles[int(mask),int(kind)]=(int(no),len(re.findall(r'\{([^}]*)\}',allowed)))
combined={}
for no,mask,a,b,allowed in re.findall(r'def combinedSpec(\d+) : CombinedSpec := ⟨(\d+),⟨singleSpec(\d+),[^⟩]+⟩,⟨singleSpec(\d+),[^⟩]+⟩,\[([^\]]*)\]',source):
 if all(any(v[0]==int(x) for v in singles.values()) for x in [a,b]):
  combined[int(mask)]=(int(no),len(re.findall(r'\{([^}]*)\}',allowed)))
check='(by decide +kernel)'

def finset(value):
 return '{'+','.join(str(i) for i in range(20) if value>>i&1)+'}'

def normal_half(case,mask,k):
 if mask==32784 and k==0:
  return f'''HalfDomain.ofSeedHull family{case} 32784 0 7 {check}
    {check} {check} ⟨(9/4,3),(11/4,3),(9/4,3),(12/5,3),3/10,0⟩ {check}
    {check} {check} {check} {check}''',1
 if (mask,k) in singles:
  no,n=singles[mask,k]
  return f'HalfDomain.ofSpec family{case} singleSpec{no} {k} singleSpec{no}_checked {check}',n
 return f'HalfDomain.singleton family{case} {mask} {k} {check} {check}',10

outdir=ROOT/'Compact/Cases/FourSquareUnused'
outdir.mkdir(parents=True,exist_ok=True)
for case in CASES:
 record=json.loads(read_text(ROOT/f'evidence/historical/data/case{case}-input.json'))
 masks=[sum(1<<i for i in g) for g in record['row']['groups']]
 promoted=case in [992,1001]
 special=4288 if case==992 else 32816
 text=['import Compact.Bridge.FourSquareConvexCase','import Compact.Bridge.OwnerBudget','import S12.DomainSpecData','',
       f'/-! Original marker case {case}, with exact auxiliary domains and convex point witnesses. -/',
       'namespace N12Compact.FourSquareUnusedCases','open S12 OwnerBudget FourSquareConvexCase','noncomputable section',
       'set_option maxRecDepth 10000','set_option maxHeartbeats 0','',
       f'def family{case} : Finset Nat := '+'{'+','.join(map(str,masks))+'}','']
 if promoted:
  if case==992:
   witnesses=['⟨(1,9/4),(1,11/4),(1,9/4),(1,113/50),1/50,0⟩',
              '⟨(1,9/4),(1,11/4),(1,9/4),(1,12/5),3/10,0⟩']
   ix=1
  else:
   witnesses=['⟨(9/4,3),(11/4,3),(9/4,3),(12/5,3),3/10,0⟩',
              '⟨(9/4,3),(11/4,3),(9/4,3),(113/50,3),1/50,0⟩']
   ix=7
  text += [f'def promotion{case} : Promotion family{case} :=',
      f'  ⟨{special}, {check}, (by intro k; fin_cases k <;> decide +kernel),',
       '    (by intro k; fin_cases k <;> decide +kernel),',
      f'    (fun _ => {ix}), !['+','.join(witnesses)+'],',
       '    (by intro k; fin_cases k <;> decide +kernel)⟩','']
 domains=[]
 for mask in masks:
  if mask in [12,48,192]: continue
  name=f'domain{case}_{mask}'
  if promoted and mask==special:
   body=f'OwnerBudget.product family{case} {mask} (promotion{case}.ownDomain 0) (promotion{case}.ownDomain 1)'
   n=1
  elif mask==520:
   body=f'CornerPairDomain.domain520 family{case} {check} {check}'; n=11
  elif mask==33792:
   body=f'UpperMidDomain.domain33792 family{case} {check} {check}'; n=6
  elif mask in combined:
   no,n=combined[mask]
   if promoted:
    body=f'promotion{case}.combined combinedSpec{no} combinedSpec{no}_checked\n    (by rfl) (by rfl) (by rfl) (by rfl) {check} {check}'
   else:
    body=f'CertifiedDomain.ofCombined family{case} combinedSpec{no} combinedSpec{no}_checked {check}'
  else:
   halves=[];n=1
   for k in [0,1]:
    if promoted:
     if (mask,k) in singles:
      no,nn=singles[mask,k]
      h=f'promotion{case}.ofSpec singleSpec{no} {k} singleSpec{no}_checked (by rfl) (by rfl) (by rfl) {check}'
     else: h=f'promotion{case}.singleton {mask} {k} {check}';nn=10
    else: h,nn=normal_half(case,mask,k)
    halves.append(h);n*=nn
   body=f'OwnerBudget.product family{case} {mask}\n    ('+halves[0]+')\n    ('+halves[1]+')'
  domains.append((n,mask))
  text += [f'def {name} : CertifiedDomain family{case} :=','  '+body,'']
 domains.sort()
 text += [f'def domains{case} : List (CertifiedDomain family{case}) :=',
          '  ['+','.join(f'domain{case}_{mask}' for n,mask in domains)+']','',
          f'theorem domains{case}_members : ∀ d ∈ domains{case}, d.mask ∈ family{case} := by decide +kernel',
          f'theorem domains{case}_distinct : domains{case}.Pairwise (fun a b => a.mask ≠ b.mask) := by decide +kernel','']
 owners=([7,8,9,11,6] if case in [841,842] else [6,5,9,11,7] if case==995 else [6,7,8,10,5])
 targets=[record['domains'][i][0] for i in owners]
 selected=[masks[i] for i in owners]
 transform='⟨true,false,false⟩' if case==995 else '⟨false,false,false⟩'
 left=1 if case==995 else 2
 hulls=['[]']*5
 if case == 842:hulls[3]='[⟨(3,9/4),(3,11/4),(3,9/4),(3,12/5),3/10,0⟩]'
 if case==992:hulls[2]='[⟨(1,9/4),(1,1543/500),(1,9/4),(1,12/5),75/418,0⟩]'
 text += [f'def data{case} : FourSquareConvexCase.Data :=',
          f'  ⟨{transform}, !['+','.join(map(str,selected))+'],',
          '    !['+','.join(finset(v) for v in targets)+f'], {left},',
          '    !['+','.join(hulls)+']⟩','',
          f'theorem data{case}_checked : data{case}.Check family{case} := by decide +kernel','',
          f'theorem forced{case} (p : NormalizedPacking) (hf : codedMarkerFamily p = family{case}) :',
          f'    ∀ i, natCombinedOwners p (ownerIndex p (data{case}.masks i)) = data{case}.owned i := by',
          '  intro i','  fin_cases i']
 for mask,target in zip(selected,targets):
  text += [f'  · exact certified_domain_forced domains{case} domains{case}_members domains{case}_distinct',
           f'      {mask} {finset(target)} {check} p hf']
 text += ['',f'theorem case{case}_impossible (p : NormalizedPacking)',
          f'    (hf : codedMarkerFamily p = family{case}) : False :=',
          f'  FourSquareConvexCase.impossible data{case} family{case} data{case}_checked forced{case} p hf','',
          f'#print axioms case{case}_impossible','end','end N12Compact.FourSquareUnusedCases','']
 (outdir/f'Case{case}.lean').write_text('\n'.join(text))
(ROOT/'Compact/Cases/FourSquareUnused.lean').write_text('\n'.join(f'import Compact.Cases.FourSquareUnused.Case{case}' for case in CASES)+'\n')
text=['import Compact.Cases.FourSquareUnused','import Completion.Contracts','',
      '/-! Original whole-case obligations, with exact convex entrance proofs. -/',
      'namespace N12Compact.FourSquareUnusedCases','open S12 S12Completion',
      'set_option maxRecDepth 10000','set_option maxHeartbeats 0','',
      'def coveredIds : Finset Nat := {'+','.join(map(str,CASES))+'}','',
      'def coveredFamilies : List (Nat × Finset Nat) :=',
      '  ['+','.join(f'({case},family{case})' for case in CASES)+']','',
      'theorem covered_families_excluded : ∀ entry ∈ coveredFamilies, ExcludesFamily entry.2 := by',
      '  intro entry h','  simp only [coveredFamilies, List.mem_cons, List.not_mem_nil, or_false] at h',
      '  rcases h with '+' | '.join('rfl' for _ in CASES)]
text += [f'  · exact case{case}_impossible' for case in CASES]
text += ['', 'theorem covered_rows_checked : ∀ r ∈ retainedRows, r.originalId ∈ coveredIds →',
         '    (r.originalId, r.groups) ∈ coveredFamilies := by decide +kernel','',
         'theorem covered_cases_excluded (id : Nat) (hid : id ∈ coveredIds) : ExcludesCase id := by',
         '  intro r hr he','  exact covered_families_excluded (r.originalId, r.groups)',
         '    (covered_rows_checked r hr (by simpa only [he] using hid))','',
         '#print axioms covered_cases_excluded','end N12Compact.FourSquareUnusedCases','']
(ROOT/'Compact/Assembly/FourSquareUnusedCases.lean').write_text('\n'.join(text))
