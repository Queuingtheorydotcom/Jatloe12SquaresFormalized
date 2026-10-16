#!/usr/bin/env python3
"""Propose small literal covers for the unchanged C981 ownership domains.

Only integer finite-set source data is read. Proposed tables are untrusted:
ordinary Lean proofs must check every domain equality and every compatible
prefix extension. No saved count, Python success flag or native axiom proves
coverage. The bounded proposal has at most one million candidate extensions.
"""
import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def sets(text):
    return [frozenset(map(int, re.findall(r'\d+', s)))
        for s in re.findall(r'\{[\d, ]*\}|∅', text)]

def first_list(text, name):
    match = re.search(r'^def '+re.escape(name)+r'\b[^\n]*?\[(.*?)\]', text, re.M)
    if not match:
        raise ValueError('No literal list for '+name)
    return sets(match.group(1))

def show_set(s):
    return '{'+','.join(map(str, sorted(s)))+'}' if s else '∅'

def show_sets(xs):
    return '['+','.join(show_set(x) for x in xs)+']'

def show_vectors(xs):
    return '[\n'+',\n'.join('  '+show_sets(x) for x in xs)+'\n]'

def step_proof(index, owner):
    """Lean checks one exact extension-table equality, avoiding repeated search."""
    old, new = f"prefix{index-1:02}", f"prefix{index:02}"
    return (f"theorem step{index:02} : StepCheck {old} allowed{owner} {new} := by\n"
            "  apply stepCheck_of_extensions_eq\n  rfl\n")

def propose(limit):
    specs = (ROOT/'source/S12/DomainSpecData.lean').read_text()
    subset = (ROOT/'Compact/Bridge/C981DomainReuse/Subset.lean').read_text()
    query_source = '\n'.join(p.read_text() for p in sorted(
        (ROOT/'Compact/Bridge/C981DomainReuse').glob('Queries*.lean')))
    queries = {int(n): frozenset(map(int, re.findall(r'\d+', owned)))
        for n, owned in re.findall(
            r'checked_local_query query976_(\d+)\s*:=\s*⟨\d+,2,(\{[\d, ]*\}|∅)', query_source)}
    def product(owner, excluded):
        first = first_list(subset, f'single976_{owner}_0')
        second = first_list(subset, f'single976_{owner}_1')
        removed = {queries[n] for n in excluded}
        return [a | {j+10 for j in b} for a in first for b in second
            if a | {j+10 for j in b} not in removed]
    domains = [first_list(specs, 'combinedSpec1'),first_list(specs, 'combinedSpec3'),
        product(2,range(230,233)),product(3,range(249,252)),product(4,range(268,271)),
        first_list(specs, 'combinedSpec8'),product(7,range(649,706))]
    domains += [first_list(specs,f'combinedSpec{i}') for i in (13,17,19,21,24)]
    prefixes, attempts = [[[]]], 0
    order = [0,1,8,9,10,11,2,3,4,5,6,7]
    for index in order:
        domain = domains[index]
        result = []
        for row in prefixes[-1]:
            used = frozenset().union(*row)
            attempts += len(domain)
            if attempts > limit:
                raise RuntimeError('Candidate-extension budget exhausted')
            result += [row+[choice] for choice in domain if not choice & used]
        if len(result)>10000:
            raise RuntimeError('Prefix-row budget exhausted')
        prefixes.append(result)
    vector_source = (ROOT/'Completion/Cases/C981/VectorData.lean').read_text()
    vector_data = vector_source.split('def representativeVectors',1)[1].split('\n\n',1)[0]
    representatives = [sets(line) for line in vector_data.splitlines()
        if line.strip().startswith('[{') or line.strip().startswith('[∅')]
    if len(representatives)!=117 or any(len(v)!=12 for v in representatives):
        raise ValueError('Unexpected representative catalogue shape')
    auxiliary_source = (ROOT/'Completion/Cases/C981/DiagonalAuxiliary.lean').read_text()
    def permutation(name):
        match = re.search(r'def '+name+r'\b.*?\!\[([\d,]+)\]',auxiliary_source,re.S)
        return list(map(int,match.group(1).split(',')))
    aux, owners = permutation('auxiliaryTranspose'),permutation('ownerTranspose')
    covered = []
    for vector in representatives:
        covered += [vector,[frozenset(j for j in range(20) if aux[j] in vector[owners[i]])
            for i in range(12)]]
    original_order = lambda v: v[:2]+v[6:]+v[2:6]
    missing = [v for v in prefixes[-1] if original_order(v) not in covered]
    if missing:
        raise ValueError(f'Uncovered authentic assignments: {len(missing)}')
    return domains,prefixes,covered,attempts

def write(domains,prefixes,covered):
    dest=ROOT/'Completion/Cases/C981/Coverage'
    dest.mkdir(parents=True,exist_ok=True)
    preamble='\nnamespace S12Completion.C981.Coverage\nopen S12 N12Compact.PrefixCoverage\n'+\
        'set_option Elab.async false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n'
    data='import Completion.Cases.C981.OwnershipDomains\nimport Compact.Bridge.CoverageReorder\n'+preamble
    for i,domain in enumerate(domains):
        data+=f'\ndef allowed{i} : List (Finset Nat) := {show_sets(domain)}\n'+\
            f'theorem allowed{i}_exact : domain{i}.allowed = allowed{i} := by decide +kernel\n'
    data+='\ndef literalChoices : List (List (Finset Nat)) :=\n  ['+\
        ','.join(f'allowed{i}' for i in range(12))+']\n'
    data+='theorem allowed_exact : domains.map (fun d => d.allowed) = literalChoices := by\n'+\
        '  simp only [domains,List.map_cons,List.map_nil,'+\
        ','.join(f'allowed{i}_exact' for i in range(12))+']\n  rfl\n'
    order = [0,1,8,9,10,11,2,3,4,5,6,7]
    data+='\ndef reorderedChoices : List (List (Finset Nat)) :=\n  ['+\
        ','.join(f'allowed{i}' for i in order)+']\n'
    data+='theorem reordered_exact : reorder literalChoices = reorderedChoices := rfl\n'
    data+='end S12Completion.C981.Coverage\n'
    (dest/'AllowedData.lean').write_text(data)
    for i,rows in enumerate(prefixes):
        previous='AllowedData' if i==0 else f'Prefix{i-1:02}'
        source=f'import Completion.Cases.C981.Coverage.{previous}\n'+preamble+\
            f'\ndef prefix{i:02} : List (List (Finset Nat)) := {show_vectors(rows)}\n'
        if i:
            source += step_proof(i, order[i-1])
        source+='end S12Completion.C981.Coverage\n'
        (dest/f'Prefix{i:02}.lean').write_text(source)
    case_path=ROOT/'Completion/Cases/C981/CaseVectors.lean'
    original=case_path.read_text()
    end=original.index('/-- Kernel finite enumeration')
    transpose_path=ROOT/'Completion/Cases/C981/TransposeData.lean'
    if '/-- The exact inverse image' in original:
        start=original.index('/-- The exact inverse image')
        transpose='import Completion.Cases.C981.VectorData\nimport Completion.Cases.C981.DiagonalAuxiliary\n'+\
            '\nnamespace S12Completion.C981\nopen S12 S12Pilot\n'+original[start:end]+\
            'end S12Completion.C981\n'
        transpose_path.write_text(transpose)
    elif not transpose_path.exists():
        raise ValueError('The factored transpose source is missing')
    final='import Completion.Cases.C981.Coverage.Prefix12\n'+\
        'import Completion.Cases.C981.TransposeData\n'+preamble+\
        '\ndef literalCovered : List (List (Finset Nat)) := '+show_vectors(covered)+'\n'+\
        'theorem covered_exact : coveredVectors = literalCovered := by decide +kernel\n'+\
        'theorem final_covered : ∀ a ∈ prefix12, unorder a ∈ literalCovered := by decide +kernel\n'+\
        'theorem complete_chain : Chain [[]] reorderedChoices prefix12 :=\n  '
    final+=''.join(f'.cons step{i:02} (' for i in range(1,13))+'.nil prefix12'+')'*12+'\n'
    final+='end S12Completion.C981.Coverage\n'
    (dest/'Final.lean').write_text(final)
    oldproof='theorem complete_vector_coverage : DomainCasesCheck domains coveredVectors := by\n  decide'
    newproof='theorem complete_vector_coverage : DomainCasesCheck domains coveredVectors := by\n'+\
        '  unfold DomainCasesCheck\n  rw [Coverage.allowed_exact,Coverage.covered_exact]\n'+\
        '  intro a ha\n  have valid := N12Compact.PrefixCoverage.enumerate_valid _ _ _ ha\n'+\
        '  have allowed := N12Compact.PrefixCoverage.reorder_allowed valid.1\n'+\
        '  rw [Coverage.reordered_exact] at allowed\n'+\
        '  have final := Coverage.complete_chain.sound [] (N12Compact.PrefixCoverage.reorder a)\n'+\
        '    (by simp) allowed (N12Compact.PrefixCoverage.reorder_pairwise a valid.2.1) (by simp)\n'+\
        '  have covered := Coverage.final_covered _ (by simpa only [List.nil_append] using final)\n'+\
        '  have length : a.length = 12 := valid.1.length_eq\n'+\
        '  simpa only [N12Compact.PrefixCoverage.unorder_reorder a length] using covered'
    body=original[end:]
    if oldproof in body:
        body=body.replace(oldproof,newproof,1)
    elif newproof not in body:
        raise ValueError('Coverage proof changed; refusing an adaptive overwrite')
    case_path.write_text('import Completion.Cases.C981.Coverage.Final\n\n'+\
        'namespace S12Completion.C981\nopen S12 S12Pilot\n\n'+body)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--candidate-limit',type=int,default=1000000)
    args=parser.parse_args()
    domains,prefixes,covered,attempts=propose(args.candidate_limit)
    report={'domain_sizes':list(map(len,domains)),
        'prefix_sizes':list(map(len,prefixes)),'candidate_extensions':attempts,
        'complete_assignments':len(prefixes[-1]),'covered_vectors':len(covered),
        'lean_tables_verified':False,'global_optimality_proved':False}
    print(json.dumps(report))
    if args.write:
        write(domains,prefixes,covered)
        (ROOT/'.verification/c981-prefix-proposal.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
