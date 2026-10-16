#!/usr/bin/env python3
"""Encode all initial roots without contexts, sharing the original pose rows.

Every arithmetic check and every branch remains explicit. This encoder does
not solve new geometry or trust an old decision oracle. Finite invariants are
checked before source is written; Lean independently replays each root.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import math,json,re,hashlib,resource,signal,time
signal.alarm(45)
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'Compact/Cases/C898/Initial'
SOURCE=ROOT/'evidence/C898/raw/data/region898.json'
start=time.monotonic()
owners=json.loads(SOURCE.read_text())
shared=json.loads((ROOT/'evidence/c898-shared-pose-map.json').read_text())
poses={p['name']:p for p in shared['poses']}
rows=[tuple(Q(x,r['denominator']) for x in r['integers'])+(r['strict'],) for r in shared['rows']]
raw_rows=[(*r['integers'],r['strict'],r['denominator']) for r in shared['rows']]
row_ids={r:i for i,r in enumerate(rows)}
assert len(row_ids)==len(rows)
shared_count=len(rows)
angles={int(i):[Q(x.strip().strip('()')) for x in fields.split(',')]
        for i,fields in re.findall(r'def angle64_(\d+) : AngleEnclosure := ⟨([^⟩]+)⟩',
          (ROOT/'vendor/S12/AngleData.lean').read_text())}
def canonical(raw):return tuple(Q(x) for x in raw[0])+(bool(raw[1]),)
def negate(r):return tuple(-x for x in r[:3])+(not r[3],)
def ids(xs):return '['+', '.join(map(str,xs))+']'
def rational(q):
 q=Q(q);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def points(ps):return '['+', '.join(f'({rational(x)}, {rational(y)})' for x,y in ps)+']'
def intern(row):
 if row not in row_ids:
  row_ids[row]=len(rows);rows.append(row)
  den=math.lcm(*(x.denominator for x in row[:3]))
  raw_rows.append(tuple(int(x*den) for x in row[:3])+(row[3],den))
 return row_ids[row]
def forms(c,s,side,point):
 x,y=map(Q,point)
 return [(-c,-s,side/2+c*x+s*y,True),(c,s,side/2-c*x-s*y,True),
         (s,-c,side/2-s*x+c*y,True),(-s,c,side/2+s*x-c*y,True)]
def geometry(owner,a):
 lo,hi,c,s,outer,inner,wall=angles[a]
 incoming=[r for p in owner['inside'] for r in forms(c,s,Q(1001,1000)*outer,p)]
 incoming += [(Q(1),Q(0),-wall/2,False),(Q(-1),Q(0),4-wall/2,False),
              (Q(0),Q(1),-wall/2,False),(Q(0),Q(-1),4-wall/2,False),(Q(0),Q(0),Q(1),True)]
 return incoming,[forms(c,s,inner,p) for p in owner['outside']]
def gather(tree):
 k=tree['kind']
 if k=='cut':
  r=canonical(tree['test']);intern(r);intern(negate(r));gather(tree['yes']);gather(tree['no'])
 elif k=='empty':
  for r,_ in tree['terms']:intern(canonical(r))
 elif k=='forbidden':
  for r in tree['block']:intern(canonical(r))
for a in range(64):
 for owner in owners:
  incoming,forbidden=geometry(owner,a)
  for r in incoming:intern(r)
  for block in forbidden:
   for r in block:intern(r)
  gather(owner['roots'][a])
total=len(rows);extra=total-shared_count
assert shared_count==26026 and total==40307 and extra==14281

# Preserve all existing shared IDs; store only genuinely new rational rows.
text=['import Compact.Core.RowSyntax','import Compact.Cases.C898.SharedPoses','import Compact.Core.RegionTraversal',
      'import Lean.Elab.Tactic.Omega','',
      'namespace N12Compact.C898Initial','open IntegerSupport RegionTraversal',
      'set_option maxRecDepth 100000','set_option Elab.async false','set_option linter.unnecessarySeqFocus false','set_option maxHeartbeats 0','',
      f'def initialRowCount : Nat := {total}',
      '/-- Exact extra rows paired with denominator minus one. -/',
      'noncomputable def extraRows : Array (Array (Row × Nat)) := row_text% "']
for j,(x,y,z,strict,den) in enumerate(raw_rows[shared_count:]):
 assert den > 0
 text+=[f'{x},{y},{z},{str(strict).lower()},{den-1}']
text+= ['"',f'noncomputable def extraDen (i : Fin {extra}) : Nat := Nat.succ ((RowSyntax.lookup extraRows i.val).2)',
        f'theorem extra_positive : ∀ i : Fin {extra}, 0 < extraDen i := by',
        '  intro i', '  exact Nat.zero_lt_succ _','',
        'def widenRow (i : Fin C898Shared.rowCount) : Fin initialRowCount :=',
        '  ⟨i.val, by have hi := i.isLt; change i.val < 26026 at hi; change i.val < 40307; omega⟩',
        'noncomputable def initialRows (i : Fin initialRowCount) : Row :=',
        '  if h : i.val < C898Shared.rowCount then C898Shared.rows ⟨i.val, h⟩',
        f'  else (RowSyntax.lookup extraRows (i.val - {shared_count})).1',
        'noncomputable def initialDen (i : Fin initialRowCount) : Nat :=',
        '  if h : i.val < C898Shared.rowCount then C898Shared.denominators ⟨i.val, h⟩',
        f'  else extraDen ⟨i.val - {shared_count}, by have hi := i.isLt; change i.val < {total} at hi; omega⟩',
        'theorem initial_positive (i : Fin initialRowCount) : 0 < initialDen i := by',
        '  unfold initialDen','  split_ifs',
        '  · exact C898Shared.positive_denominators _','  · exact extra_positive _','',
        'def sharedLeafRows (i : Fin C898Shared.poseCount) : List (Fin initialRowCount) :=',
        '  (C898Shared.poseRows i).map widenRow','',
        'end N12Compact.C898Initial','']
(OUT/'Rows.lean').write_text('\n'.join(text))

stats=Counter();root_stats=[];parts={}
for owner in owners:
 for part in range(4):
  parts[owner['owner'],part]=['import Compact.Cases.C898.Initial.Inputs',
      'import Compact.Cases.C898.Initial.Rows','',
      'namespace N12Compact.C898Initial',
      'open S12 IntegerSupport SparseInteger RegionDAG RegionTraversal RegionTraversalOwner',
      'set_option maxRecDepth 100000','set_option maxHeartbeats 0','']

for owner in owners:
 oi=owner['owner'];saved_indices=[]
 for a,tree in enumerate(owner['roots']):
  incoming,forbidden=geometry(owner,a)
  incoming_ids=[row_ids[r] for r in incoming]
  forbidden_ids=[[row_ids[r] for r in b] for b in forbidden]
  nodes=[];leaves=[];local_counts=Counter()
  def visit(t,context):
   k=t['kind'];local_counts[k]+=1;available=set(context)
   if k=='cut':
    row=canonical(t['test']);ri=row_ids[row];ci=row_ids[negate(row)]
    yes,yd=visit(t['yes'],[ri]+context);no,nd=visit(t['no'],[ci]+context)
    result=f'.cut {ri} {ci} {yes} {no}';depth=1+max(yd,nd)
   elif k=='forbidden':
    block=[canonical(r) for r in t['block']];bi=forbidden.index(block)
    assert set(forbidden_ids[bi])<=available
    local_counts['discarded_tautological_implications']+=len(t['proofs'])
    result=f'.forbidden {bi}';depth=1
   elif k=='leaf':
    old=t['index'];saved=owner['leaves'][old];pose=poses[f'leaf898_{oi}_{old}']
    assert saved['angle']==a==pose['angle']
    saved_rows=[row_ids[canonical(r)] for r in saved['inputs']]
    assert saved_rows==context==pose['rows']
    result=f'.leaf {len(leaves)}';leaves.append(pose['index']);saved_indices.append(old);depth=1
   elif k=='empty':
    terms=[(row_ids[canonical(r)],Q(w)) for r,w in t['terms']]
    assert all(i in available for i,_ in terms)
    weights=[w/raw_rows[i][4] for i,w in terms]
    lcm=math.lcm(*(w.denominator for w in weights));nums=[int(w*lcm) for w in weights]
    gcd=math.gcd(*nums);nums=[w//gcd for w in nums]
    assert min(nums)>=0 and any(w>0 and raw_rows[i][3] for w,(i,_) in zip(nums,terms))
    assert all(sum(w*raw_rows[i][j] for w,(i,_) in zip(nums,terms))==0 for j in range(3))
    result='.empty ⟨['+', '.join(f'({w}, {i})' for w,(i,_) in zip(nums,terms))+'], 1⟩';depth=1
    local_counts['weighted_terms']+=len(terms)
   else:raise AssertionError(k)
   index=len(nodes);nodes.append(result);return index,depth
  index,depth=visit(tree,incoming_ids);prefix=f'r{oi}_{a}'
  text=[f'/- Owner {oi}, angle {a}; context derived from cuts, depth {depth}. -/',
        f'def {prefix}_incoming : List (Fin initialRowCount) := {ids(incoming_ids)}',
        f'def {prefix}_nodes : Array (Kind initialRowCount) := #[',
        ',\n'.join('  '+n for n in nodes),']',
        f'def {prefix}_leafIds : Array (Fin C898Shared.poseCount) := #{ids(leaves)}',
        f'def {prefix}_forbidden : Array (List (Fin initialRowCount)) := #[',
        ',\n'.join('  '+ids(b) for b in forbidden_ids),']',
        f'def {prefix}_program : RegionTraversal.Program initialRowCount where',
        '  rows := initialRows','  denominators := initialDen',
        f'  nodes i := ({prefix}_nodes[i]?).getD (.leaf 0)',f'  nodeCount := {len(nodes)}',
        f'  leaves i := sharedLeafRows (({prefix}_leafIds[i]?).getD 0)',f'  leafCount := {len(leaves)}',
        f'  forbidden i := ({prefix}_forbidden[i]?).getD []',f'  forbiddenCount := {len(forbidden)}',
        f'def {prefix} : Root := ⟨initialRowCount, {prefix}_program, {index}, {prefix}_incoming, {depth},',
        f'  ⟨angle64_{a}, angle64_{a}_checked⟩⟩',
        f'theorem {prefix}_checked : {prefix}.Check inside{oi} outside{oi} := by',
        '  refine ⟨?_, initial_positive, ?_, ?_, ?_⟩','  all_goals decide +kernel','']
  parts[oi,a//16]+=text;stats.update(local_counts);stats['nodes']+=len(nodes);stats['roots']+=1
  root_stats.append({'owner':oi,'angle':a,'nodes':len(nodes),'depth':depth,'leaves':len(leaves)})
 assert saved_indices==list(range(len(owner['leaves'])))
for (oi,part),text in parts.items():
 text+=['end N12Compact.C898Initial',''];(OUT/f'Owner{oi:02d}Part{part}.lean').write_text('\n'.join(text))

# The public owner theorem/API stays unchanged while its root type is replaced.
p=OUT/'Inputs.lean';p.write_text(p.read_text().replace('Compact.Bridge.RegionOwner','Compact.Bridge.RegionTraversalOwner')
                              .replace('RegionDAG RegionOwner','RegionDAG RegionTraversalOwner'))
for owner in owners:
 p=OUT/f'Owner{owner["owner"]:02d}.lean';p.write_text(p.read_text().replace('open S12 RegionOwner','open S12 RegionTraversalOwner'))
# Only known obsolete generator-owned dictionaries are removed.
for part in range(4):(OUT/f'Shared{part}.lean').unlink()
assert stats['roots']==704 and stats['cut']==14088 and stats['empty']==10149
assert stats['forbidden']==3522 and stats['leaf']==1121
files=[p for p in OUT.glob('*.lean') if not p.name.startswith('Shared')]
report={'scope':'All704 initial roots, original11 owners and1121 exact shared leaves; traversal representation.',
 'validation':'Exact encoder checks; generated Lean awaiting serial replay.',
 'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
 'counts':dict(stats),'shared_rows_reused':shared_count,'extra_rows':extra,'logical_rows':total,
 'stored_context_records':0,'removed_context_records':41616,'removed_duplicate_rows':15243,
 'total_lean_lines':sum(p.read_text().count('\n') for p in files),
 'total_lean_bytes':sum(p.stat().st_size for p in files),'modules':len(files),
 'seconds':time.monotonic()-start,'max_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
 'roots':root_stats}
(ROOT/'evidence/c898-initial-traversal-conversion.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='roots'},indent=2))
