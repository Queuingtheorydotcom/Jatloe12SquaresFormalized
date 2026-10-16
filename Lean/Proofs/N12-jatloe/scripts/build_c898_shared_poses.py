#!/usr/bin/env python3
"""Translate authenticated explicit pose data, preserving row order and values."""
from provenance_source import read_bytes, read_text, text_stream
from pathlib import Path
from fractions import Fraction
import hashlib,json,math,re

ROOT=Path(__file__).resolve().parents[1]
decl=re.compile(r'^(?:noncomputable )?(?:def|theorem) ([A-Za-z0-9_]+)',re.M)
poses=[];blocks=[];row_entries=[];row_lookup={};provenance=[]

def add_row(fields):
    values=[Fraction(x.replace('(','').replace(')','')) for x in fields[:3]]
    strict=fields[3] in ['true','1']
    key=(*values,strict)
    if key not in row_lookup:
        den=math.lcm(*(x.denominator for x in values))
        integers=[int(x*den) for x in values]
        index=len(row_entries);row_lookup[key]=index
        row_entries.append({'integers':integers,'strict':strict,'denominator':den})
    return row_lookup[key]

for number in range(66):
    path=ROOT/f'vendor/S12/Push898Chunk{number}.lean';raw=read_bytes(path);text=raw.decode()
    provenance.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(raw).hexdigest()})
    matches=list(decl.finditer(text))
    for j,m in enumerate(matches):
        name=m[1];end=matches[j+1].start() if j+1<len(matches) else len(text);d=text[m.start():end]
        if re.search(r' : PoseLeaf :=',d[:200]):
            shape=re.search(r'⟨⟨angle64_(\d+),angle64_\d+_checked⟩,regionConstraintsFromText "([^"\n]*)"',d)
            assert shape,name
            rows=[add_row(row.split(',')) for row in shape[2].split(';')] if shape[2] else []
            poses.append({'name':name,'index':len(poses),'angle':int(shape[1]),'rows':rows})
        if re.fullmatch(r'continuousScout898Step\d+Pose\d+BlockRows',name):
            expr=d.split('\n')[0].split(':=',1)[1].strip()
            if expr.startswith('['):
                fields=re.findall(r'⟨⟨!\[([^,\]]+),([^\]]+)\],([^⟩]+)⟩,(true|false)⟩',expr)
                assert len(fields)==expr.count('⟨⟨!['),(name,expr)
                blocks.append({'name':name,'index':len(blocks),'rows':[add_row(f) for f in fields]})
assert len(poses)==3317
assert len({p['name'] for p in poses})==len(poses)
outdir=ROOT/'Compact/Cases/C898';outdir.mkdir(parents=True,exist_ok=True)
rowsfile=outdir/'SharedRows.lean'
lines=['import Compact.Core.RowSyntax','import Compact.Core.IntegerSupport','','namespace N12Compact.C898Shared','open IntegerSupport','set_option maxRecDepth 100000','set_option Elab.async false','set_option linter.unnecessarySeqFocus false','',
       '/-- Exact rows paired with denominator minus one; positivity is structural. -/',
       'noncomputable def rowData : Array (Array (Row × Nat)) := row_text% "']
for entry in row_entries:
    x,y,z=entry['integers'];s=str(entry['strict']).lower();d=entry['denominator']
    assert d > 0
    lines.append(f'{x},{y},{z},{s},{d - 1}')
lines+= ['"','',f'abbrev rowCount : Nat := {len(row_entries)}',
          'noncomputable def rows (i : Fin rowCount) : Row := (rowData[i.val]!).1',
          'noncomputable def denominators (i : Fin rowCount) : Nat := Nat.succ ((rowData[i.val]!).2)','',
          'theorem positive_denominators : ∀ i : Fin rowCount, 0 < denominators i := by',
          '  intro i', '  exact Nat.zero_lt_succ _','','end N12Compact.C898Shared','']
# Product fallback is explicit, so no Inhabited Row instance is assumed.
lines=[l.replace('(rowData[i.val]!)',"(RowSyntax.lookup rowData i.val)") for l in lines]
rowsfile.write_text('\n'.join(lines))
posefile=outdir/'SharedPoses.lean'
lines=['import Compact.Core.PoseSyntax','import Compact.Cases.C898.SharedRows','import S12.OwnerEnclosure','import S12.AngleData64','',
       'namespace N12Compact.C898Shared','open S12 IntegerSupport','set_option Elab.async false','set_option linter.unnecessarySeqFocus false','',
       f'abbrev poseCount : Nat := {len(poses)}',
       f'noncomputable def poseData : Array (Array (Fin 64 × List (Fin rowCount))) := pose_text% 64 {len(row_entries)} "']
for p in poses:lines.append(str(p["angle"])+";"+",".join(map(str,p["rows"])))
lines+= ['"','',
         'noncomputable def poseAngle (i : Fin poseCount) : Fin 64 := (PoseSyntax.lookup poseData (0, []) i.val).1',
         'noncomputable def poseRows (i : Fin poseCount) : List (Fin rowCount) := (PoseSyntax.lookup poseData (0, []) i.val).2',
         'noncomputable def poses (i : Fin poseCount) : PoseLeaf :=',
         '  ⟨(angles64[(poseAngle i).val]?).getD ⟨angle64_0, angle64_0_checked⟩,',
         '    (poseRows i).map (fun r => (rows r).normalized (denominators r))⟩','',
         '/-- Names retain the authenticated source identifiers and exact row order. -/']
for p in poses:lines.append(f"noncomputable def {p['name']} : PoseLeaf := poses {p['index']}")
lines+= ['','end N12Compact.C898Shared',''];posefile.write_text('\n'.join(lines))
payload={'scope':'Exact source data translation only; generated Lean not yet checked.',
         'namespace':'N12Compact.C898Shared','module':'Compact.Cases.C898.SharedPoses',
         'row_count':len(row_entries),'rows':row_entries,'pose_count':len(poses),'poses':poses,'blocks':blocks,
         'source_files':provenance,
         'output_files':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'newlines':p.read_bytes().count(b'\n'),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in [rowsfile,posefile]]}
(ROOT/'evidence/c898-shared-pose-map.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
print(json.dumps({'rows':len(row_entries),'poses':len(poses),'raw_source_leaves':sum(p['name'].startswith('leaf898_') for p in poses),'blocks':len(blocks),'files':payload['output_files']},indent=2))
