"""Emit the new C98154/55 exact continuous certificate, never run Lean.

Parent-only serial execution under the external256MiB guard. Internal25s
timeout, <=65 total new Lean modules including ShortCertificateBridge,
and <=6MiB aggregate generated Lean source. No archive, network or native
proof is used. Every output is a proposal until its Lean checks pass.
"""
from __future__ import annotations
import argparse
import importlib.util
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
import json
import resource
import signal
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUT = HERE/'ShortCertificate54'
MOD = 'Compact.Completion.C981.ShortCertificate54'
NS = 'N12Compact.C981CompletionShort54'
factor_spec = importlib.util.spec_from_file_location(
    'short54_input_factor', ROOT/'scripts/factor_short54_inputs.py')
factor = importlib.util.module_from_spec(factor_spec)
factor_spec.loader.exec_module(factor)
spec = importlib.util.spec_from_file_location('c981_proposal_geometry', HERE/'short_certificate_pilot.py')
geo = importlib.util.module_from_spec(spec)
spec.loader.exec_module(geo)
Q = geo.Q
ROW_ATOMS = {}
DEN_ATOMS = {}
BASIS_ATOMS = {}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def qtext(q):
    q = Q(q)
    return str(q.numerator) if q.denominator == 1 else '('+str(q.numerator)+'/'+str(q.denominator)+')'


def point_text(p):
    return '('+qtext(p[0])+','+qtext(p[1])+')'


def points_text(points):
    return '['+','.join(point_text(p) for p in points)+']'


def row_text(row):
    key=tuple(row[:4])
    if key not in ROW_ATOMS:
        ROW_ATOMS[key]=len(ROW_ATOMS)
    return 'row'+str(ROW_ATOMS[key])


def den_text(den):
    if den<100000000:
        return str(den)
    if den not in DEN_ATOMS:
        DEN_ATOMS[den]=len(DEN_ATOMS)
    return 'den'+str(DEN_ATOMS[den])


def basis_text(a,b,x,y,den):
    key=(tuple(a[:4]),tuple(b[:4]),x,y,den)
    row_text(a)
    row_text(b)
    if key not in BASIS_ATOMS:
        BASIS_ATOMS[key]=len(BASIS_ATOMS)
    return 'basis'+str(BASIS_ATOMS[key])


def atom_declarations():
    out=[]
    for (x,y,c,strict),index in ROW_ATOMS.items():
        out.append(f'def row{index} : Row := ⟨{x},{y},{c},{str(strict).lower()}⟩')
    for den,index in DEN_ATOMS.items():
        out.append(f'def den{index} : Nat := {den}')
    for (a,b,x,y,den),index in BASIS_ATOMS.items():
        out.append(f'def basis{index} : VertexSupport.Basis := ⟨{row_text(a)},{row_text(b)},{x},{y},{den}⟩')
    return '\n'.join(out)+'\n'


def rows_text(rows):
    return '['+','.join(row_text(r) for r in rows)+']'


def list_text(values):
    return '['+','.join(map(str,values))+']'


def array_text(values):
    return '#['+','.join(values)+']'


def header(imports):
    return '\n'.join('import '+m for m in imports)+f'''\n\nnamespace {NS}
open S12 S12Pilot N12Compact IntegerSupport RegionDAG
open C981CompletionShortCertificate
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
\n'''


def footer():
    return '\nend\nend '+NS+'\n'


def integer_form(x,y,c,strict):
    x,y,c = map(Q,(x,y,c))
    den = lcm(x.denominator,y.denominator,c.denominator)
    return (int(x*den),int(y*den),int(c*den),strict,den)


def point_forms(angle,p,inner=False):
    _,_,c,s,outer,small,_ = angle
    radius = (small if inner else Q(1001,1000)*outer)/2
    return [integer_form(-n[0],-n[1],geo.dot(n,p)+radius,True) for n in geo.axes(angle)]


def coeff(row):
    return row[:2]


def row_eval(row,p):
    return row[0]*p[0]+row[1]*p[1]+row[2]


def cramer(a,b,n):
    det = a[0]*b[1]-a[1]*b[0]
    if det == 0:
        return None
    sign = 1 if det > 0 else -1
    left = sign*(n[0]*b[1]-n[1]*b[0])
    right = sign*(a[0]*n[1]-a[1]*n[0])
    return left,right,sign*det


class Program:
    def __init__(self,angle,initial_rows,poly):
        self.angle=angle
        self.rows=[]
        self.row_map={}
        self.contexts=[(0,0,0)]
        self.context_map={}
        self.nodes=[]
        self.leaves=[]
        self.leaf_polys=[]
        self.leaf_map={}
        self.forbidden=[]
        self.forbidden_points=[]
        self.forbidden_map={}
        self.initial=[self.add(r) for r in initial_rows]
        self.one=self.add((0,0,1,True,1))
        need(self.one in self.initial,'the strict constant input must be present')
        self.initial_context=0
        for row in reversed(self.initial):
            self.initial_context=self.push(self.initial_context,row)
        self.poly=poly

    def add(self,row):
        if row not in self.row_map:
            self.row_map[row]=len(self.rows)
            self.rows.append(row)
        return self.row_map[row]

    def push(self,parent,row):
        key=(parent,row)
        if key not in self.context_map:
            self.context_map[key]=len(self.contexts)
            self.contexts.append((parent,row,self.contexts[parent][2]+1))
        return self.context_map[key]

    def context_rows(self,context):
        rows=[]
        while context:
            parent,row,_=self.contexts[context]
            rows.append(row)
            context=parent
        return rows

    def node(self,context,kind):
        self.nodes.append((context,kind))
        return len(self.nodes)-1

    def active(self,poly,inputs):
        active=[i for i in inputs if any(row_eval(self.rows[i],p)==0 for p in poly)]
        return sorted(set(active+[self.one]))

    def leaf(self,context,poly):
        active=self.active(poly,self.context_rows(context))
        key=(poly,tuple(active))
        if key not in self.leaf_map:
            self.leaf_map[key]=len(self.leaves)
            self.leaves.append(active)
            self.leaf_polys.append(poly)
        return self.node(context,('leaf',self.leaf_map[key]))

    def basis(self,poly,inputs,n):
        minimum=min(geo.dot(n,p) for p in poly)
        for p in poly:
            if geo.dot(n,p)!=minimum:
                continue
            active=[i for i in inputs if row_eval(self.rows[i],p)==0]
            for a,b in combinations(active,2):
                weights=cramer(self.rows[a],self.rows[b],n)
                if weights and weights[0]>=0 and weights[1]>=0:
                    return a,b,p,weights
        raise ValueError('no nonnegative active basis for an exact support')

    def empty_after(self,context,before,prior,new):
        row=self.rows[new]
        a,b,p,(left,right,scale)=self.basis(before,prior,(-row[0],-row[1]))
        terms=[(left,a),(right,b),(scale,new)]
        total=[sum(w*self.rows[i][j] for w,i in terms) for j in range(3)]
        need(total[0]==total[1]==0 and total[2]<0,'closed empty branch needs a negative exact dual')
        terms.append((-total[2],self.one))
        return self.empty_node(context,terms)

    def empty_node(self,context,terms):
        terms=[(w,i) for w,i in terms if w]
        common=0
        for w,_ in terms:
            common=gcd(common,abs(w))
        terms=[(w//common,i) for w,i in terms]
        need(all(w>=0 and i in self.context_rows(context) for w,i in terms),'empty dual must use actual inputs')
        need(all(sum(w*self.rows[i][j] for w,i in terms)==0 for j in range(3)),'empty dual identity failed')
        need(any(w>0 and self.rows[i][3] for w,i in terms),'empty dual must be strict')
        return self.node(context,('empty',terms))

    def strict_empty(self,context,poly):
        """Optional zero-slack dual for a lower-dimensional strict branch."""
        if len(poly)>=3:
            return None
        inputs=self.context_rows(context)
        p=poly[0]
        active=[i for i in inputs if row_eval(self.rows[i],p)==0]
        for a,b in combinations(active,2):
            A,B=self.rows[a],self.rows[b]
            if A[0]*B[1]-A[1]*B[0]:
                continue
            if A[0]*B[0]+A[1]*B[1]>=0:
                continue
            w1,w2=(abs(B[0]),abs(A[0])) if A[0] else (abs(B[1]),abs(A[1]))
            terms=[(w1,a),(w2,b)]
            if any(w and self.rows[i][3] for w,i in terms):
                return self.empty_node(context,terms)
        for a,b,c in combinations(active,3):
            A,B,C=self.rows[a],self.rows[b],self.rows[c]
            if not any(r[3] for r in [A,B,C]):
                continue
            weights=[B[0]*C[1]-B[1]*C[0],C[0]*A[1]-C[1]*A[0],A[0]*B[1]-A[1]*B[0]]
            if all(w<=0 for w in weights):
                weights=[-w for w in weights]
            if all(w>=0 for w in weights) and any(w>0 and self.rows[i][3] for w,i in zip(weights,[a,b,c])):
                return self.empty_node(context,list(zip(weights,[a,b,c])))
        return None

    def block_id(self,rows,point):
        key=tuple(rows)
        if key not in self.forbidden_map:
            self.forbidden_map[key]=len(self.forbidden)
            self.forbidden.append(rows)
            self.forbidden_points.append(point)
        return self.forbidden_map[key]

    def remove(self,poly,context,blocks,index=0):
        if index==len(blocks):
            return self.leaf(context,poly)
        forms,point=blocks[index]
        if any(all(row_eval(row,p)<=0 for p in poly) for row in forms):
            return self.remove(poly,context,blocks,index+1)
        row_ids=[self.add(r) for r in forms]
        def faces(poly,context,face):
            if face==len(row_ids):
                empty=self.strict_empty(context,poly)
                if empty is not None:
                    return empty
                return self.node(context,('forbidden',self.block_id(row_ids,point)))
            row_id=row_ids[face]
            row=self.rows[row_id]
            opposite=self.add((-row[0],-row[1],-row[2],not row[3],row[4]))
            yes_context=self.push(context,row_id)
            no_context=self.push(context,opposite)
            yes_poly=geo.clip(poly,(-row[0],-row[1]),row[2])
            no_poly=geo.clip(poly,(row[0],row[1]),-row[2])
            prior=self.context_rows(context)
            yes=(faces(yes_poly,yes_context,face+1) if yes_poly else
                 self.empty_after(yes_context,poly,prior,row_id))
            no=(self.remove(no_poly,no_context,blocks,index+1) if no_poly else
                self.empty_after(no_context,poly,prior,opposite))
            return self.node(context,('cut',row_id,opposite,yes,no))
        return faces(poly,context,0)

    def lean(self,name):
        n=len(self.rows)
        need(n>0 and self.nodes,'region program must have real data')
        row_records=[f'({row_text(r)},{den_text(r[4])})' for r in self.rows]
        contexts=[f'⟨{p},{r},{d}⟩' for p,r,d in self.contexts]
        nodes=[]
        for context,kind in self.nodes:
            if kind[0]=='empty':
                terms='['+','.join(f'({w},{i})' for w,i in kind[1])+']'
                value=f'.empty ⟨{terms},1⟩'
            elif kind[0]=='cut':
                value='.cut '+' '.join(map(str,kind[1:]))
            else:
                value='.'+kind[0]+' '+str(kind[1])
            nodes.append(f'⟨{context},{value}⟩')
        return f'''def {name}_rows : Array (Row × Nat) := {array_text(row_records)}
def {name}_contexts : Array (RegionDAG.Context {n}) := {array_text(contexts)}
def {name}_nodes : Array (RegionDAG.Node {n}) := {array_text(nodes)}
def {name}_leaves : Array (List (Fin {n})) := {array_text([list_text(v) for v in self.leaves])}
def {name}_forbidden : Array (List (Fin {n})) := {array_text([list_text(v) for v in self.forbidden])}
def {name}_program : RegionDAG.Program {n} :=
  ⟨(fun i => (({name}_rows[i.val]?).getD (⟨0,0,0,false⟩,1)).1),
   (fun i => (({name}_rows[i.val]?).getD (⟨0,0,0,false⟩,1)).2),
   (fun i => ({name}_contexts[i]?).getD ⟨0,0,0⟩),
   (fun i => ({name}_nodes[i]?).getD ⟨0,.leaf 0⟩),{len(self.nodes)},
   (fun i => ({name}_leaves[i]?).getD []),{len(self.leaves)},
   (fun i => ({name}_forbidden[i]?).getD []),{len(self.forbidden)}⟩
theorem {name}_program_checked : {name}_program.Check := by decide +kernel
'''


def initial(i,k,owned,outside,aa):
    angle=aa[k]
    wall=angle[6]
    low,high=wall/2,4-wall/2
    poly=((low,low),(high,low),(high,high),(low,high))
    own_forms=[f for p in owned[i] for f in point_forms(angle,p)]
    walls=[integer_form(1,0,-low,False),integer_form(-1,0,high,False),
           integer_form(0,1,-low,False),integer_form(0,-1,high,False)]
    forms=own_forms+walls+[(0,0,1,True,1)]
    program=Program(k,forms,poly)
    prior=[program.add(r) for r in walls]+[program.one]
    for row in own_forms:
        ident=program.add(row)
        clipped=geo.clip(poly,(-row[0],-row[1]),row[2])
        if not clipped:
            program.root=program.empty_after(program.initial_context,poly,prior,ident)
            return program
        poly=clipped
        prior.append(ident)
    blocks=[(point_forms(angle,p,True),p) for p in outside[i]]
    program.root=program.remove(poly,program.initial_context,blocks)
    need(len(program.leaves)<=512,'per-root leaf cap reached')
    return program


def all_directions(aa):
    out=[]
    for quadrant in range(4):
        for angle in aa:
            c,s=angle[2:4]
            x,y=[(c,s),(-s,c),(-c,-s),(s,-c)][quadrant]
            den=lcm(x.denominator,y.denominator)
            out.append((int(x*den),int(y*den)))
    return out


def basis_record(a,b,p):
    den=lcm(p[0].denominator,p[1].denominator)
    x,y=int(p[0]*den),int(p[1]*den)
    common=gcd(gcd(abs(x),abs(y)),den)
    return a,b,x//common,y//common,den//common


def fan_record(k,poly,rows,directions):
    program=Program(k,[tuple(r[:4])+(1,) for r in rows],poly)
    inputs=list(program.initial)
    entries=[]
    previous=None
    for key,n in enumerate(directions):
        a,b,p,_=program.basis(poly,inputs,n)
        record=basis_record(program.rows[a],program.rows[b],p)
        if record!=previous:
            entries.append((key,record))
            previous=record
    need(entries and entries[0][0]==0,'support fan must cover key0')
    return {'angle':k,'rows':rows,'entries':entries}


def ref_text(angle):
    c,s=angle[2:4]
    den=lcm(c.denominator,s.denominator)
    inner=angle[5]
    return '⟨'+','.join(map(str,(int(c*den),int(s*den),den,inner.numerator,inner.denominator)))+'⟩'


def fan_lean(name,fan,aa,inputs_expr):
    def entry_text(entry):
        key,(a,b,x,y,d)=entry
        return f'⟨{key},{basis_text(a,b,x,y,d)}⟩'
    entries=[entry_text(e) for e in fan['entries']]
    return f'''def {name} : RawSupportFan.Context :=
  ⟨reference{fan['angle']},{entries[0]},{array_text(entries)}⟩
theorem {name}_checked : FanCheck {name} ({inputs_expr}) := by decide +kernel
'''


def fan_select(fan,key):
    record=fan['entries'][0][1]
    for start,entry in fan['entries']:
        if start>key:
            break
        record=entry
    return record


def validate_pair(a,b,aa,directions):
    ak,bk=a['angle'],b['angle']
    keys=[ak,ak+64,ak+32,ak+96,bk,bk+64,bk+32,bk+96]
    for key in keys:
        nx,ny=directions[key]
        A=fan_select(a,key)
        B=fan_select(b,(key+64)%128)
        aw,bw=cramer(A[0],A[1],(nx,ny)),cramer(B[0],B[1],(-nx,-ny))
        need(aw and bw and aw[0]>=0 and aw[1]>=0 and bw[0]>=0 and bw[1]>=0,'pair fan cone is not checked')
        lower_a=Q(nx*A[2]+ny*A[3],A[4])
        lower_b=Q(-nx*B[2]-ny*B[3],B[4])
        radius=geo.radius(aa[ak],(nx,ny))+geo.radius(aa[bk],(nx,ny))
        need(-lower_a-lower_b<=radius,'pair support bound fails')
        strict=any(w>0 and row[3] for w,row in [(aw[0],A[0]),(aw[1],A[1]),(bw[0],B[0]),(bw[1],B[1])])
        need(-lower_a-lower_b<radius or strict,'a tangent pair needs a strict actual input')


def step(sources,neighbors,aa,directions):
    grouped={}
    for state in neighbors:
        grouped.setdefault(state['angle'],[]).extend(state['poly'])
    plans=[]
    targets=[]
    for source in sources:
        k=source['angle']
        planes=[]
        for n in geo.axes(aa[k]):
            threshold=min(geo.dot(n,p)+geo.radius(aa[l],n) for l,points in grouped.items() for p in points)
            planes.append((n,geo.radius(aa[k],n)+threshold))
        for l,points in grouped.items():
            for n in geo.axes(aa[l]):
                planes.append((n,geo.radius(aa[k],n)+geo.radius(aa[l],n)+min(geo.dot(n,p) for p in points)))
        block=[integer_form(-n[0],-n[1],rhs,True) for n,rhs in planes]
        source_rows=[tuple(row[:4])+(1,) for row in source['rows']]
        program=Program(k,source_rows,source['poly'])
        program.root=program.remove(source['poly'],program.initial_context,[(block,None)])
        block_rows=[tuple(row[:4]) for row in block]
        fan=None
        if program.forbidden:
            poly=source['poly']
            for row in block:
                poly=geo.clip(poly,(-row[0],-row[1]),row[2])
            need(poly,'a forbidden block must have a retained closed polygon')
            fan=fan_record(k,poly,block_rows+source['rows'],directions)
        plan={'source':source,'program':program,'block':block_rows,'fan':fan}
        plans.append(plan)
        for rows,poly in zip(program.leaves,program.leaf_polys):
            targets.append({'angle':k,'rows':[program.rows[i][:4] for i in rows],
                            'poly':poly,'plan':len(plans)-1,'leaf':len(targets)-sum(len(p['program'].leaves) for p in plans[:-1])})
    need(len(targets)<=512,'per-owner512 leaf cap reached')
    return plans,targets


def state_text(state):
    k=state['angle']
    return f'⟨⟨angle32_{k},angle32_{k}_checked⟩,{rows_text(state["rows"])}⟩'


def emit_inputs(owned,outside,ancestry,aa):
    s=header(['Compact.Completion.C981.ShortCertificateBridge','S12.AngleData32'])
    for i in [5,6,7]:
        s+=f'def inside{i} : List (ℚ × ℚ) := {points_text(owned[i])}\n'
        s+=f'def outside{i} : List (ℚ × ℚ) := {points_text(outside[i])}\n'
    for k,angle in enumerate(aa):
        s+=f'def reference{k} : ReferenceAxis.Reference := {ref_text(angle)}\n'
        s+=f'theorem reference{k}_valid : reference{k}.Valid := by decide +kernel\n'
        s+=f'theorem reference{k}_exact : reference{k}.value=angle32_{k}.reference 1 := by decide +kernel\n'
    return s+footer()


def emit_initial(programs,owned,outside):
    files={}
    names={5:[],6:[],7:[]}
    for batch in range(6):
        s=header([MOD+'.Inputs'])
        subset=programs[batch*16:(batch+1)*16]
        for i,k,program in subset:
            name=f'initial{i}_{k}'
            names[i].append(name)
            s+=program.lean(name)
            s+=f'''def {name} : RegionOwner.Root :=
  ⟨{len(program.rows)},{name}_program,{program.root},⟨angle32_{k},angle32_{k}_checked⟩⟩
theorem {name}_checked : {name}.Check inside{i} outside{i} := by
  refine ⟨{name}_program_checked,?_,?_,?_,?_⟩ <;> decide +kernel
'''
        files[f'Initial{batch}']=s+footer()
    s=header([MOD+f'.Initial{i}' for i in range(6)])
    for i in [5,6,7]:
        roots='['+','.join(f'⟨{n},{n}_checked⟩' for n in names[i])+']'
        s+=f'''def owner{i} : RegionOwner.Owner := ⟨inside{i},outside{i},{roots}⟩
theorem owner{i}_checked : owner{i}.Check := by decide +kernel
def initialStates{i} : List State := ownerStates owner{i}
'''
    files['InitialAssembly']=s+footer()
    return files


def emit_neighbors(states,aa,directions):
    s=header([MOD+'.InitialAssembly'])
    fans={}
    for i in [6,7]:
        for j,state in enumerate(states[i]):
            s+=f'def state{i}_{j} : State := {state_text(state)}\n'
            fan=fan_record(state['angle'],state['poly'],state['rows'],directions)
            fans[i,j]=fan
            s+=fan_lean(f'fan{i}_{j}',fan,aa,f'state{i}_{j}.rows')
        n=len(states[i])
        s+=f'def state{i} : Fin {n} → State := !['+','.join(f'state{i}_{j}' for j in range(n))+']\n'
        s+=f'def fan{i} : Fin {n} → RawSupportFan.Context := !['+','.join(f'fan{i}_{j}' for j in range(n))+']\n'
        s+=f'def angle{i} : Fin {n} → Nat := !['+','.join(str(st['angle']) for st in states[i])+']\n'
        s+=f'''theorem initialStates{i}_exact : initialStates{i}=(List.finRange {n}).map state{i} := by decide +kernel
theorem fan{i}_valid (j : Fin {n}) : FanCheck (fan{i} j) (state{i} j).rows := by
  fin_cases j
'''
        for j in range(n):
            s+=f'  · exact fan{i}_{j}_checked\n'
        s+=f'''theorem fan{i}_reference_valid (j : Fin {n}) : (fan{i} j).reference.Valid := by decide +kernel
theorem fan{i}_reference_exact (j : Fin {n}) :
    (fan{i} j).reference.value=(state{i} j).angle.val.reference 1 := by decide +kernel
'''
    return s+footer(),fans


def emit_stage(stage,plans,targets,aa):
    s=header([MOD+'.Neighbors'])
    for i,plan in enumerate(plans):
        name=f'stage{stage}_{i}'
        program=plan['program']
        s+=program.lean(name)
        s+=f'''def {name} : Plan :=
  ⟨{len(program.rows)},{name}_program,{program.root},{state_text(plan['source'])},{rows_text(plan['block'])}⟩
theorem {name}_checked : {name}.Check := by
  refine ⟨{name}_program_checked,?_,?_,?_⟩ <;> decide +kernel
'''
        if plan['fan']:
            s+=fan_lean(f'{name}_fan',plan['fan'],aa,f'{name}.block++{name}.source.rows')
    s+=f'def stage{stage}Plans : List Plan := ['+','.join(f'stage{stage}_{i}' for i in range(len(plans)))+']\n'
    source='initialStates5' if stage==1 else 'stage1Plans.flatMap Plan.states'
    if stage==2:
        # This source equality is placed in Geometry after both data modules.
        source=None
    if source:
        s+=f'theorem stage{stage}_sources : stage{stage}Plans.map Plan.source={source} := by decide +kernel\n'
    return s+footer()


def emit_pairs(stage,plans,neighbor,batch,batches,aa,neighbors):
    imports=[MOD+f'.Stage{stage}']
    s=header(imports)
    start=len(plans)*batch//batches
    stop=len(plans)*(batch+1)//batches
    n=len(neighbors)
    count=(n+7)//8
    for i in range(start,stop):
        plan=plans[i]
        if not plan['fan']:
            continue
        name=f'stage{stage}_{i}'
        k=plan['source']['angle']
        for block in range(count):
            s+=f'''theorem {name}_pairs{block} : FiniteCheckChunks.Check
    (fun j : Fin {n} => RawSupportFan.PairCheck {name}_fan (fan{neighbor} j)
      (keys {k} (angle{neighbor} j)) opposite) {block} := by decide +kernel
'''
        s+=f'''theorem {name}_pairs (j : Fin {n}) :
    RawSupportFan.PairCheck {name}_fan (fan{neighbor} j) (keys {k} (angle{neighbor} j)) opposite := by
  refine FiniteCheckChunks.sound _ (count:={count}) (by decide) ?_ j
  intro block
  fin_cases block
'''
        for block in range(count):
            s+=f'  · exact {name}_pairs{block}\n'
    return s+footer()


def emit_geometry(plans1,plans2,n6,n7):
    imports=[MOD+f'.Pairs1_{i}' for i in range(4)]+[MOD+f'.Pairs2_{i}' for i in range(2)]
    s=header(imports)
    for stage,plans,neighbor,n in [(1,plans1,6,n6),(2,plans2,7,n7)]:
        for i,plan in enumerate(plans):
            name=f'stage{stage}_{i}'
            s+=f'''theorem {name}_forbidden (q r : OpenSquare)
    (hq : {name}.source.pose.Realizes q) (hr : Covered initialStates{neighbor} r)
    (apart : ∀ x y, ¬(q.Inside x y ∧ r.Inside x y))
    (positive : 0 < {name}.program.forbiddenCount) :
    ¬(∀ row ∈ {name}.block,row.Holds ![centerX q,centerY q]) := by
'''
            if not plan['fan']:
                s+='  have zero : '+name+'.program.forbiddenCount=0 := by rfl\n  omega\n'
                continue
            k=plan['source']['angle']
            s+=f'''  intro blocked
  obtain ⟨pose,member,realizes⟩ := hr
  obtain ⟨state,hs,rfl⟩ := List.mem_map.mp member
  rw [initialStates{neighbor}_exact] at hs
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hs
  obtain ⟨x,y,overlap⟩ := actual_overlap {name}.source (state{neighbor} j) {name}.block
    {name}_fan (fan{neighbor} j) {name}_fan_checked (fan{neighbor}_valid j)
    reference{k}_valid (fan{neighbor}_reference_valid j) reference{k}_exact
    (fan{neighbor}_reference_exact j) {k} (angle{neighbor} j) ({name}_pairs j)
    q r hq realizes blocked
  exact apart x y overlap
'''
        s+=f'''theorem stage{stage}_checked : ∀ plan ∈ stage{stage}Plans,plan.Check := by
  simp only [stage{stage}Plans,List.forall_mem_cons,List.forall_mem_nil,and_true]
  exact '''
        facts=[f'stage{stage}_{i}_checked' for i in range(len(plans))]
        proof=facts[-1]
        for fact in reversed(facts[:-1]):
            proof='⟨'+fact+','+proof+'⟩'
        s+=proof+'\n'
        s+=f'''theorem stage{stage}_forbidden (q r : OpenSquare)
    (hr : Covered initialStates{neighbor} r)
    (apart : ∀ x y, ¬(q.Inside x y ∧ r.Inside x y)) :
    ∀ plan ∈ stage{stage}Plans,plan.source.pose.Realizes q →
      0 < plan.program.forbiddenCount →
        ¬(∀ row ∈ plan.block,row.Holds ![centerX q,centerY q]) := by
  simp only [stage{stage}Plans,List.forall_mem_cons,List.forall_mem_nil,and_true]
  exact '''
        facts=[f'(fun incoming => stage{stage}_{i}_forbidden q r incoming hr apart)' for i in range(len(plans))]
        proof=facts[-1]
        for fact in reversed(facts[:-1]):
            proof='⟨'+fact+','+proof+'⟩'
        s+=proof+'\n'
    s+='''theorem stage2_sources : stage2Plans.map Plan.source=stage1Plans.flatMap Plan.states := by decide +kernel
theorem terminal : stage2Plans.flatMap Plan.states=[] := by decide +kernel

theorem impossible (q r t : OpenSquare)
    (hq : Covered initialStates5 q) (hr : Covered initialStates6 r) (ht : Covered initialStates7 t)
    (apartR : ∀ x y, ¬(q.Inside x y ∧ r.Inside x y))
    (apartT : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) : False := by
  have first := plans_sound initialStates5 stage1Plans stage1_checked
    (cover_of_source_map _ _ stage1_sources) q hq (stage1_forbidden q r hr apartR)
  have second := plans_sound (stage1Plans.flatMap Plan.states) stage2Plans stage2_checked
    (cover_of_source_map _ _ stage2_sources) q first (stage2_forbidden q t ht apartT)
  rw [terminal] at second
  obtain ⟨_,member,_⟩ := second
  simp only [List.map_nil,List.not_mem_nil] at member

#print axioms impossible
'''
    return s+footer()


def emit_original(owned,outside,ancestry):
    s=header([MOD+'.Geometry','Completion.Cases.C981.VectorData','S12.Convex'])
    s+='''open S12Completion.C981
structure ForeignPoint where
  owner : Fin 12
  first : ℚ × ℚ
  second : ℚ × ℚ
  weight : ℚ

def ForeignPoint.point (p : ForeignPoint) : ℚ × ℚ :=
  ((1-p.weight)*p.first.1+p.weight*p.second.1,
   (1-p.weight)*p.first.2+p.weight*p.second.2)

def ForeignPoint.Check (p : ForeignPoint) (i : Fin 12) (v : List (Finset Nat)) : Prop :=
  p.owner≠i ∧ 0≤p.weight ∧ p.weight≤1 ∧
  p.first∈queryInsidePoints (ownerMasks p.owner) 2 (v[p.owner.val]!) ∧
  p.second∈queryInsidePoints (ownerMasks p.owner) 2 (v[p.owner.val]!)
instance (p : ForeignPoint) (i : Fin 12) (v : List (Finset Nat)) : Decidable (p.Check i v) :=
  inferInstanceAs (Decidable (_ ∧ _))
'''
    # Keep direct outside points direct; other points carry an actual owner
    # and exact convex ancestry, never only a hull-membership assertion.
    all_original=set(geo.MARKERS+geo.AUX)
    proofs={}
    for i in [5,6,7]:
        selected=[]
        for point in outside[i]:
            if point in all_original and point not in owned[i]:
                continue
            matches=[a for a in ancestry if a[0]!=i and a[1]==point]
            need(matches,'every non-original point needs actual convex ancestry')
            j,p,a,b,t=matches[0]
            selected.append((j,a,b,t))
        proofs[i]=selected
        records=[f'⟨{j},{point_text(a)},{point_text(b)},{qtext(t)}⟩' for j,a,b,t in selected]
        s+=f'def foreign{i} : List ForeignPoint := ['+','.join(records)+']\n'
    s+='def Check (v : List (Finset Nat)) : Prop :=\n'
    parts=[]
    for i in [5,6,7]:
        parts += [f'(∀ P ∈ inside{i}, P∈queryInsidePoints (ownerMasks {i}) 2 (v[{i}]!))',
                  f'(∀ p ∈ foreign{i}, p.Check {i} v)',
                  f'(∀ P ∈ outside{i}, P∈queryOutsidePoints (ownerMasks {i}) 2 (v[{i}]!) ∨ ∃ p∈foreign{i}, p.point=P)']
    s+='  '+' ∧\n  '.join(parts)+'\n'
    s+='''instance (v : List (Finset Nat)) : Decidable (Check v) := inferInstanceAs (Decidable (_ ∧ _))

theorem excludes (v : List (Finset Nat)) (checked : Check v) : ExcludesVector v := by
  intro packing family vector
  let q := owners packing
  have aux (i : Fin 12) : AuxExact (q i) 2 (v[i.val]!) := by
    have entry := ownership_entry_at packing v vector i
    simpa only [q,owners,entry] using nat_combined_exact packing (ownerIndex packing (ownerMasks i))
  have inside (i : Fin 12) (P : ℚ × ℚ)
      (member : P∈queryInsidePoints (ownerMasks i) 2 (v[i.val]!)) : (q i).Inside P.1 P.2 :=
    query_inside_sound _ 2 _ _ (owners_side_gt packing i) (owners_side_le packing i)
      (owners_contained packing i) (owners_markers packing family i) (aux i) P member
  have outside (i : Fin 12) (P : ℚ × ℚ)
      (member : P∈queryOutsidePoints (ownerMasks i) 2 (v[i.val]!)) : ¬(q i).Inside P.1 P.2 :=
    query_outside_sound _ 2 _ _ (owners_markers packing family i) (aux i) P member
  have foreign (i : Fin 12) (p : ForeignPoint) (hp : p.Check i v) : ¬(q i).Inside p.point.1 p.point.2 := by
    have first := inside p.owner p.first hp.2.2.2.1
    have second := inside p.owner p.second hp.2.2.2.2
    have lower : (0:ℝ)≤p.weight := by exact_mod_cast hp.2.1
    have upper : (p.weight:ℝ)≤1 := by exact_mod_cast hp.2.2.1
    have strict := inside_segment (q p.owner) p.first.1 p.first.2 p.second.1 p.second.2
      p.weight first second lower upper
    have genuine : (q p.owner).Inside p.point.1 p.point.2 := by
      convert strict using 1 <;> dsimp [ForeignPoint.point] <;> push_cast <;> ring
    intro own
    exact owners_disjoint packing family i p.owner (Ne.symm hp.1) _ _ ⟨own,genuine⟩
'''
    for index,i in enumerate([5,6,7]):
        path='checked'+'.2'* (index*3)
        own=path+'.1'
        fp=path+'.2.1'
        omitted=path+'.2.2.1' if i!=7 else path+'.2.2'
        s+=f'''  have hi{i} : ∀ P∈inside{i}, (q {i}).Inside P.1 P.2 :=
    fun P member => inside {i} P ({own} P member)
  have ho{i} : ∀ P∈outside{i}, ¬(q {i}).Inside P.1 P.2 := by
    intro P member
    rcases {omitted} P member with direct | ⟨p,hp,he⟩
    · exact outside {i} P direct
    · rw [←he]
      exact foreign {i} p ({fp} p hp)
  have covered{i} : Covered initialStates{i} (q {i}) :=
    owner_sound owner{i} owner{i}_checked (q {i}) (owners_side_gt packing {i})
      (owners_side_le packing {i}) (owners_contained packing {i}) hi{i} ho{i}
'''
    s+='''  exact impossible (q 5) (q 6) (q 7) covered5 covered6 covered7
    (owners_disjoint packing family 5 6 (by decide)) (owners_disjoint packing family 5 7 (by decide))

theorem checked54 : Check (representativeVectors[54]!) := by decide +kernel
theorem checked55 : Check (representativeVectors[55]!) := by decide +kernel
theorem representative54_excluded : ExcludesVector (representativeVectors[54]!) := excludes _ checked54
theorem representative55_excluded : ExcludesVector (representativeVectors[55]!) := excludes _ checked55
#print axioms representative54_excluded
#print axioms representative55_excluded
'''
    return s+footer()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--external-memory-guard',action='store_true')
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    need(args.external_memory_guard,'parent external256MiB guard is required')
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('25-second generator limit')))
    signal.alarm(25)
    start=time.monotonic()
    report={'proof_status':'proposal_only','row_ids':[54,55]}
    try:
        aa=geo.angles()
        directions=all_directions(aa)
        owned,outside,ancestry=geo.inputs(54)
        programs=[]
        states={5:[],6:[],7:[]}
        for i in [5,6,7]:
            for k in range(32):
                program=initial(i,k,owned,outside,aa)
                programs.append((i,k,program))
                for leaf,(rows,poly) in enumerate(zip(program.leaves,program.leaf_polys)):
                    states[i].append({'angle':k,'rows':[program.rows[r][:4] for r in rows],
                                      'poly':poly,'initial':(i,k,leaf)})
            need(len(states[i])<=512,'per-owner512 leaf cap reached')
        report['initial_pieces']={i:len(v) for i,v in states.items()}
        first,remaining=step(states[5],states[6],aa,directions)
        second,terminal=step(remaining,states[7],aa,directions)
        report['stage_pieces']=[len(remaining),len(terminal)]
        need(not terminal,'the new certificate proposal must have an empty final cover')
        files={'Inputs':emit_inputs(owned,outside,ancestry,aa)}
        files.update(emit_initial(programs,owned,outside))
        neighbors,fans=emit_neighbors(states,aa,directions)
        files['Neighbors']=neighbors
        files['Stage1']=emit_stage(1,first,remaining,aa)
        files['Stage2']=emit_stage(2,second,terminal,aa)
        for stage,plans,neighbor,batches in [(1,first,6,4),(2,second,7,2)]:
            for plan in plans:
                if plan['fan']:
                    for j in range(len(states[neighbor])):
                        validate_pair(plan['fan'],fans[neighbor,j],aa,directions)
            for batch in range(batches):
                files[f'Pairs{stage}_{batch}']=emit_pairs(stage,plans,neighbor,batch,batches,aa,states[neighbor])
        files['Geometry']=emit_geometry(first,second,len(states[6]),len(states[7]))
        files['Original']=emit_original(owned,outside,ancestry)
        declarations=atom_declarations()
        files['Inputs']=files['Inputs'].replace(footer(),declarations+footer())
        input_files,input_report=factor.split_inputs(files['Inputs'])
        files.update(input_files)
        total=sum(len(text.encode()) for text in files.values())
        bridge_bytes=(HERE/'ShortCertificateBridge.lean').stat().st_size
        report['module_count_with_bridge']=len(files)+1
        report['generated_source_bytes']=total
        report['source_bytes_with_bridge']=total+bridge_bytes
        report['file_source_bytes']={name:len(text.encode()) for name,text in files.items()}
        report['shared_atoms']={'rows':len(ROW_ATOMS),'denominators':len(DEN_ATOMS),'vertex_bases':len(BASIS_ATOMS)}
        need(len(files)+1<=65,'sixty-five-module source limit exceeded')
        need(total+bridge_bytes<=6*1024*1024,'six-MiB source limit including bridge exceeded')
        OUT.mkdir(exist_ok=True)
        for name,text in files.items():
            target=OUT/(name+'.lean')
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_text(text)
        factor.MANIFEST.parent.mkdir(parents=True,exist_ok=True)
        factor.MANIFEST.write_text(json.dumps(input_report,indent=2)+'\n')
        report['input_factorization']=input_report
        report['status']='emitted'
        report['modules']=[MOD+'.'+name.replace('/','.') for name in files]
        report['source_directory']=str(OUT)
    except (TimeoutError,MemoryError,ValueError,RuntimeError) as error:
        report['status']='bounded_stop'
        report['reason']=str(error)
    report['elapsed_seconds']=round(time.monotonic()-start,3)
    report['reported_peak_rss']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    text=json.dumps(report,indent=2)+'\n'
    Path(args.report).write_text(text)
    print(text,end='')


if __name__=='__main__':
    main()
