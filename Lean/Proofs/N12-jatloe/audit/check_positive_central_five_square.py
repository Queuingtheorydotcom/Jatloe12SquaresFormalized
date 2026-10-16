"""Exact audit of a hand-supplied local witness, not a search or Lean proof."""
import json
import sys
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path

root = Path(__file__).resolve().parents[1]
original = json.loads((root / "evidence/positive-central-three-square-left-point-countermodel.json").read_text())
a = Q(original["side"])
squares = {name: tuple(map(Q, record["frame"]))
           for name, record in original["squares"].items()}
c, s, u, v = squares["A"]
squares["A"] = (c, s, u, v-Q(1, 10000))
squares["W"] = (Q(1), Q(0), Q(0), Q(2)-Q(1, 20000))
squares["E"] = (Q(1), Q(0), Q(0), Q(4)-a)
positive_bottom = "--positive-bottom" in sys.argv
if positive_bottom:
    c,s = Q(39999,40001),Q(400,40001)
    u = 2*c+Q(457,500)*s-a
    squares["O"] = (c,s,u,-s*u/c)
    squares["L"] = (Q(1),Q(0),Q(0),Q(49999,50000))
    squares["W"] = (Q(1),Q(0),Q(0),Q(199999,100000))
order_triple = "--order-triple" in sys.argv
if order_triple:
    assert positive_bottom
    squares = {name:square for name,square in squares.items() if name in ("O","A","W")}
markers = [(1,Q(457,500)), (Q(457,500),1), (3,Q(457,500)),
           (Q(1543,500),1), (3,Q(1543,500)), (Q(1543,500),3),
           (1,Q(1543,500)), (Q(457,500),3), (Q(33,20),Q(33,20)),
           (Q(47,20),Q(33,20)), (Q(47,20),Q(47,20)), (Q(33,20),Q(47,20)),
           (Q(457,500),2), (2,Q(457,500)), (Q(1543,500),2), (2,Q(1543,500))]
auxiliary = [(1,Q(87,50)),(1,Q(113,50)),(Q(8,5),1),(Q(8,5),3),
             (2,Q(87,50)),(2,Q(113,50)),(Q(12,5),1),(Q(12,5),3),
             (3,Q(87,50)),(3,Q(113,50)),(1,Q(8,5)),(1,Q(12,5)),
             (Q(87,50),1),(Q(87,50),2),(Q(87,50),3),(Q(113,50),1),
             (Q(113,50),2),(Q(113,50),3),(3,Q(8,5)),(3,Q(12,5))]

def inside(square, point):
    c,s,u,v = square
    x,y = point
    return u<c*x+s*y<u+a and v<-s*x+c*y<v+a

def vertices(square):
    c,s,u,v = square
    return [(c*U-s*V,s*U+c*V) for U,V in product((u,u+a),(v,v+a))]

expected = {"O":([0],[2,12]), "L":([1],[0,10]), "A":([8],[4,13]),
            "W":([12],[1,11]), "E":([6,7],[])}
report = {"scope":"Exact local witness; not a twelve-square packing, not Lean replay.",
          "side":str(a), "squares":{}, "separators":{}}
for name,square in squares.items():
    c,s,u,v = square
    signature = ([i for i,p in enumerate(markers) if inside(square,p)],
                 [i for i,p in enumerate(auxiliary) if inside(square,p)])
    record = {"frame":list(map(str,square)), "unit":c*c+s*s==1,
              "contained":all(0<=x<=4 and 0<=y<=4 for x,y in vertices(square)),
              "markers":signature[0], "auxiliary":signature[1],
              "center":inside(square,(2,2)), "left_point":inside(square,(1,2)),
              "top_seed":inside(square,(1,Q(72,25)))}
    assert record["unit"] and record["contained"], (name,record)
    assert signature == expected[name], (name,signature,expected[name])
    required = [tuple(map(Q,r["point"])) for r in original["squares"].get(name,{}).get("required",[])]
    if name=="E": required += [(1,3)]
    record["required"] = [{"point":list(map(str,p)),"strict":inside(square,p)} for p in required]
    assert all(r["strict"] for r in record["required"]), (name,record)
    report["squares"][name] = record
for (name,x),(other,y) in combinations(squares.items(),2):
    separators = []
    for which,square in ((name,x),(other,y)):
        c,s,_,_ = square
        for axis,(nx,ny) in (("U",(c,s)),("V",(-s,c))):
            px = [nx*X+ny*Y for X,Y in vertices(x)]
            py = [nx*X+ny*Y for X,Y in vertices(y)]
            for direction,gap in ((name+"-before-"+other,min(py)-max(px)),
                                  (other+"-before-"+name,min(px)-max(py))):
                if gap>=0: separators.append({"frame":which,"axis":axis,"direction":direction,"gap":str(gap)})
    assert separators, (name,other)
    report["separators"][name+other] = separators
assert not report["squares"]["A"]["center"]
assert not report["squares"]["A"]["left_point"]
report["all_pairs_separated"] = True
report["local_center_forcing_claim_refuted"] = True
if positive_bottom:
    assert squares["O"][1]>0 and squares["W"][1]==0
    report["missing_west_angle_order_refuted"] = True
destination = root / ("evidence/positive-bottom-order-triple-countermodel.json" if order_triple
                      else "evidence/positive-bottom-five-square-countermodel.json" if positive_bottom
                      else "evidence/positive-central-five-square-countermodel.json")
destination.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({"result":"passed", "squares":len(squares), "pairs":len(report["separators"]), "output":str(destination)}))
