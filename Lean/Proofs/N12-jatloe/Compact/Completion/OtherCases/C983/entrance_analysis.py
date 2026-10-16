"""Lightweight exact source metadata for C983's ordinary Lean certificates.
This script selects existing rational witnesses. It is not a proof oracle.
"""
import ast
import itertools
import json
import re
from fractions import Fraction as Q
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[4]

def value(text):
    def read(node):
        if isinstance(node, ast.Constant):
            return Q(node.value)
        if isinstance(node, ast.Tuple):
            return tuple(read(item) for item in node.elts)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -read(node.operand)
        if isinstance(node, ast.BinOp):
            left, right = read(node.left), read(node.right)
            if isinstance(node.op, ast.Div):
                return left / right
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
        raise ValueError(text)
    return read(ast.parse(text, mode="eval").body)

def fields(text):
    depth, start, result = 0, 0, []
    for index, char in enumerate(text):
        if char in "([{⟨":
            depth += 1
        elif char in ")]}⟩":
            depth -= 1
        elif char == "," and depth == 0:
            result.append(text[start:index].strip())
            start = index + 1
    result.append(text[start:].strip())
    return result

F = [(1,Q(87,50)),(1,Q(113,50)),(Q(8,5),1),(Q(8,5),3),
     (2,Q(87,50)),(2,Q(113,50)),(Q(12,5),1),(Q(12,5),3),
     (3,Q(87,50)),(3,Q(113,50))]
G = [(1,Q(8,5)),(1,Q(12,5)),(Q(87,50),1),(Q(87,50),2),
     (Q(87,50),3),(Q(113,50),1),(Q(113,50),2),(Q(113,50),3),
     (3,Q(8,5)),(3,Q(12,5))]

def transform(point, flags):
    x, y = point
    if flags[0] == "true":
        x, y = y, x
    if flags[1] == "true":
        x = 4 - x
    if flags[2] == "true":
        y = 4 - y
    return x, y

def query_metadata():
    four = {}
    for line in (PROJECT / "source/S12/FourPointData.lean").read_text().splitlines():
        match = re.match(r"def fourDatum(\d+) .*? := ⟨(.*)⟩$", line)
        if match:
            four[match[1]] = [value(item) for item in fields(match[2])[:4]]
    files = [PROJECT / "source/S12/LocalQueryData.lean",
             *sorted((PROJECT / "Compact/HistoricalOwnership").glob("Queries*.lean")),
             PROJECT / "Compact/Cases/C713/EntryQuery05.lean"]
    result = []
    for file in files:
        for line in file.read_text().splitlines():
            match = re.search(r"(?:def |checked_local_query )([A-Za-z0-9_]+).*?⟨(\d+),(\d+),\{([^}]*)\},(.*)⟩$", line)
            if not match:
                continue
            name, mask, kind, owned, certificate = match.groups()
            mask, kind = int(mask), int(kind)
            bits = sum(1 << int(index) for index in owned.split(",") if index.strip())
            if certificate.startswith(".hull "):
                outside = [value(fields(certificate[certificate.index("⟨")+1:-1])[3])]
            elif certificate.startswith(".four "):
                flags = re.search(r"⟨(true|false),(true|false),(true|false)⟩", certificate).groups()
                number = re.search(r"fourDatum(\d+)", certificate)[1]
                outside = [transform(point, flags) for point in four[number][2:4]]
            elif certificate.startswith(".short "):
                flags = re.search(r"⟨(true|false),(true|false),(true|false)⟩", certificate).groups()
                variant = re.search(r"\.(fiveLeft|fiveRight|six)", certificate)[1]
                points = [(1,Q(87,50)),(Q(33,20),Q(47,20)),(2,Q(87,50))]
                if variant == "six":
                    points = [(1,Q(8,5)),(1,Q(12,5)),(Q(33,20),Q(33,20))]
                outside = [transform(point, flags) for point in points]
            else:
                raise ValueError(certificate[:100])
            aux = F if kind == 0 else G if kind == 1 else F + G
            blocked = sum(1 << index for index, point in enumerate(aux) if point in outside)
            if name.startswith("localQuery"):
                reference = f"(certified_query% {name[10:]})"
            elif name.startswith("query713_"):
                reference = f"⟨S12.{name},S12.{name}_checked⟩"
            else:
                reference = f"N12Compact.HistoricalOwnership.Queries.{name}_certified"
            module = str(file.relative_to(PROJECT)).removesuffix(".lean").replace("/", ".")
            result.append(dict(mask=mask,kind=kind,owned=bits,blocked=blocked,
                               name=name,reference=reference,module=module))
    return result

CODES = [1,2,12,48,192,512,1024,2304,4096,8192,16384,32768]

def compatible(query, owned):
    return query["owned"] & owned == query["owned"] and not query["blocked"] & owned

def subsets(lower, upper):
    return [sum(1 << index for index in chosen)
            for size in range(lower, upper + 1)
            for chosen in itertools.combinations(range(10), size)]

def candidates(queries, mask, kind):
    exempt = mask in ([12,48,192,2304] if kind == 0 else [12,48,192])
    lower = 0 if exempt else 1
    upper = (2 if exempt else 3) if kind == 0 else (1 if exempt else 2)
    pool = [query for query in queries if query["mask"] == mask and query["kind"] == kind]
    allowed, selected = [], {}
    for owned in subsets(lower, upper):
        witness = next((query for query in pool if compatible(query, owned)), None)
        if witness is None:
            allowed.append(owned)
        else:
            selected[witness["module"], witness["name"]] = witness
    return dict(mask=mask,kind=kind,lower=lower,upper=upper,
                allowed=allowed,queries=list(selected.values()))

if __name__ == "__main__":
    queries = query_metadata()
    print(json.dumps([candidates(queries,mask,kind) for mask in CODES for kind in range(2)]))

