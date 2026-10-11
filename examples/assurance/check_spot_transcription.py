#!/usr/bin/env python3
"""Compare the checked-in Spot DOT graph with its Rocq PBuchi transcription.

This is an executable consistency check, not a verified importer. It checks
state/acceptance structure and propositional edge guards, up to state renaming.
It does not invoke Spot and does not prove language equivalence.
"""

from __future__ import annotations

import argparse
import itertools
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DOT_PATH = ROOT / "examples" / "spot" / "alarm_response_backend.dot"
ROCQ_PATH = ROOT / "proof" / "OverlappingResponse_Example.v"
ATOMS = ("handled", "not_alarm_prop", "clock_le_3", "unch_clock")
ROCq_ATOM = {
    ("LAct HANDLED", "true"): "handled",
    ("LAct HANDLED", "false"): "handled",
    ("LNAct ALARM", "true"): "not_alarm_prop",
    ("LNAct ALARM", "false"): "not_alarm_prop",
    ("LCLe alarm_clock 3", "true"): "clock_le_3",
    ("LCLe alarm_clock 3", "false"): "clock_le_3",
    ("LUnch alarm_clock", "true"): "unch_clock",
    ("LUnch alarm_clock", "false"): "unch_clock",
}


class CheckError(Exception):
    pass


@dataclass(frozen=True)
class Graph:
    states: frozenset[str]
    initial: str
    accepting: frozenset[str]
    # For each (source, target), the set of satisfying valuations.
    edges: dict[tuple[str, str], frozenset[tuple[bool, ...]]]


def assignments():
    return tuple(itertools.product((False, True), repeat=len(ATOMS)))


class BooleanParser:
    def __init__(self, source: str):
        self.tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[!&|()]", source)
        if "".join(self.tokens) != re.sub(r"\s+", "", source):
            raise CheckError(f"unsupported or malformed guard syntax: {source!r}")
        self.index = 0

    def parse(self):
        result = self.parse_or()
        if self.index != len(self.tokens):
            raise CheckError(f"unexpected token {self.tokens[self.index]!r}")
        return result

    def parse_or(self):
        node = self.parse_and()
        while self.take("|"):
            node = ("or", node, self.parse_and())
        return node

    def parse_and(self):
        node = self.parse_unary()
        while self.take("&"):
            node = ("and", node, self.parse_unary())
        return node

    def parse_unary(self):
        if self.take("!"):
            return ("not", self.parse_unary())
        if self.take("("):
            node = self.parse_or()
            if not self.take(")"):
                raise CheckError("unclosed parenthesis in guard")
            return node
        if self.index >= len(self.tokens):
            raise CheckError("unexpected end of guard")
        name = self.tokens[self.index]
        self.index += 1
        if name not in ATOMS:
            raise CheckError(f"unknown DOT guard atom {name!r}")
        return ("atom", name)

    def take(self, token):
        if self.index < len(self.tokens) and self.tokens[self.index] == token:
            self.index += 1
            return True
        return False


def evaluate(ast, assignment):
    kind = ast[0]
    if kind == "atom":
        return assignment[ast[1]]
    if kind == "not":
        return not evaluate(ast[1], assignment)
    if kind == "and":
        return evaluate(ast[1], assignment) and evaluate(ast[2], assignment)
    if kind == "or":
        return evaluate(ast[1], assignment) or evaluate(ast[2], assignment)
    raise CheckError(f"unknown expression node {kind!r}")


def merge_edge(edges, source, target, truth_set):
    key = (str(source), str(target))
    edges[key] = frozenset(set(edges.get(key, frozenset())) | set(truth_set))


def parse_dot(path: Path) -> Graph:
    text = path.read_text(encoding="utf-8", errors="replace")
    states = set()
    accepting = set()
    initial_edges = []
    edges = {}

    state_re = re.compile(r'^\s*(\d+)\s*\[label="(\d+)"([^]]*)\]\s*$')
    edge_re = re.compile(r'^\s*(\w+)\s*->\s*(\w+)\s*\[label="([^"]+)"\]\s*$')
    initial_re = re.compile(r"^\s*I\s*->\s*(\d+)\s*$")
    for line_no, line in enumerate(text.splitlines(), 1):
        state_match = state_re.match(line)
        if state_match:
            state, label, attrs = state_match.groups()
            if state != label:
                raise CheckError(f"DOT line {line_no}: state id/label mismatch")
            states.add(state)
            if re.search(r"(?:^|,)\s*peripheries\s*=\s*2(?:,|$)", attrs):
                accepting.add(state)
            continue
        initial_match = initial_re.match(line)
        if initial_match:
            initial_edges.append(initial_match.group(1))
            continue
        edge_match = edge_re.match(line)
        if not edge_match:
            continue
        source, target, label = edge_match.groups()
        if source == "I":
            initial_edges.append(target)
            continue
        ast = BooleanParser(label).parse()
        truth_set = frozenset(a for a in assignments() if evaluate(ast, dict(zip(ATOMS, a))))
        merge_edge(edges, source, target, truth_set)

    if not states:
        raise CheckError(f"no numeric states found in {path}")
    if len(initial_edges) != 1:
        raise CheckError(f"expected one Spot initial edge, found {len(initial_edges)}")
    if initial_edges[0] not in states:
        raise CheckError(f"initial edge points to undeclared state {initial_edges[0]}")
    if set(edges) and any(s not in states or t not in states for s, t in edges):
        raise CheckError("DOT transition references an undeclared state")
    return Graph(frozenset(states), initial_edges[0], frozenset(accepting), edges)


def parse_rocq(path: Path) -> Graph:
    text = path.read_text(encoding="utf-8", errors="replace")
    marker = "Definition alarm_response_spot_backend : PBuchi alarm_response :="
    start = text.find(marker)
    if start < 0:
        raise CheckError(f"could not find PBuchi definition in {path}")
    end = text.find("Definition alarm_spot_not_alarm", start)
    if end < 0:
        raise CheckError("could not find end of PBuchi definition")
    block = text[start:end]

    def integer(name):
        match = re.search(rf"\b{name}\s*:=\s*(\d+)", block)
        if not match:
            raise CheckError(f"could not parse {name}")
        return int(match.group(1))

    nstates = integer("pb_nstates")
    initial = str(integer("pb_init"))
    accepting_match = re.search(r"pb_accepting\s*:=\s*\[(.*?)\]", block, re.S)
    if not accepting_match:
        raise CheckError("could not parse Rocq accepting-state list")
    accepting = frozenset(re.findall(r"(\d+)%nat", accepting_match.group(1)))

    transition_re = re.compile(
        r"\{\|\s*pt_src\s*:=\s*(\d+)\s*;\s*"
        r"pt_label\s*:=\s*\[(.*?)\]\s*;\s*"
        r"pt_tgt\s*:=\s*(\d+)\s*\|\}",
        re.S,
    )
    literal_re = re.compile(r"\((LAct HANDLED|LNAct ALARM|LCLe alarm_clock 3|LUnch alarm_clock),\s*(true|false)\)")
    edges = {}
    seen = 0
    for source, labels, target in transition_re.findall(block):
        seen += 1
        literals = literal_re.findall(labels)
        if labels.strip() and not literals:
            raise CheckError(f"unparsed Rocq transition label: {labels!r}")
        residue = literal_re.sub("", labels).replace(";", "").strip()
        if residue:
            raise CheckError(f"unsupported Rocq label syntax: {residue!r}")
        conditions = []
        for literal in literals:
            if literal not in ROCq_ATOM:
                raise CheckError(f"unmapped Rocq literal {literal!r}")
            atom = ROCq_ATOM[literal]
            value = literal[1] == "true"
            conditions.append((atom, value))
        truth_set = frozenset(
            a for a in assignments()
            if all(dict(zip(ATOMS, a))[atom] == value for atom, value in conditions)
        )
        merge_edge(edges, source, target, truth_set)

    if seen == 0:
        raise CheckError("no Rocq transitions parsed")
    states = frozenset(str(i) for i in range(nstates))
    if initial not in states or not accepting.issubset(states):
        raise CheckError("Rocq initial or accepting state is outside pb_nstates")
    if any(s not in states or t not in states for s, t in edges):
        raise CheckError("Rocq transition references an undeclared state")
    return Graph(states, initial, accepting, edges)


def isomorphic(dot: Graph, rocq: Graph):
    if len(dot.states) != len(rocq.states):
        return None
    rocq_states = sorted(rocq.states)
    dot_states = sorted(dot.states)
    for image in itertools.permutations(dot_states):
        mapping = dict(zip(rocq_states, image))
        if mapping[rocq.initial] != dot.initial:
            continue
        if frozenset(mapping[s] for s in rocq.accepting) != dot.accepting:
            continue
        mapped_edges = {
            (mapping[source], mapping[target]): truth
            for (source, target), truth in rocq.edges.items()
        }
        if mapped_edges == dot.edges:
            return mapping
    return None


def self_test(dot: Graph, rocq: Graph):
    if isomorphic(dot, rocq) is None:
        raise CheckError("baseline mismatch; cannot run checker self-tests")
    bad_edges = dict(dot.edges)
    key = next(iter(bad_edges))
    bad_edges[key] = frozenset()
    changed_guard = Graph(dot.states, dot.initial, dot.accepting, bad_edges)
    if isomorphic(changed_guard, rocq) is not None:
        raise CheckError("self-test failed: changed guard was not detected")
    changed_acceptance = Graph(dot.states, dot.initial, frozenset(), dot.edges)
    if isomorphic(changed_acceptance, rocq) is not None:
        raise CheckError("self-test failed: changed acceptance was not detected")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dot", type=Path, default=DOT_PATH)
    parser.add_argument("--rocq", type=Path, default=ROCQ_PATH)
    parser.add_argument("--self-test", action="store_true", help="also verify mutated guard/acceptance are rejected")
    args = parser.parse_args()

    try:
        dot = parse_dot(args.dot)
        rocq = parse_rocq(args.rocq)
        mapping = isomorphic(dot, rocq)
        if mapping is None:
            raise CheckError("DOT graph and Rocq PBuchi record differ in states, acceptance, or guards")
        if args.self_test:
            self_test(dot, rocq)
        print(f"PASS: {len(dot.states)} states; initial={dot.initial}; accepting={sorted(dot.accepting)}")
        print(f"PASS: {len(dot.edges)} DOT source/target pairs match {len(rocq.edges)} Rocq source/target pairs modulo state renaming")
        print("PASS: transition guards have identical Boolean truth tables over the four declared propositions")
        print("Rocq-to-DOT state map: " + ", ".join(f"{k}->{v}" for k, v in sorted(mapping.items())))
        if args.self_test:
            print("PASS: self-tests reject a changed guard and a changed accepting set")
        print("LIMIT: executable syntax/graph consistency check only; Spot regeneration, importer correctness, and semantic language equivalence are not established by this script")
    except (OSError, CheckError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
