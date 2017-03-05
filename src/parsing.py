#!/usr/bin/env python3

import src.Predicates
import re

################################################################################
#                                File parser                                   #
################################################################################

regex = re.compile(' |\t|\n')

def clean_line(l):
    return regex.sub('', l.split('#')[0])

def is_empty_line(l):
    return(clean_line(l) == '')

def parse_rules(f):
    flag = False
    for line in f:
        if not is_empty_line(line):
            if not flag:
                flag = True
            parse_rule(clean_line(line))
        elif flag:
            return

def create_equivalence(p1, p2):
    p1.entity.merge(p2.entity)
    p1.defined_eqs.add(p2)
    p2.defined_eqs.add(p1)

def create_implication(p1, p2):
    p1.self_implies.add(p2)
    p2.is_implied_by.add(p1)

operators = {
    '+' : (2, src.Predicates.AndPredicate),
    '|' : (3, src.Predicates.OrPredicate),
    '^' : (4, src.Predicates.XorPredicate)
}

def create_predicate(s):
    p_depth = 0
    op_index = None
    i = 0
    for c in s:
        if c == '(':
            p_depth += 1
        elif c == ')':
            if p_depth == 0:
                raise Exception
            p_depth -= 1  
        elif (
            c in operators.keys() and p_depth == 0
            and (
                op_index == None
                or operators[c][0] > operators[s[op_index]][0]
            )
        ):
            op_index = i
        i += 1
    if p_depth > 0:
        raise Exception
    if op_index == None:



        if s[0] == '!':
            p = create_predicate(s[1:])
            return src.Predicates.NotPredicate(p)
        elif s[0] == '(' and s[-1] == ')':
            return create_predicate(s[1:][:-1])
        elif len(s) == 1 and s.isupper():
            return src.Predicates.AtomicPredicate(s)
        else:
            raise Exception
    else:
        p1 = create_predicate(s[:op_index])
        p2 = create_predicate(s[op_index + 1:])
        return operators[s[op_index]][1](p1, p2)
        
        
def parse_rule(l):
    if l.find('<=>') != -1:
        p = l.split('<=>')
        if len(p) == 2:
            p1 = create_predicate(p[0])
            p2 = create_predicate(p[1])
            create_equivalence(p1, p2)
        else:
            raise Exception
    elif l.find('=>') != -1:
        p = l.split('=>')
        if len(p) == 2:
            p1 = create_predicate(p[0])
            p2 = create_predicate(p[1])
            create_implication(p1, p2)
        else:
            raise Exception
    else:
        raise Exception
    

def parse_initial_facts(line):
    for letter in clean_line(line)[1:]:
        src.Predicates.AtomicPredicate(letter).set_initial_state()
                
def parse_queries(line):
    queries = set()
    for letter in clean_line(line)[1:]:
        queries.add(src.Predicates.AtomicPredicate(letter))
    return queries

def parse(filename):
    state = 0

    with open(filename) as f:
        for line in f:
            line = clean_line(line)
            if state == 0:  # empty lines before rules
                if not is_empty_line(line):
                    state = 1
            if state == 1:  # rules
                if line.startswith('?'):
                    state = 6
                elif line.startswith('='):
                    state = 3
                elif is_empty_line(line):
                    state = 2
                else:
                    parse_rule(line)
            if state == 2:  # empty lines after rules, before initial facts.
                if not is_empty_line(line):
                    state = 3
            if state == 3:  # initial facts
                parse_initial_facts(line)
                state = 4
                continue
            if state == 4:  #
                if not is_empty_line(line):
                    raise Exception("Syntax error in file")
                state = 5
            if state == 5:  # empty lines after rules, after initial facts, before queries
                if not is_empty_line(line):
                    state = 6
            if state == 6:  # queries
                queries = parse_queries(line)
                state = 7
                continue
            if state == 6:
                if not is_empty_line(line):
                    raise Exception("Syntax error in file")
    return queries


if __name__ == '__main__':
    pass
