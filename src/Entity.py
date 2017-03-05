#!/usr/bin/env python3

################################################################################
#                                    Entity                                    #
################################################################################

class Entity:
    def __init__(self, *predicates):
        self.predicates = set()
        self.predicates.add(*predicates)
        self.used = False
        
    def merge(self, e):
        for p in e.predicates:
            p.entity = self
        self.predicates.update(e.predicates)
        del e

    def solve(self):
        if self.used:
            return
        self.used = True
        for p in self.predicates():
            p.direct_solve()
        self.used = False
            
    def check_results(self):
        pass
    
    def get_result(self, predicate):
        self.check_results()
        #result = None
        # for p in self.predicates:
        #     for r in p.results:
        #         result = min(result, r.result_for(predicate)) # result_for(permits to include equivalence)
        # if result == None:
        #     result = Result(...)#default value result.
        return predicate.get_shortest_result()

    def __str__(self):
        result = "Entity Containing :%s"
        return (result % (''.join(['\n' + str(p) for p in self.predicates])))

if __name__ == '__main__':
    pass
