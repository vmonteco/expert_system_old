#!/usr/bin/env python3

from src.LogicalValues import T, F, U, Undefined
import src.Entity
import src.Results
import src.Metaclasses

################################################################################
#                                  Predicates                                  #
################################################################################

############################# Predicate mainclasse #############################

class Predicate(metaclass=src.Metaclasses.MemoizeMetaclass):

    """
    Class to represent a predicate (A value expressed with other predicates in
    a tree structure.
    """

    def __init__(self, register=True):
        """
        Predicate __init__ method adds containers for :
        -predicates implied by the instance.
        -predicates implying the instance.
        -defined equivalences.
        -upcoming results.
        -parents predicates.
        
        It also adds the entity the instance represents, and init the
        equivalence links (if register args is True).
        """

        # related predicates
        self.self_implies = set()
        self.is_implied_by = set()
        self.contained_by = set()
        self.defined_eqs = set()
        
        self.entity = src.Entity.Entity(self)        
        self.results = set()

        # flags
        # self.used = False
        self.results_built = False

        if register:
            self.link_equivalents()
        
    def solve(self, verbose=False, debug=False):
        """
        This method solves the state of the current predicate by
        computing all the values of related predicates.

        It must avoid cyclic route that would lead to infinite loop.

        Here must be the expected returned format :

        solution :
        {
            'result' : ,
            'length' : ,
            'parent_solutions' : [solution1 [, solution2]]
        }
        """

        # if self.used:
        #     return None
        # self.used = True
        if self.results_built == False:
            self.make_results()
        solutions = [r.get_solution() for r in self.results if not r.used]
        T_res = None
        F_res = None
        U_res = None
        for s in solutions:
            if s == None:
                continue
            if s.result.value == T:
                if F_res != None:
                    raise Exception()
                elif T_res == None or s.length < T_res.length:
                    T_res = s
            elif s.result.value == F:
                if T_res != None:
                    raise Exception()
                elif F_res == None or s.length < F_res.length:
                    F_res = s
            elif s.result.value == U:
                if U_res == None or s.result.length < U_res.result.length:
                    U_res = s
        solution = (
            T_res or F_res or U_res
            or src.Results.DefaultResult(self).get_solution()
        )
        # self.used = False
        return solution

    
    def link_equivalents(self):

        """
        Finds equivalences amongst every predicate (logically deduced) and
        merges entities.
        """

        eqs = self.get_equivalents()
        for e in eqs:
            e.merge(self.entity)
    
    def get_equivalents(self):

        """
        Returns a set containing all the existing entities of Predicates that
        are equivalents with self.
        """

        result = set()
        for c in (
                NotPredicate,
                OrPredicate,
                XorPredicate,
                AndPredicate,
                AtomicPredicate
        ):
            for p in c.instances.values():
                if self.is_eq(p):
                    result.add(p.entity)
        return result

    
    def is_eq(self, pred):

        """
        Returns True if pred and self are equivalent, False otherwise.
        """

        # states an atomicpredicate can take.
        states = [F, T, U]
        cases_number = len(states)
        
        # make copies to compare each case :
        selfbis = self.make_bis()
        predbis = pred.make_bis()

        # Get every atomic predicates involved in copies :
        atompreds = selfbis.list_atomic_preds()
        atompreds.update(predbis.list_atomic_preds())

        # Making an iterable from it :
        atompreds = list(atompreds)

        result = True

        # looping through different states :
        for a in range(0, cases_number ** len(atompreds)):
            for p, i in zip(atompreds, range(0, len(atompreds))):
                state = (a // cases_number ** i) % cases_number
                p.value = states[state]
            result &= selfbis.get_direct_state() == predbis.get_direct_state()
        for p in atompreds:
            del AtomicPredicate.instances[frozenset((p.name,))]
        return result

    
    def list_atomic_preds(self):

        """
        returns a set containing all the AtomicPredicates contained by self.
        """

        result = set()
        if isinstance(self, AtomicPredicate):
            result.update((self,))
        elif (isinstance(self, OrPredicate) or isinstance(self, AndPredicate)
              or isinstance(self, XorPredicate)):
            result.update(self.p1.list_atomic_preds())
            result.update(self.p2.list_atomic_preds())
        elif isinstance(self, NotPredicate):
            result.update(self.p.list_atomic_preds())
        return result

    def make_results(self):

        """
        Makes results.
        """
        
        self.make_equivalences_results()
        self.make_direct_implication_results()
        self.make_indirect_implication_results()
        self.make_parent_results()
        if not isinstance(self, AtomicPredicate):
            self.make_child_results()
        self.results_built = True


    def make_equivalences_results(self):

        """
        Make results related to equivalences.
        """

        for pred in self.entity.predicates :
            if not pred is self:
                if pred in self.defined_eqs:
                    self.results.add(DefinedEquivalenceResult(self, pred))
                else:
                    self.results.add(DeducedEquivalenceResult(self, pred))

    
    def make_direct_implication_results(self):

        """
        Make results related to direct implications.
        """

        for pred in self.is_implied_by:
            self.results.add(src.Results.ImplicationResult(pred=self, srcpred=pred))

            
    def make_indirect_implication_results(self):

        """
        Make results related to indirect implications, ((A->B)->(!B->!A)).
        """

        for pred in self.self_implies:
            self.results.add(src.Results.IndirectImplicationResult(pred=self, srcpred=pred))
            
    
    def make_parent_results(self):

        """
        Make results related to predicates containing the instance.
        """
        
        for pred in self.contained_by:
            self.results.add(pred.parent_result_class(self, pred))
            

    def make_child_results(self):

        """
        Make results related to contained predicates (For Parent predicates).
        """

        self.results.add(src.Results.ChildResult(self))

    
    def make_bis(self):

        """
        Used to make a copy of self, the AtomicPredicates names change ('-bis'
        at their end.
        """

        raise NotImplementedError

    
############################# Predicate subclasses #############################

# "Leaf" predicate - AtomicPredicate

class AtomicPredicate(Predicate):
    def __init__(self, name, *args, **kwargs):
        self.name = name
        super().__init__(*args, **kwargs)
        
    def make_bis(self):
        return AtomicPredicate(self.name + "-bis", register=False)

    def set_initial_state(self, state=T):
        self.results.add(src.Results.DefinedResult(self, value=T))
    
    def get_direct_state(self):
        return self.value

    def __str__(self):
        return self.name
    
# non-atomic predicates

class NotPredicate(Predicate):#, metaclass=MemoizeNotMetaclass):
    
    parent_result_class = src.Results.NotParentResult

    values_table = {
        U : U,
        Undefined : Undefined,
        F : T,
        T : F
    }

    def __init__(self, pred, *args, **kwargs):
        self.p = pred
        self.p.contained_by.add(self)
        super().__init__(*args, **kwargs)
    
    def make_bis(self):
        return NotPredicate(self.p.make_bis(), register=False)

    def get_state(self):
        return self.values_table[self.p.solve()]

    def get_direct_state(self):
        return self.values_table[self.p.get_direct_state()]

    def __str__(self):
        if (isinstance(self.p, AtomicPredicate)
            or isinstance(self.p, NotPredicate)):
            p = str(self.p)
        else:
            p = "(%s)" % self.p
        return ("!%s" % (p,))

    
class ParentPredicate(Predicate):

    def __init__(self, pred1, pred2, *args, **kwargs):
        self.p1 = pred1
        self.p2 = pred2
        self.p1.contained_by.add(self)
        self.p2.contained_by.add(self)
        super().__init__(*args, **kwargs)

    def make_bis(self):
        p1_bis = self.p1.make_bis()
        p2_bis = self.p2.make_bis()
        return type(self)(p1_bis, p2_bis, register = False)

    def get_state(self):
        return self.values_table[
            (
                self.p1.solve(),
                self.p2.solve()
            )
        ]
    
    def get_direct_state(self):
        return self.values_table[
            (
                self.p1.get_direct_state(),
                self.p2.get_direct_state()
            )
        ]

    def __str__(self):
        if (isinstance(self.p1, AtomicPredicate) or
            isinstance(self.p1, NotPredicate)):
            p1 = str(self.p1)
        else:
            p1 = "(%s)" % self.p1
        if (isinstance(self.p2, AtomicPredicate)
            or isinstance(self.p2, NotPredicate)):
            p2 = str(self.p2)
        else:
            p2 = "(%s)" % self.p2
        return ("%s %s %s" % (p1, self.op, p2))
    

class OrPredicate(ParentPredicate):

    parent_result_class = src.Results.OrParentResult

    values_table = {
        (Undefined, Undefined) : Undefined,
        (Undefined, U) : U,
        (Undefined, F) : Undefined,
        (Undefined, T) : T,
        (U, Undefined) : U,
        (U, U) : U,
        (U, F) : U,
        (U, T) : T,
        (F, Undefined) : Undefined,
        (F, U) : U,
        (F, F) : F,
        (F, T) : T,
        (T, Undefined) : T,
        (T, U) : T,
        (T, F) : T,
        (T, T) : T
    }

    op = '+'
        
class AndPredicate(ParentPredicate):

    parent_result_class = src.Results.AndParentResult

    values_table = {
        (Undefined, Undefined) : Undefined,
        (Undefined, U) : Undefined,
        (Undefined, F) : F,
        (Undefined, T) : Undefined,
        (U, Undefined) : Undefined,
        (U, U) : U,
        (U, F) : F,
        (U, T) : U,
        (F, Undefined) : F,
        (F, U) : F,
        (F, F) : F,
        (F, T) : F,
        (T, Undefined) : Undefined,
        (T, U) : U,
        (T, F) : F,
        (T, T) : T
    }

    op = '|'
    
class XorPredicate(ParentPredicate):

    parent_result_class = src.Results.XorParentResult

    values_table = {
        (Undefined, Undefined) : Undefined,
        (Undefined, U) : Undefined,
        (Undefined, F) : Undefined,
        (Undefined, T) : Undefined,
        (U, Undefined) : Undefined,
        (U, U) : U,
        (U, F) : U,
        (U, T) : U,
        (F, Undefined) : Undefined,
        (F, U) : U,
        (F, F) : F,
        (F, T) : T,
        (T, Undefined) : Undefined,
        (T, U) : U,
        (T, F) : T,
        (T, T) : F
    }

    op = '^'


if __name__ == '__main__':
    pass
