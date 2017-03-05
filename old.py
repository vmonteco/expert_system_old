#!/usr/bin/env python3

import re
import argparse

################################################################################
#                               Logical values                                 #
################################################################################

class LogicalValue:
    def __init__(self, s):
        self.s = s

    def __str__(self):
        return self.s

Undefined = LogicalValue("UNDEFINED")
T = LogicalValue("TRUE")
F = LogicalValue("FALSE")
U = LogicalValue("UNDETERMINED")


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

################################################################################
#                                 Metaclasses                                  #
################################################################################

class MemoizeMetaclass(type):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.instances = {}
    
    def __call__(cls, *args, **kwargs):
        if "register" in kwargs.keys():
            register = kwargs["register"]
            #del kwargs["register"]
        else:
            register = True
        key = frozenset(args)
        if key in cls.instances.keys():
            return cls.instances[key]
        obj = super().__call__(*args, **kwargs)
        if register or cls == AtomicPredicate:
            cls.instances[key] = obj
        return obj


class MemoizeNotMetaclass(MemoizeMetaclass):
    
    def __call__(cls, *args, **kwargs):
        if "register" in kwargs.keys():
            register = kwargs["register"]
            #del kwargs["register"]
        else:
            register = True
        key = frozenset(args)
        if key in cls.instances.keys():
            return cls.instances[key]
        if type(args[0]) == cls:
            obj = args[0].p
        else:
            obj = super().__call__(*args, **kwargs)
        if register:
            cls.instances[key] = obj
        return obj


################################################################################
#                                Result classes                                #
################################################################################

################################## Base Result #################################

class Result:#(metaclass=ResultMemoizeMetaclass):
    """
    Base result class.
    """

    def __init__(self, pred, value=Undefined):
        """
        pred argument is the predicate the instance permits the deduction.
        
        Other arguments (parent predicate, value...) may be added with
        subclassing.

        Results values aren't determined by default, to be solved, the solve()
        method must be called to do so.
        """
        self.used = False
        self.value = value
        self.pred = pred
        self.displayed = False
        
    def __len__(self):
        """
        Depending of the kind of predicate, the __len__ method returns the
        length of the shortest reasonning that permits to deduce the instance
        value.
        
        It's 0 if the result comes from an end (default value, arbitrary
        definition in parsed file...).
        
        If it's not an end (parent predicate, implication, predicate...), the
        __len__ method uses the source predicate's (parent, premise in
        implication...) find_shortest_reasonning method and returns the
        returned's result + 1.
        """
        #if self.length != None:
        #    return length
        reasonning_to_follow = self.srcpred.get_reasonning_to_follow()
        if reasonning_to_follow == None:
            return 0
        srclen = len(reasonning_to_follow)
        self.length = srclen + 1
        return self.length

    def get_characteristics(self):
        print(self, type(self))
        reasonning_to_follow = self.srcpred.get_reasonning_to_follow()
        print(reasonning_to_follow)
        if reasonning_to_follow == None:
            return None
        return {
            'result' : self,
            'length' : (
                reasonning_to_follow['length']
                + 1
            )
        }
    
    def solve(self, verbose=False, debug=False):
        """
        If the result's value isn't determined, the solve method deduces it,
        sets the determined attribute to True, sets the found value and
        returns it.

        ??? Should a flag be used to avoid repeating the displaying of an
        already displayed result in case of verbose output. ???

        This method calls the solvesubmethod method.

        It also handles the used attribute before calling it.
        """

        if self.used:
            return Undefined
        #self.value = Undefined
        self.used = True
        if self.value == Undefined or self.value == U:
            self.value = self.solvesubmethod(verbose, debug)
        self.used = False
        return self.value

    def make_display_text(self, verbose, debug):
        if self.displayed == True:
            return ''
        self.displayed == True
        if hasattr(self, 'twinpred'):
            res = "{}\n\n{}\n\n{}".format(
                self.srcpred.make_display_text(
                    verbose,
                    debug
                ).replace('\n', '\n  '),
                self.twinpred.make_display_text(
                    verbose,
                    debug
                ).replace('\n', '\n  '),
                str(self)
            )
        else:
            res = "{}\n\n{}".format(
                self.srcpred.make_display_text(
                    verbose,
                    debug
                ).replace('\n', '\n  '),
                str(self)
            )
        return res
        
    def solvesubmethod(self, verbose, debug):
        """
        This method must compute and return the
        result's value.
        """
        raise NotImplementedError

    def __str__(self):
        raise NotImplementedError

    
    
############################# Containing relations #############################

class ParentResult(Result):
    """
    Result subclass to represent a result deduced from a parent predicate.
    (e.g.: We can deduce that A is True from !A being False).
    """

    def __init__(self, pred, srcpred):
        super().__init__(pred)
        self.srcpred = srcpred
        if (isinstance(self, NotParentResult)
            or (self.srcpred.p1 is self.srcpred.p2
                and self.srcpred.p1 is self)):
            self.twinpred = None
        elif not self.srcpred.p1 is self:
            self.twinpred = self.srcpred.p1
        elif not self.srcpred.p2 is self:
            self.twinpred = self.srcpred.p2


    def value_from_srcpred(self):
        """
        get the value the instance should have from the source predicate.
        """

        key = (
            self.srcpred.solve(),
            self.twinpred.solve() if self.twinpred else None
        )
        if key in self.error_cases:
            raise IncoherenceError
        return self.conv_table[key]
        
    def solvesubmethod(self, verbose, debug):
        if self.value != Undefined and self.value != U:
            return self.value
        self.value = self.value_from_srcpred()
        return self.value

            
    def __len__(self):
        
        #if self.length != None:
        #    return self.length
        reasonning_to_follow = self.srcpred.get_reasonning_to_follow()
        if reasonning_to_follow == None:
            return 0
        srclen = len(reasonning_to_follow)
        if self.twinpred != None:
            twinlen = len(twinpred.get_reasonning_to_follow())
            self.length = max(srclen, twinlen) + 1
        else: # Not case
            self.length = srclen + 1
        return self.length

    def __str__(self):
        res = "{srcpred} is {srcval}, therefore {pred} is {val}"
        vals['srcpred'] = self.srcpred
        vals['srcval'] = self.srcpred.solve()
        vals['pred'] = self.pred
        vals['val'] = self.solve()
        if not (isinstance(self.pred, NotPredicate)
                or self.srcpred.p1 is self.srcpred.p2):
            if self.srcpred.p1 is self:
                vals['twinpred'] = self.srcpred.p2
            else:
                vals['twinpred'] = self.srcpred.p1
            vals['twinval'] = twinpred.solve()
            res = "{twinpred} is {twinval} and " + res
        return res.format(**vals)

    
        
class NotParentResult(ParentResult):
    """
    ParentResult subclass for NOT particular case.
    """

    conversion_table = {
        (Undefined, None) : Undefined,
        (U, None) : U,
        (F, None) : T,
        (T, None) : F
    }

    #def __len__(self):
    #    return super(Result, self).__len__()
    
    def value_from_srcpred(self):
        return self.conversion_table[self.srcpred.solve()]

    
class AndParentResult(ParentResult):
    """
    ParentResult subclass for AND particular case.
    """
    # (src, twin)
    
    error_cases = (
        (T, F),
    )

    conv_table = {
        (Undefined, Undefined) : Undefined,
        (Undefined, U) : Undefined,
        (Undefined, F) : Undefined,
        (Undefined, T) : Undefined,
        (Undefined, None) : Undefined,
        (U, Undefined) : Undefined,
        (U, U) : U,
        (U, F) : U,
        (U, T) : U,
        (U, None) : U,
        (F, Undefined) : Undefined,
        (F, U) : U,
        (F, F) : U,
        (F, T) : F,
        (F, None) : F,
        (T, Undefined) : Undefined,
        (T, U) : T,
        (T, T) : T,
        (T, None) : T,
    }

    
class OrParentResult(ParentResult):
    """
    ParentResult subclass for OR particular case.
    """

    # (src, twin)
    
    error_cases = (
        (F, T),
    )

    
    conv_table = {
        (Undefined, Undefined) : Undefined,
        (Undefined, U) : Undefined,
        (Undefined, F) : Undefined,
        (Undefined, T) : Undefined,
        (Undefined, None) : Undefined,
        (U, Undefined) : Undefined,
        (U, U) : U,
        (U, F) : U,
        (U, T) : T,
        (U, None) : U,
        (F, Undefined) : Undefined,
        (F, U) : F,
        (F, F) : F,
        (F, None) : F,
        (T, Undefined) : Undefined,
        (T, U) : U,
        (T, F) : T,
        (T, T) : U,
        (T, None) : T,
    }


class XorParentResult(ParentResult):
    """
    ParentResult subclass for XOR particular case.
    """

    # (src, twin)

    error_cases = (
        
    )
    
    conv_table = {
        (Undefined, Undefined) : Undefined,
        (Undefined, U) : Undefined,
        (Undefined, F) : Undefined,
        (Undefined, T) : Undefined,
        (Undefined, None) : Undefined,
        (U, Undefined) : Undefined,
        (U, U) : U,
        (U, F) : U,
        (U, T) : U,
        (U, None) : U,
        (F, Undefined) : Undefined,
        (F, U) : U,
        (F, F) : F,
        (F, T) : T,
        (T, Undefined) : Undefined,
        (T, U) : U,
        (T, F) : T,
        (T, T) : F,
    }

    
class ChildResult(Result):
    """
    Result subclass to solve a composed predicate from its childs.
    """
    
    def __init__(self, pred):
        super().__init__(pred)
        self.atomic_childs = self.pred.list_atomic_preds()
        
    def solvesubmethod(self, verbose, debug):
        if self.value == F or self.value == T:
            return self.value
        for a in self.atomic_childs:
            a.solve()
        self.value = self.pred.get_state()

    def __str__(self):
        res = ''.join([
            '{pred} is {value}, '.format(pred=pred, value=pred.solve())
            for pred in self.atomic_childs
        ])
        res = res + ", therefore {pred} is {predval}".format(
            pref=self.pred, predval=self.pred.get_state()
        )
        return res


####################### Equivalences and implications ##########################
    
class EquivalenceResult(Result):
    """
    Class to represent a result from an equivalence.
    """

    def __init__(self, pred, srcpred):
        super().__init__(pred)
        self.srcpred = srcpred
    
    def solvesubmethod(self, verbose, debug):
        if self.value != None and self.value != U:
            return self.value
        srcstate = self.srcpred.solve(verbose, debug)
        self.value = srcstate
        return self.value
        
    
    def __str__(self):
        res = ("{srcpred} <=> {pred} ({reason}) and {srcpred} is {srcval},"
               "therefore {pred} is {val}.")
        vals = {}
        val['srcpred'] = self.srcpred
        val['pred'] = self.pred
        val['srcval'] = self.srcpred.solve()
        val['val'] = self.pred.solve()
        val['reason'] = self.reason
        return res.format(**vals)
    
    
class DeducedEquivalenceResult(EquivalenceResult):
    """
    EquivalenceResult subclass for cases where the equivalence is logically
    deduced.
    """

    reason = "logically deduced"

    
class DefinedEquivalenceResult(EquivalenceResult):
    """
    EquivalenceResult subclass for cases where the equivalence is defined in
    the parsed file.
    """

    reason = "previously defined"

    
class ImplicationResult(Result):
    """
    Result subclass to represent result deduced from an implication.
    """

    values = {
        T : T,
        U : U,
        F : U,
        Undefined : Undefined
    }
    
    def __init__(self, pred, srcpred):
        super().__init__(pred)
        self.srcpred = srcpred

    def value_from_srcpred(self, srcstate):
        return self.values[srcstate]
    
    def solvesubmethod(self, verbose, debug):
        if self.value != None and self.value != Undefined and self.value != U:
            return self.value
        srcstate = self.srcpred.solve(verbose, debug)
        self.value = self.value_from_srcpred(srcstate)
        return self.value
    
    def __str__(self):
        res = ("{srcpred} => {pred} and {srcpred} is {srcval}, therefore {pred}"
               " is {val}.")
        vals = {}
        vals['srcpred'] = self.srcpred
        vals['pred'] = self.pred
        vals['srcval'] = self.srcpred.solve()
        vals['val'] = self.value
        #vals['reason'] = self.reason
        return res.format(**vals)

    
class IndirectImplicationResult(ImplicationResult):
    """
    Result subclass to represent result deduced from a deduced implication.

    In this case, pred must be the deduced predicate but the premisse of
    the implication we work on, therefore, the implication will be :
    pred -> srcpred.
    """

    values = {
        T : U,
        U : U,
        F : F,
        Undefined : Undefined
    }
            
    def __str__(self):
        res = ("{pred} => {srcpred} and {srcpred} is {srcval}, therefore {pred} "
               "is {val}.")
        vals = {}
        vals['srcpred'] = self.srcpred
        vals['pred'] = self.pred
        vals['srcval'] = self.srcpred.solve()
        vals['val'] = self.value
        #vals['reason'] = self.reason
        return res.format(**vals)




################################################################################
#                                  Predicates                                  #
################################################################################

############################# Predicate mainclasse #############################

class Predicate(metaclass=MemoizeMetaclass):

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

        self.self_implies = set()
        self.is_implied_by = set()
        self.contained_by = set()
        self.results = set()
        self.defined_eqs = set()
        self.entity = Entity(self)
        self.state = Undefined
        self.results_built = False
        self.used = False
        self.displayed = False
        self.reasonning_selection = False
        if register:
            self.link_equivalents()

            
    def solve(self, verbose=False, debug=False):

        """
        Entrypoint to solve a predicate's state.
        """

        # if self.entity.used :
        #     return Undefined

        # Make results :
        if self.used:
            return Undefined
        #print("solving", self)
        self.used = True
        
        # Make results :
        if self.results_built == False:
            self.make_results()
            
        # Solve results (while no undefined result?):
        #r_to_solve = [r for r in self.results if r.value == Undefined]
        if debug:
            print("Trying to solve %s" % self)
            #while r_to_solve:
        for r in self.results:
            r.solve(verbose, debug)
            #r_to_solve = [r for r in self.results if r.value == Undefined]
            
        # Check results :
        #elf.check_results()
        solution = self.get_reasonning_to_follow()

        if solution == None:
            self.value = Undefined
        else:
            self.value = solution['result'].solve()
        self.used = False
        return self.value

    
    


    def make_display_text(self, verbose, debug):
        if self.displayed == True:
            return ''
        self.displayed = True
        self.solve()
        if verbose :
            r = self.get_reasonning_to_follow()
            r_display_text = r['result'].make_display_text(
                verbose,
                debug
            )
            res = "  {}\nTherefore : {} is {}.".format(
                r_display_text.replace('\n', '\n  '), str(self), str(self.solve())
            )
        elif debug:
            r_display_text = '\n\n'.join(
                [r.make_display_text(verbose, debug) for r in self.results]
            )
            res = "{}\nTherefore : {} is {}.".format(
                r_display_text.replace('\n', '\n  '), str(self), str(self.solve())
            )
        else:
            res = "{} is {}.".format(str(self), str(self.solve()))
        return res
            

    def check_results(self):

        """
        An exception should be raised if :
        There are both a True result and a False result.
        """

        if ([r for r in self.results if r.value == F]
            and [r for r in self.results if r.value == T]):
            raise IncoherenceError()


    def print_details(self):
        print("-%s\nImplied by :" % (str(self),))
        for p in self.is_implied_by:
            print(p)
        print("Implying :")
        for p in self.self_implies:
            print(p)
        print("defined_eqs:")
        for p in self.defined_eqs:
            print(p)
        print("contained by :")
        for p in self.contained_by:
            print(p)
        print("equivalences :")
        for p in self.entity.predicates:
            print(p)

        
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
            self.results.add(ImplicationResult(pred=self, srcpred=pred))

            
    def make_indirect_implication_results(self):

        """
        Make results related to indirect implications, ((A->B)->(!B->!A)).
        """

        for pred in self.self_implies:
            self.results.add(IndirectImplicationResult(pred=self, srcpred=pred))
            
    
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

        self.results.add(ChildResult(self))
        

    def get_reasonning_to_follow(self):
        if self.reasonning_selection:
            return None
        self.solve()
        self.reasonning_selection = True
        T_res = None
        F_res = None
        U_res = None
        results = [r.get_characteristics() for r in self.results]
        print(results)
        print("result : ", results[-1])
        for r in results:
            if r == None:
                continue
            if r['result'].value == T:
                if F_res != None:
                    raise Exception()
                elif T_res == None or r['length'] < T_res['length']:
                    T_res = r
            if r['result'].value == F:
                if T_res != None:
                    raise Exception()
                elif F_res == None or r['length'] < F_res['length']:
                    F_res = r
            if r['result'].value == U:
                if U_res == None or r['length'] < U_res['length']:
                    U_res = r
        result = T_res or F_res or U_res or {'result' : DefaultResult(self), 'length' : 0}
        result['length'] += 1
        self.reasonning_selection = False
        return result
        
    # def get_reasonning_to_follow(self):

    #     """
    #     Used to get the best result to follow (T, F > U), and the shorter the
    #     better.

    #     In some cases, a result is created and returned (DefaultResult for
    #     instance).
    #     """

    #     default = DefaultResult(self)
    #     result = default
    #     if self.reasonning_selection:
    #         return None
    #     self.reasonning_selection = True
    #     #print(self, self.results)
    #     for r in list(self.results):
    #         if len(r) == 0:
    #             #print(self, r)
    #             continue
    #         if (result.value in (T, F)
    #             and r.value in (T, F)
    #             and not isinstance(result, DefaultResult)
    #             and r.value != result.value
    #         ):
    #             raise IncoherenceError(result, r)
    #         if (result == default):
    #             if r.value in (T, F, U):
    #                 result = r
    #         else:
    #             if result.value == U and r.value in (T, F):
    #                 result = r
    #             elif len(result) > len(r):
    #                 result = r
    #     self.reasonning_selection = False
    #     return result


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
                p.state = states[state]
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

    
    def make_bis(self):

        """
        Used to make a copy of self, the AtomicPredicates names change ('-bis'
        at their end.
        """

        raise NotImplementedError

    
    def get_state(self):

        """
        Returns the current instance's state (T, F, U, Undefined).

        ??? From a state attribute or from the best result found. ???
        How to make is_eq then? 
        Or make two different methods?
        """

        raise NotImplementedError

    
    def get_direct_state(self):

        """
        Returns the current instance's state (T, F, U, Undefined) from the
        instance's attribute.
        """

        raise NotImplementedError

    
    def get_state_from_results(self):

        """
        Return the current instance's state from the computed results.
        """

        pass
    
    def __contains__(self, pred):

        """
        Returns True if self contains or is pred, False otherwise.
        """

        raise NotImplementedError
    
    def __str__(self):

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
        self.results.add(DefinedResult(self, value=T))
    
    def get_direct_state(self):
        return self.state

    def __str__(self):
        return self.name
    
# non-atomic predicates

class NotPredicate(Predicate):#, metaclass=MemoizeNotMetaclass):
    
    parent_result_class = NotParentResult

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
        return self.values_table[self.state]

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

    parent_result_class = OrParentResult

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

    parent_result_class = AndParentResult

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

    parent_result_class = XorParentResult

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

################################################################################
#                                    Result                                    #
################################################################################
    
################################## End Results #################################


class DefaultResult(Result):

    """
    Result subclass to represent a result deduced from the predicate's default
    value (no other result to override it).
    It should only appear if no other result is registered, otherwise no need
    to register it in first place (it can also make the solving more
    complicated).
    """

    def __init__(self, pred, value=F):
        super().__init__(pred, value=value)
        
    def __len__(self):
        return 1

    def make_display_text(self, verbose, debug):
        if self.displayed == True:
            return ''
        self.displayed = True
        return str(self)

    def solvesubmethod(self):
        return self.value
    
    def __str__(self):
        return  "{pred}'s default value is {val}".format(
            pred=self.pred,
            val=self.value
        )

    
class DefinedResult(Result):

    """
    Result subclass to represent a result defined in the parsed file.
    (It should be created during the parsing).
    """

    def __init__(self, pred, value):
        super().__init__(pred, value=value)

    def __len__(self):
        return 1

    def make_display_text(self, verbose, debug):
        if self.displayed == True:
            return ''
        self.displayed = True
        return str(self)

    def solvesubmethod(self):
        return self.value

    def get_characteristics(self):
        return {
            'result' : self,
            'length' : 0,
        }
    
    def __str__(self):
        return  "{pred} was defined as {val}".format(
            pred=self.pred,
            val=self.value
        )


# ################################# Child Results ################################

# class ChildResult(Result):

#     """
#     For Parent results.
#     """

#     def solve(self):
#         if self.state in (T, F):
#             return self.state
#         p1state = self.p1.solve()
#         p2state = self.p2.solve()
#         self.state = self.values_table[(p1state, p2state)]
#         return self.state

#     def __str__(self):
#         res = ("{p1} is {p1state} and {p2} is {p2state}, therefore {pred} is "
#         "{state}")
#         return res.format(
#             pred=pred,
#             p1=self.p1,
#             p2=self.p2,
#             state=self.solve(),
#             p1state=self.p1.solve(),
#             p2state=self.p2.solve()
#         )

    
# class NotChildResult(Result):

#     """
#     For Not case.
#     """
    
#     predicate_class = NotPredicate
    
#     def solve(self):
#         if self.state in (T, F):
#             return self.state
#         pstate = self.p.solve()
#         self.state = self.values_table[pstate]
#         return self.state

#     def __str__(self):
#         res = "{p} is {pstate}, therefore {pred} is {state}"
#         return res.format(
#             pred=pred,
#             p=self.p,
#             state=self.solve(),
#             pstate=self.p.solve(),
#         )
    
    
# class OrChildResult(ChildResult):
    
#     predicate_class = OrPredicate
    

# class AndChildResult(ChildResult):
    
#     predicate_class = AndPredicate
    


# class XorChildResult(ChildResult):

#     predicate_class = XorPredicate

    
################################################################################
#                                File parser                                   #
################################################################################

regex = re.compile(' |\t|\n')

def clean_line(l):
    #print(l)
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
    #'!' : 1,
    '+' : (2, AndPredicate),
    '|' : (3, OrPredicate),
    '^' : (4, XorPredicate)
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
            return NotPredicate(p)
        elif s[0] == '(' and s[-1] == ')':
            return create_predicate(s[1:][:-1])
        elif len(s) == 1 and s.isupper():
            return AtomicPredicate(s)
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
        AtomicPredicate(letter).set_initial_state()
                
def parse_queries(line):
    queries = set()
    for letter in clean_line(line)[1:]:
        queries.add(AtomicPredicate(letter))
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


################################################################################
#                              Command parser                                  #
################################################################################

def make_parser():
    parser = argparse.ArgumentParser(description='Modelize logic.')
    subparsers = parser.add_subparsers(dest="subcommand")
    subparsers.required = True
    test_subparser = subparsers.add_parser('test')
    solver_subparser = subparsers.add_parser('run')
    solver_subparser.add_argument(
        '-v', '--verbose', help='enable verbose mode.', action='store_true'
    )
    solver_subparser.add_argument(
        '-d', '--debug', help='enable debug mode.', action='store_true'
    )
    solver_subparser.add_argument(
        'filename', type=str,
        help='filename containing the instructions to process.'
    )
    return parser

    
def test():
    #unittest.main(module='tests.tests')
    pass



def solve(queries, verbose, debug):
    for q in queries:
        q.solve()
        print(q.make_display_text(verbose, debug))

# def print_details():
#     for c in (
#             AtomicPredicate,
#             NotPredicate,
#             OrPredicate,
#             AndPredicate,
#             XorPredicate
#     ):
#         for p in c.instances.values():
#             p.print_details()
#             print('')
        
def run(filename, verbose, debug):
    queries = parse(filename)
    #if verbose:
    #    print_details()
    #    #print(' '.join([q.name for q in queries]))
    solve(queries, verbose, debug)
        

################################################################################
#                                Entrypoint                                    #
################################################################################    
    
if __name__ == '__main__':
    parser = make_parser()
    args = parser.parse_args()
    if args.subcommand == 'test':
        sys.argv = sys.argv[:1:]
        test()
    else:
        run(args.filename, verbose=args.verbose, debug=args.debug)
        
