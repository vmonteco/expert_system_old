#!/usr/bin/env python3

from src.LogicalValues import T, F, U, Undefined
import src.Solution

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

        
    def get_solution(self):
        """
        This method generates the reasonning (Solution instance) to deduce the
        current predicate's state.
        It implementation may depend of the kind of result and the number of
        parent results may vary.
        """
        self.solve()
        solution = src.Solution.Solution(self, self.srcpred.solve())
        return solution
            
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
            return self.value
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

        src_sol = self.srcpred.solve()
        print(" Result- ", self.pred, self.srcpred, self.srcpred.results, src_sol)
        #print("test", self.srcpred, src_sol)
        twin_sol = self.twinpred.get_determined_solution() if self.twinpred else None
        src_val = src_sol.result.value if src_sol else Undefined
        twin_val = twin_sol.result.value if twin_sol else Undefined
        print(self.pred, src_sol, src_val, twin_sol, twin_val)
        #print(type(self))
        key = (src_val, twin_val)
        #self.srcpred.solve().result.value or None,
        #    self.twinpred.solve().result.value if self.twinpred else None
        #)
        if key in self.error_cases:
            raise IncoherenceError
        res = self.conv_table[key]
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
        res = "{srcpred} is {srcval}" #, therefore {pred} is {val}"
        vals = {}
        vals['srcpred'] = self.srcpred
        vals['srcval'] = self.srcpred.solve().result.value
        #vals['pred'] = self.pred
        #vals['val'] = self.solve()
        if not (isinstance(self.srcpred, src.Predicates.NotPredicate)
                or self.srcpred.p1 is self.srcpred.p2):
            if self.srcpred.p1 is self:
                vals['twinpred'] = self.srcpred.p2
            else:
                vals['twinpred'] = self.srcpred.p1
            vals['twinval'] = vals['twinpred'].solve().result.value
            res = "{twinpred} is {twinval} and " + res
        return res.format(**vals)

    
        
class NotParentResult(ParentResult):
    """
    ParentResult subclass for NOT particular case.
    """

    conversion_table = {
        Undefined : Undefined,
        U : U,
        F : T,
        T : F
    }

    #def __len__(self):
    #    return super(Result, self).__len__()
    
    def value_from_srcpred(self):
        return self.conversion_table[self.srcpred.solve().result.value]

    
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

    def get_solution(self):
        return src.Solution.Solution(self, *[a.solve() for a in self.pred.list_atomic_preds()])
        
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
        F : Undefined,
        Undefined : Undefined,
        None : Undefined
    }
    
    def __init__(self, pred, srcpred):
        super().__init__(pred)
        self.srcpred = srcpred

    def value_from_srcpred(self, srcstate):
        return self.values[srcstate.result.value]
    
    def solvesubmethod(self, verbose, debug):
        if self.value != None and self.value != Undefined and self.value != U:
            return self.value
        srcstate = self.srcpred.solve(verbose, debug)
        if srcstate == None:
            return Undefined
        self.value = self.value_from_srcpred(srcstate)
        return self.value
    
    def __str__(self):
        res = ("{srcpred} => {pred} and {srcpred} is {srcval}")#, therefore {pred}"
        #" is {val}.")
        vals = {}
        vals['srcpred'] = self.srcpred
        vals['pred'] = self.pred
        vals['srcval'] = self.srcpred.solve().result.value
        #vals['val'] = self.value
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
        T : Undefined,
        U : U,
        F : F,
        Undefined : Undefined,
        None : Undefined
    }
            
    def __str__(self):
        res = ("{pred} => {srcpred} and {srcpred} is {srcval}, therefore {pred} "
               "is {val}.")
        vals = {}
        vals['srcpred'] = self.srcpred
        vals['pred'] = self.pred
        vals['srcval'] = self.srcpred.solve().result.val
        vals['val'] = self.value
        #vals['reason'] = self.reason
        return res.format(**vals)

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

    def get_solution(self):
        solution = src.Solution.Solution(self)
        return solution
        
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

    def get_solution(self):
        solution = src.Solution.Solution(self)
        return solution
    
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

if __name__ == '__main__':
    pass
