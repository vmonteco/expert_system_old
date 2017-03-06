#!/usr/bin/env python3

class Solution:
    """
    This class contains the whole reasonning to deduce a predicate's state.
    """

    def __init__(self, result, *solutions):
        self.result = result
        self.length = max([s.length for s in solutions if s != None] or [0]) + 1
        self.parent_solutions = solutions
        self.displayed = False
        
    def make_display_text(self, verbose, debug):
        if self.displayed:
            return ''
        self.displayed = True
        res = ''
        if verbose or debug:
            for solution in self.parent_solutions:
                res += (
                    (
                        '\n' if res else '  '
                        + solution.make_display_text(verbose, debug)
                    ).replace('\n', '\n  ')
                    + '\n\n'
                )
        res += str(self.result)
        res += '\nTherefore, {pred} is {val}'.format(
            pred=self.result.pred,
            val=self.result.solve()
        )
        return res
                
    def display(self, verbose, debug, indent=0):
        if self.result.displayed:
            return
        if verbose or debug:
            for solution in self.parent_solutions:
                solution.display(verbose, debug, indent + 2)
            print(self.result.replace('\n', '\n' + indent * ' '))
            self.result.displayed = True


if __name__ == '__main__':
    pass
