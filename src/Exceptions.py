#!/usr/bin/env python3

def IncoherenceError(Exception):

    def __init__(self, solution1, solution2):
        self.solution1 = solution1
        self.solution2 = solution2

    def display(self, verbose=False, debug=False):
        pass

if __name__ == '__main__':
    pass
