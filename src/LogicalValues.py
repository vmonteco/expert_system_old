#!/usr/bin/env python3

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

if __name__ == '__main__':
    pass
