#!/usr/bin/env python3

import src.Predicates

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
        if register or cls == src.Predicates.AtomicPredicate:
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


if __name__ == '__main__':
    pass
