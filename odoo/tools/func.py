# -*- coding: utf-8 -*-
# Part of Odoo. See LICENSE file for full copyright and licensing details.

__all__ = ['synchronized', 'lazy_classproperty', 'lazy_property',
           'classproperty', 'conditional', 'lazy']

from functools import wraps, partial
from inspect import getsourcefile
from json import JSONEncoder


class lazy_property(object):
    """ Decorator for a lazy property of an object, i.e., an object attribute
        that is determined by the result of a method call evaluated once. To
        reevaluate the property, simply delete the attribute on the object, and
        get it again.
    """
    def __init__(self, fget):
        self.fget = fget

    def __get__(self, obj, cls):
        if obj is None:
            return self
        value = self.fget(obj)
        setattr(obj, self.fget.__name__, value)
        return value

    @property
    def __doc__(self):
        return self.fget.__doc__

    @staticmethod
    def reset_all(obj):
        """ Reset all lazy properties on the instance `obj`. """
        cls = type(obj)
        obj_dict = vars(obj)
        for name in obj_dict.keys():
            if isinstance(getattr(cls, name, None), lazy_property):
                obj_dict.pop(name)

class lazy_classproperty(lazy_property):
    """ Similar to :class:`lazy_property`, but for classes. """
    def __get__(self, obj, cls):
        val = self.fget(cls)
        setattr(cls, self.fget.__name__, val)
        return val

def conditional(condition, decorator):
    """ Decorator for a conditionally applied decorator.

        Example:

           @conditional(get_config('use_cache'), ormcache)
           def fn():
               pass
    """
    if condition:
        return decorator
    else:
        return lambda fn: fn

def synchronized(lock_attr='_lock'):
    def decorator(func):
        @wraps(func)
        def wrapper(self, *args, **kwargs):
            lock = getattr(self, lock_attr)
            try:
                lock.acquire()
                return func(self, *args, **kwargs)
            finally:
                lock.release()
        return wrapper
    return decorator

def frame_codeinfo(fframe, back=0):
    """ Return a (filename, line) pair for a previous frame .
        @return (filename, lineno) where lineno is either int or string==''
    """
    
    try:
        if not fframe:
            return "<unknown>", ''
        for i in range(back):
            fframe = fframe.f_back
        try:
            fname = getsourcefile(fframe)
        except TypeError:
            fname = '<builtin>'
        lineno = fframe.f_lineno or ''
        return fname, lineno
    except Exception:
        return "<unknown>", ''

def compose(a, b):
    """ Composes the callables ``a`` and ``b``. ``compose(a, b)(*args)`` is
    equivalent to ``a(b(*args))``.

    Can be used as a decorator by partially applying ``a``::

         @partial(compose, a)
         def b():
            ...
    """
    @wraps(b)
    def wrapper(*args, **kwargs):
        return a(b(*args, **kwargs))
    return wrapper


class _ClassProperty(property):
    def __get__(self, cls, owner):
        return self.fget.__get__(None, owner)()

def classproperty(func):
    return _ClassProperty(classmethod(func))


class lazy(object):
    """ A proxy to the (memoized) result of a lazy evaluation::
            foo = lazy(func, arg)           # func(arg) is not called yet
            bar = foo + 1                   # eval func(arg) and add 1
            baz = foo + 2                   # use result of func(arg) and add 2
    """
    __slots__ = ['_func', '_args', '_kwargs', '_cached_value']

    def __init__(self, func, *args, **kwargs):
        # bypass own __setattr__
        object.__setattr__(self, '_func', func)
        object.__setattr__(self, '_args', args)
        object.__setattr__(self, '_kwargs', kwargs)

    @property
    def _value(self):
        if self._func is not None:
            value = self._func(*self._args, **self._kwargs)
            object.__setattr__(self, '_func', None)
            object.__setattr__(self, '_args', None)
            object.__setattr__(self, '_kwargs', None)
            object.__setattr__(self, '_cached_value', value)
        return self._cached_value

    def __getattr__(self, name):
        return getattr(self._value, name)

    def __setattr__(self, name, value):
        return setattr(self._value, name, value)

    def __delattr__(self, name):
        return delattr(self._value, name)

    def __repr__(self):
        return repr(self._value) if self._func is None else object.__repr__(self)

    def __str__(self):
        return str(self._value)

    def __format__(self, format_spec):
        return format(self._value, format_spec)

    def __lt__(self, other):
        return self._value < other

    def __le__(self, other):
        return self._value <= other

    def __eq__(self, other):
        return self._value == other

    def __ne__(self, other):
        return self._value != other

    def __gt__(self, other):
        return self._value > other

    def __ge__(self, other):
        return self._value >= other

    def __hash__(self):
        return hash(self._value)

    def __bool__(self):
        return bool(self._value)

    def __call__(self, *args, **kwargs):
        return self._value(*args, **kwargs)

    def __len__(self):
        return len(self._value)

    def __getitem__(self, key):
        return self._value[key]

    def __missing__(self, key):
        return self._value.__missing__(key)

    def __setitem__(self, key, value):
        self._value[key] = value

    def __delitem__(self, key):
        del self._value[key]

    def __iter__(self):
        return iter(self._value)

    def __reversed__(self): return \
        reversed(self._value)

    def __contains__(self, key):
        return key in self._value


# patch serialization of lazy
def default(self, o):
    if isinstance(o, lazy):
        return o._value
    return json_encoder_default(self, o)


json_encoder_default = JSONEncoder.default
JSONEncoder.default = default
