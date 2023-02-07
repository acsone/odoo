# -*- coding: utf-8 -*-
from decorator import decorator
import inspect
import logging
import sys
import time
import functools

import odoo

_logger = logging.getLogger(__name__)


class _LogTracer(object):
    def __init__(self, whitelist=None, blacklist=None, files=None, deep=False):
        self.profiles = {}
        self.whitelist = whitelist
        self.blacklist = blacklist
        self.files = files
        self.deep = deep
        self.first_frame = None

    def tracer(self, frame, event, arg):
        if not self.first_frame:
            self.first_frame = frame.f_code
        if not self.deep and self.first_frame != frame.f_code:
            return self.tracer

        if frame.f_code.co_name in ['<genexpr>', '__getattr__', '__iter__', '__init__']:
            return

        if 'self' not in frame.f_locals:
            return self.tracer

        if self.files and frame.f_code.co_filename not in self.files:
            return self.tracer

        in_self = frame.f_locals['self']

        if not isinstance(in_self, odoo.models.BaseModel):
            return self.tracer

        model = getattr(in_self, '_name', None)

        if self.whitelist and model not in self.whitelist:
            return self.tracer
        if model in self.blacklist and self.first_frame != frame.f_code:
            return self.tracer

        if frame.f_code not in self.profiles:
            try:
                lines, firstline = inspect.getsourcelines(frame)
                self.profiles[frame.f_code] = {
                    'model': model,
                    'filename': frame.f_code.co_filename,
                    'firstline': firstline,
                    'code': lines,
                    'calls': [],
                    'nb': 0,
                }
            except Exception:
                return
        codeProfile = self.profiles[frame.f_code]

        if not frame.f_lineno:
            codeProfile['nb'] += 1

        cr = getattr(in_self, '_cr', None)
        codeProfile['calls'].append({
            'event': event,
            'lineno': frame.f_lineno,
            'queries': cr and cr.sql_log_count,
            'time': time.time(),
            'callno': codeProfile['nb'],
        })

        return self.tracer


def profile(method=None, whitelist=None, blacklist=(None,), files=None,
            minimum_time=0, minimum_queries=0):
    """
        Decorate an entry point method.
        If profile is used without params, log as shallow mode else, log
        all methods for all odoo models by applying the optional filters.

        :param whitelist: None or list of model names to display in the log
                        (Default: None)
        :type whitelist: list or None
        :param files: None or list of filenames to display in the log
                        (Default: None)
        :type files: list or None
        :param list blacklist: list model names to remove from the log
                        (Default: remove non odoo model from the log: [None])
        :param int minimum_time: minimum time (ms) to display a method
                        (Default: 0)
        :param int minimum_queries: minimum sql queries to display a method
                        (Default: 0)

        .. code-block:: python

          from odoo.tools.profiler import profile

          class SaleOrder(models.Model):
            ...

            @api.model
            @profile                    # log only this create method
            def create(self, vals):
            ...
            @profile()                  # log all methods for all odoo models
            def unlink(self):
            ...
            @profile(whitelist=['sale.order', 'ir.model.data'])
            def action_quotation_send(self):
            ...
            @profile(files=['/home/openerp/odoo/odoo/addons/sale/models/sale.py'])
            def write(self):
            ...

        NB: The use of the profiler modifies the execution time
    """

    deep = not method

    def _odooProfile(method, *args, **kwargs):
        log_tracer = _LogTracer(whitelist=whitelist, blacklist=blacklist, files=files,
                                deep=deep)
        sys.settrace(log_tracer.tracer)
        try:
            result = method(*args, **kwargs)
        finally:
            sys.settrace(None)

        log = ["\n%-10s%-10s%s\n" % ('calls', 'queries', 'ms')]

        for v in log_tracer.profiles.values():
            v['report'] = {}
            l = len(v['calls'])
            for k, call in enumerate(v['calls']):
                if k + 1 >= l:
                    continue

                if call['lineno'] not in v['report']:
                    v['report'][call['lineno']] = {
                        'nb_queries': 0,
                        'delay': 0,
                        'nb': 0,
                    }
                v['report'][call['lineno']]['nb'] += 1

                n = k + 1
                while k + 1 <= l and v['calls'][k + 1]['callno'] != call['callno']:
                    n += 1
                if n >= l:
                    continue
                next_call = v['calls'][n]
                if next_call['queries'] is not None:
                    v['report'][call['lineno']]['nb_queries'] += next_call[
                                                                     'queries'] - call.get(
                        'queries', 0)
                v['report'][call['lineno']]['delay'] += next_call['time'] - call['time']

            queries = 0
            delay = 0
            for call in v['report'].values():
                queries += call['nb_queries']
                delay += call['delay']

            if minimum_time and minimum_time > delay * 1000:
                continue
            if minimum_queries and minimum_queries > queries:
                continue

            # todo: no color if output in a file
            log.append("\033[1;33m%s %s--------------------- %s, %s\033[1;0m\n\n" % (
            v['model'] or '', '-' * (15 - len(v['model'] or '')), v['filename'],
            v['firstline']))
            for lineno, line in enumerate(v['code']):
                if (lineno + v['firstline']) in v['report']:
                    data = v['report'][lineno + v['firstline']]
                    log.append("%-10s%-10s%-10s%s" % (
                        str(data['nb']) if 'nb_queries' in data else '.',
                        str(data.get('nb_queries', '')),
                        str(round(
                            data['delay'] * 100000) / 100) if 'delay' in data else '',
                        line[:-1]))
                else:
                    log.append(" " * 30)
                    log.append(line[:-1])
                log.append('\n')

            log.append("\nTotal:\n%-10s%-10d%-10s\n\n" % (
                str(data['nb']),
                queries,
                str(round(delay * 100000) / 100)))

        _logger.info(''.join(log))

        return result

    if not method:
        return lambda method: decorator(_odooProfile, method)

    wrapper = decorator(_odooProfile, method)
    return wrapper


class QwebTracker():

    @classmethod
    def wrap_render(cls, method_render):
        @functools.wraps(method_render)
        def _tracked_method_render(self, template, values=None, **options):
            current_thread = threading.current_thread()
            execution_context_enabled = getattr(current_thread, 'profiler_params',
                                                {}).get('execution_context_qweb')
            qweb_hooks = getattr(current_thread, 'qweb_hooks', ())
            if execution_context_enabled or qweb_hooks:
                # To have the new compilation cached because the generated code will change.
                # Therefore 'profile' is a key to the cache.
                options['profile'] = True
            return method_render(self, template, values, **options)

        return _tracked_method_render

    @classmethod
    def wrap_compile(cls, method_compile):
        @functools.wraps(method_compile)
        def _tracked_compile(self, template, options):
            if not options.get('profile'):
                return method_compile(self, template, options)

            render_template = method_compile(self, template, options)

            def profiled_method_compile(self, values):
                ref = options.get('ref')
                ref_xml = options.get('ref_xml')
                qweb_tracker = QwebTracker(ref, ref_xml, self.env.cr)
                self = self.with_context(qweb_tracker=qweb_tracker)
                if qweb_tracker.execution_context_enabled:
                    with ExecutionContext(template=ref):
                        return render_template(self, values)
                return render_template(self, values)

            return profiled_method_compile

        return _tracked_compile

    @classmethod
    def wrap_compile_directive(cls, method_compile_directive):
        @functools.wraps(method_compile_directive)
        def _tracked_compile_directive(self, el, options, directive, indent):
            if not options.get('profile') or directive in ('content', 'tag'):
                return method_compile_directive(self, el, options, directive, indent)

            enter = self._indent(
                f"self.env.context['qweb_tracker'].enter_directive({directive!r}, {el.attrib!r}, {options['last_path_node']!r})",
                indent)
            leave = self._indent("self.env.context['qweb_tracker'].leave_directive()",
                                 indent)
            code_directive = method_compile_directive(self, el, options, directive,
                                                      indent)
            return [enter, *code_directive, leave] if code_directive else []

        return _tracked_compile_directive

    def __init__(self, view_id, arch, cr):
        current_thread = threading.current_thread()  # don't store current_thread on self
        self.execution_context_enabled = getattr(current_thread, 'profiler_params',
                                                 {}).get('execution_context_qweb')
        self.qweb_hooks = getattr(current_thread, 'qweb_hooks', ())
        self.context_stack = []
        self.cr = cr
        self.view_id = view_id
        for hook in self.qweb_hooks:
            hook('render', self.cr.sql_log_count, view_id=view_id, arch=arch)

    def enter_directive(self, directive, attrib, xpath):
        execution_context = None
        if self.execution_context_enabled:
            execution_context = tools.profiler.ExecutionContext(directive=directive,
                                                                xpath=xpath)
            execution_context.__enter__()
            self.context_stack.append(execution_context)

        for hook in self.qweb_hooks:
            hook('enter', self.cr.sql_log_count, view_id=self.view_id, xpath=xpath,
                 directive=directive, attrib=attrib)

    def leave_directive(self):
        if self.execution_context_enabled:
            self.context_stack.pop().__exit__()

        for hook in self.qweb_hooks:
            hook('leave', self.cr.sql_log_count)
