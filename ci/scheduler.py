"""Bounded module scheduling; receipt policy and child termination stay with callers."""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import heapq


def schedule(order, dependencies, check, workers=1, before_submit=None,
             completed=None, abort=None):
    """Run dependency-ready checks and return results keyed in ``order`` order.

    ``check(module)`` runs in a worker thread. ``before_submit(module)`` and
    ``completed(module, result)`` run on the calling thread. A dependency is
    released only after its completion callback returns successfully. A failed
    status returned normally is caller policy; an exception aborts scheduling.

    On any exception (including interruption), cancel queued work, invoke
    ``abort()`` on the calling thread, wait for running checks, and re-raise.
    Callers with compiler children must make abort terminate/unblock them;
    Python cannot cancel a thread that is already running. Invalid graphs or
    worker counts fail before creating workers or invoking any callbacks.
    """
    if type(workers) is not int or workers < 1:
        raise ValueError('workers must be a positive integer')
    order = list(order)
    rank = {module: index for index, module in enumerate(order)}
    if len(rank) != len(order):
        raise ValueError('duplicate module in schedule')
    needed = {module: set(dependencies.get(module, ())) for module in order}
    users = {module: set() for module in order}
    for module, deps in needed.items():
        for dep in deps:
            if dep not in rank:
                raise ValueError(f'unknown dependency {dep!r} of {module!r}')
            users[dep].add(module)
    remaining = {module: len(deps) for module, deps in needed.items()}
    # Reject cycles before any work starts, including cycles outside ready roots.
    probe = remaining.copy()
    roots = [module for module in order if not probe[module]]
    visited = 0
    while roots:
        module = roots.pop()
        visited += 1
        for user in users[module]:
            probe[user] -= 1
            if not probe[user]:
                roots.append(user)
    if visited != len(order):
        raise ValueError('dependency cycle in schedule')
    if not order:
        return {}

    ready = [rank[module] for module in order if not remaining[module]]
    heapq.heapify(ready)
    results = {}
    running = {}
    executor = ThreadPoolExecutor(max_workers=workers, thread_name_prefix='verify')
    try:
        while ready or running:
            while ready and len(running) < workers:
                module = order[heapq.heappop(ready)]
                if before_submit is not None:
                    before_submit(module)
                running[executor.submit(check, module)] = module
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in sorted(done, key=lambda item: rank[running[item]]):
                module = running.pop(future)
                result = future.result()
                if completed is not None:
                    completed(module, result)
                results[module] = result
                for user in users[module]:
                    remaining[user] -= 1
                    if not remaining[user]:
                        heapq.heappush(ready, rank[user])
    except BaseException as failure:
        for future in running:
            future.cancel()
        try:
            if abort is not None:
                abort()
        except BaseException as abort_failure:
            raise failure from abort_failure
        raise
    finally:
        executor.shutdown(wait=True, cancel_futures=True)
    return {module: results[module] for module in order}
