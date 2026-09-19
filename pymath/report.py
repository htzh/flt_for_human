"""Presentation helpers shared by the pymath demos.

A demo should read as an illustrated explanation, not a bare computation:

* ``note``   prints narrative prose saying what the example illustrates;
* ``data``   prints a computed value or a displayed formula;
* ``check``  prints and records one mathematical law;
* ``finish`` exits non-zero if any check failed.

Blank lines are managed so output is consistently spaced, and wrapping lives
here so the result is readable both in a terminal and in ``<demo>.expected.txt``.
"""

import textwrap


class Report:
    def __init__(self, title=None, width=78):
        self.width = width
        self.failures = []
        self.checks = 0
        self._blank = True
        if title:
            self._p(title)
            self._p()

    def _p(self, line=""):
        """Print a line, collapsing runs of blank lines."""
        if line == "":
            if not self._blank:
                print()
                self._blank = True
        else:
            print(line)
            self._blank = False

    def section(self, title):
        self._p()
        self._p(f"== {title} ==")
        self._p()

    def note(self, text):
        """Narrative prose; a blank line separates paragraphs."""
        for para in text.strip().split("\n\n"):
            self._p()
            wrapped = textwrap.fill(" ".join(para.split()), width=self.width,
                                    initial_indent="  ", subsequent_indent="  ",
                                    break_on_hyphens=False, break_long_words=False)
            for line in wrapped.split("\n"):
                self._p(line)

    def data(self, text):
        self._p(f"    {text}")

    def check(self, label, ok):
        self.checks += 1
        self._p(f"    {'ok ' if ok else 'FAIL'}  {label}")
        if not ok:
            self.failures.append(label)

    def finish(self):
        self._p()
        if self.failures:
            self._p(f"FAILED: {len(self.failures)} of {self.checks} checks: {self.failures}")
            raise SystemExit(1)
        self._p(f"all checks passed ({self.checks} checks)")
