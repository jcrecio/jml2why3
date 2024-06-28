#!/usr/bin/env python3

import sys
from io import TextIOWrapper
import re

# <tag>: <text>
comment_re = re.compile(r"^ *\(\* (Java|Why3|Section): *(.*) *\*\) *$")

def comments(lines):
    for line in lines:
        m = comment_re.match(line[:-1])
        if m:
            tag, pattern = m.group(1), m.group(2)
            # <tag>: <pattern> (// <heading> (; <conditions>)?)?
            if '//' in pattern:
                pattern, heading = pattern.split('//')
                if ';' in heading:
                    heading, condition = heading.split(';')
                    yield tag, pattern, heading, condition
                else:
                    yield tag, pattern, heading, None
            else:
                yield tag, pattern, None, None

def group(comments):
    in_section = False
    current_java, current_why3s = None, []
    def flush():
        nonlocal current_java, current_why3s
        if current_java is not None:
            yield current_java, current_why3s
        current_java, current_why3s = None, []
    for tag, content, heading, condition in comments:
        if tag == "Section":
            assert not heading and not condition
            yield from flush()
            if in_section:
                yield 'end-list'
            in_section = True
            yield content
        elif tag == "Java":
            yield from flush()
            current_java = content, heading, condition
        elif tag == "Why3":
            if current_java is None:
                print("Why3 comment without Java comments", file=sys.stderr)
                sys.exit(1)
            current_why3s.append((content, heading, condition))
    yield from flush()
    if in_section:
        yield 'end-list'

def escape(s):
    return (
        s
        .replace('\\', '\\textbackslash ')
        .replace('{', '\\{')
        .replace('}', '\\}')
        .replace('_', '\\_')
        .replace('&', '\\&')
        # .replace('[', '\\[')
        # .replace(']', '\\]')
    )

code_re = re.compile("`([^`]*)`")

def markdown(s):
    return (
        code_re
        .sub(r'\\texttt{\1}', s)
    )

pipes_re = re.compile(r'(?:\|(nonull|nullable|imm|mut))')

def group_to_latex(x, out):
    if x == 'end-list':
        # out.write("\\end{itemize}\n")
        pass
    elif type(x) == str:
        out.write("\n")
        out.write("%"*72+"\n")
        out.write("\\subsection{{{}}}\n".format(escape(x)))
        # out.write("\\begin{itemize}\n")
    else:
        def outer_latex_item(pattern, heading, condition):
            if heading:
                out.write(r"\noindent\jmlwhyheading{{{}}}".format(markdown(escape(heading)).strip()))
                out.write(r"\\")
            out.write(r"\lstinline^{}^".format(pattern.replace("_i", "$_i$").strip()))
            if condition:
                out.write(r"\jmlwhycomment{{{}}}".format(markdown(escape(condition)).strip()))
            out.write("\n\n")
        def inner_latex_item(pattern, heading, condition):
            out.write(r"\lstinline^{}^".format(pattern.replace("_i", "$_i$").strip()))
            if heading:
                out.write(r"\jmlwhycomment{{{}}}".format(markdown(escape(heading)).strip()))
                if condition: # newline
                    out.write(r"\\[-1ex]\null")
            if condition:
                out.write(r"\jmlwhycomment{{{}}}".format(markdown(escape(condition)).strip()))
            out.write("\n\n")
        # Java
        item, why3s = x
        pattern, heading, condition = item
        out.write(r"\noindent\rule{\textwidth}{1pt}\\")
        outer_latex_item(pattern, heading, condition)
        if why3s:
            out.write(r"\begin{itemize}")
            out.write("\n")
            for pattern, heading, condition in why3s:
                out.write(r"\item")
                inner_latex_item(pattern, heading, condition)
            out.write(r"\end{itemize}")
            out.write("\n")

with open("../jml2why3.ml") as f:
    for x in group(comments(f)):
        group_to_latex(x, sys.stdout)
