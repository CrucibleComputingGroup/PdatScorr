"""Recognize named upstream RSD assertions, whose macro only prints messages.

The one empty-string assertion cannot be identified retrospectively in old
logs. This checker does not claim coverage of that unlabelled diagnostic.
"""
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import re

ROOT=Path(__file__).resolve().parent

@lru_cache(maxsize=1)
def diagnostic_catalog():
    messages=set()
    sources={}
    assertions=[]
    for path in (ROOT/'rsd/Processor/Src').rglob('*.sv'):
        if 'Verification' in path.parts or path.name=='BasicMacros.sv':
            continue
        text=path.read_text()
        for match in re.finditer(r'`RSD_ASSERT_CLK(?:_FMT)?\s*\(',text):
            start=match.end();depth=1;quoted=False;escaped=False
            for end in range(start,len(text)):
                c=text[end]
                if quoted:
                    if escaped:escaped=False
                    elif c=='\\':escaped=True
                    elif c=='"':quoted=False
                elif c=='"':quoted=True
                elif c=='(':depth+=1
                elif c==')':
                    depth-=1
                    if depth==0:break
            literals=re.findall(r'"((?:[^"\\]|\\.)*)"',text[start:end])
            relative=str(path.relative_to(ROOT/'rsd/Processor/Src'))
            sources[relative]=hashlib.sha256(path.read_bytes()).hexdigest()
            assertions.append({'source':relative,'line':text.count('\n',0,match.start())+1,
                               'message':literals[-1] if literals else None})
            if literals and len(literals[-1])>=5:
                messages.add(literals[-1])
    patterns=[]
    formats={'x':r'[0-9a-fA-FxXzZ]+','X':r'[0-9a-fA-FxXzZ]+','d':r'[+-]?[0-9]+',
             'u':r'[0-9]+','f':r'[+-]?[0-9]+(?:\.[0-9]+)?','s':r'[^\n]*?',
             'p':r'(?:0x)?[0-9a-fA-F]+'}
    for message in sorted(messages):
        parts=re.split(r'(%[-+0-9.]*[dxXufsp])',message)
        patterns.append(''.join(formats[part[-1]] if part.startswith('%') else re.escape(part) for part in parts))
    return {'core_revision':'7b65f6ba0bce58d4d859082660123b7100aae975','source_sha256':sources,
            'assertions':assertions,'named_messages':sorted(messages),'regex_patterns':patterns,
            'scope':'Named upstream RSD_ASSERT_CLK/_FMT diagnostic messages; exact literal text plus typed printf substitutions. Does not identify the empty-string assertion or establish all internal properties.'}

@lru_cache(maxsize=1)
def diagnostic_pattern():
    return re.compile('|'.join(diagnostic_catalog()['regex_patterns']))

def assertion_diagnostics(log):
    found=[]
    for match in diagnostic_pattern().finditer(log):
        found.append(match.group(0))
        if len(found)>=20:break
    return found

def diagnostic_categories(log):
    """Watchdogs report >500-cycle progress gaps; completion is checked separately."""
    messages=assertion_diagnostics(log)
    # Scan the complete log for categories: a burst of watchdogs in the first
    # 20 samples must not hide a different invariant diagnostic later in the log.
    unique=dict.fromkeys(match.group(0) for match in diagnostic_pattern().finditer(log))
    watchdog={'Deadlock detected','MSHR deadlock detected'}
    return {'named_messages':messages,
            'progress_watchdogs':[m for m in unique if m in watchdog],
            'other_named_assertions':[m for m in unique if m not in watchdog]}

if __name__=='__main__':
    out=ROOT/'results/rsd_named_assertion_catalog.json'
    out.write_text(json.dumps(diagnostic_catalog(),indent=2)+'\n')
    print(out)
