#!/usr/bin/env python3
"""Check every DOI and arXiv identifier quoted in bibliography.md.

For a DOI the script asks doi.org for CSL-JSON metadata, which is provided by the
registration agency (Crossref, DataCite and so on). For an arXiv identifier it asks
the arXiv API. For each entry the script compares a short expected title fragment,
written below, with the title the registry returns, and prints MATCH or MISMATCH.

The point of the comparison is that an identifier which merely resolves can still
point at the wrong paper. A MATCH here means the registry says this identifier
belongs to a work whose title contains the fragment, so the identifier and the
title in the bibliography agree up to the fragment chosen. Volume, pages and year
are printed for eyeball comparison with bibliography.md and are not asserted.

Run:   python3 check_refs.py
Writes check_refs.out in the same directory and prints the same text.
Deterministic: fixed order, one request per identifier, no randomness, fixed pause.
"""

import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET

UA = "ac-bibliography-check/1.0 (Andrews-Curtis round 1)"

# (key in bibliography.md, DOI, lowercase title fragment expected)
DOI_TABLE = [
    ("1.1", "10.1090/S0002-9939-1965-0173241-8", "free groups and handlebodies"),
    ("1.2", "10.1080/00029890.1966.11970717", "extended nielsen operations"),
    ("1.5", "10.2307/1969736", "free differential calculus"),
    ("1.4", "10.1112/plms/s2-45.1.243", "simplicial spaces"),
    ("1.6", "10.1007/978-3-642-61896-3", "combinatorial group theory"),
    ("1.7", "10.1007/978-1-4684-9372-6", "simple-homotopy theory"),
    ("2.1", "10.1112/blms/25.6.513", "balanced presentations of the trivial group"),
    ("2.2", "10.1017/CBO9780511629358", "two-dimensional homotopy"),
    ("2.3", "10.1017/CBO9780511629358.014", "andrews-curtis conjecture and its generalizations"),
    ("2.5", "10.1090/conm/296/05067", "open problems in combinatorial group theory"),
    ("2.6", "10.1090/pspum/032.2/520548", "problems in low dimensional manifold theory"),
    ("3.1", "10.1090/S0002-9947-1975-0380813-5", "group presentations and formal deformations"),
    ("3.2", "10.1023/A:1026683910833", "q-equivalence"),
    ("4.1", "10.1016/0040-9383(63)90014-4", "on the dunce hat"),
    ("4.2", "10.1016/0040-9383(85)90010-2", "potential smooth counterexample"),
    ("4.3", "10.1016/0040-9383(91)90036-4", "killing the akbulut-kirby 4-sphere"),
    ("4.4", "10.4310/jdg/1214437136", "topology of four-dimensional manifolds"),
    ("4.7", "10.1016/0040-9383(84)90040-5", "schoenflies conjecture"),
    ("4.8", "10.1007/s10711-024-00891-6", "andrews-curtis trivializations"),
    ("4.10", "10.1007/s002220050168", "morse theory and finiteness properties"),
    ("5.4", "10.1142/S1793525317500182", "balanced finite presentations of the trivial group"),
    ("6.1", "10.1142/S0218196799000370", "genetic algorithms and the andrews"),
    ("6.2", "10.1142/S0218196703001365", "breadth-first search and the andrews"),
    ("6.3", "10.1017/CBO9780511542770.022", "todd-coxeter"),
    ("6.4", "10.1142/S0218196711006753", "fitness landscapes and the andrews"),
    ("6.6", "10.1515/gcc-2019-2005", "conjugacy search problem"),
    ("7.1", "10.1007/978-3-319-96418-8_41", "andrews-curtis"),
    ("7.3", "10.1016/j.exco.2024.100168", "new andrews"),
    ("7.4", "10.1016/j.exco.2025.100201", "automated theorem proving reveals"),
    ("7.5", "10.1016/j.jaca.2025.100041", "ak(3) revisited"),
    ("7.6", "10.1007/s10817-026-09759-8", "probabilistic automaton classifier"),
    ("8.1", "10.1090/S0894-0347-00-00356-8", "product replacement algorithm"),
    ("10.2", "10.1090/conm/250/03848", "some presentations of the trivial group"),
]

# (key, arXiv id, lowercase title fragment expected)
ARXIV_TABLE = [
    ("5.1", "1504.04187", "complexity of balanced presentations"),
    ("5.5", "1504.05927", "balanced presentations of the trivial group and four-dimensional geometry"),
    ("5.6", "2606.06122", "stable andrews-curtis conjecture and thickenable"),
    ("6.1", "math/0304306", "genetic algorithms and the andrews"),
    ("6.5", "1606.01412", "distance metric ensemble learning"),
    ("6.7", "2408.15332", "what makes math problems hard"),
    ("6.8", "2606.21611", "two-hump problem"),
    ("6.9", "2607.23611", "machine-checkable equivalence certificates"),
    ("7.5", "2501.18601", "stable andrews-curtis trivialization of ak(3)"),
    ("8.3", "1103.1295", "finitary andrews-curtis conjecture"),
    ("2.8", "1401.0300", "unsolved problems in group theory"),
    ("4.8", "2304.03196", "family of andrews-curtis trivializations"),
    ("3.4", "2102.03212", "andrews-curtis"),
]


DASHES = {"\u2010": "-", "\u2011": "-", "\u2012": "-", "\u2013": "-", "\u2014": "-", "\u2015": "-"}


def normalise(text):
    """Fold Unicode dashes to '-', drop HTML tags, collapse whitespace, lowercase."""
    for bad, good in DASHES.items():
        text = text.replace(bad, good)
    text = re.sub(r"<[^>]+>", "", text)
    return " ".join(text.split()).lower()


def fetch(url, accept):
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": accept})
    with urllib.request.urlopen(req, timeout=40) as response:
        return response.status, response.read().decode("utf-8", "replace")


def do_year(meta):
    for field in ("issued", "published", "created"):
        value = meta.get(field)
        if isinstance(value, dict):
            parts = value.get("date-parts")
            if parts and parts[0]:
                return parts[0][0]
    return ""


def first(value):
    if isinstance(value, list):
        return value[0] if value else ""
    return value or ""


def check_doi(key, doi, fragment):
    columns = ["doi", key, doi]
    try:
        status, body = fetch(
            "https://doi.org/" + doi, "application/vnd.citationstyles.csl+json"
        )
    except urllib.error.HTTPError as error:
        columns.append("HTTP %s" % error.code)
        return columns
    except Exception as error:  # network failure, timeout, bad TLS
        columns.append("ERROR %s" % type(error).__name__)
        return columns
    try:
        meta = json.loads(body)
    except ValueError:
        columns.append("status %s, body is not JSON" % status)
        return columns
    title = " ".join(str(first(meta.get("title"))).split())
    year = do_year(meta)
    container = " ".join(str(first(meta.get("container-title"))).split())
    verdict = "MATCH" if normalise(fragment) in normalise(title) else "MISMATCH"
    columns += [
        "status %s" % status,
        verdict,
        title[:120],
        "year %s" % year,
        container[:70],
        "vol %s" % (meta.get("volume") or ""),
        "pp %s" % (meta.get("page") or ""),
    ]
    return columns


def check_arxiv(key, identifier, fragment):
    columns = ["arxiv", key, identifier]
    try:
        status, body = fetch(
            "https://export.arxiv.org/api/query?id_list=" + identifier,
            "application/atom+xml",
        )
    except urllib.error.HTTPError as error:
        columns.append("HTTP %s" % error.code)
        return columns
    except Exception as error:
        columns.append("ERROR %s" % type(error).__name__)
        return columns
    namespace = {"atom": "http://www.w3.org/2005/Atom"}
    try:
        root = ET.fromstring(body)
        entry = root.find("atom:entry", namespace)
        title = " ".join(entry.find("atom:title", namespace).text.split())
        published = entry.find("atom:published", namespace).text[:10]
        authors = [
            " ".join(a.find("atom:name", namespace).text.split())
            for a in entry.findall("atom:author", namespace)
        ]
    except Exception:
        columns.append("status %s, unparsable Atom feed" % status)
        return columns
    verdict = "MATCH" if normalise(fragment) in normalise(title) else "MISMATCH"
    columns += [
        "status %s" % status,
        verdict,
        title[:120],
        "submitted %s" % published,
        "authors %s" % ", ".join(authors)[:100],
    ]
    return columns


def main():
    lines = [
        "Identifier check for bibliography.md",
        "Sources: doi.org CSL-JSON content negotiation, and the arXiv Atom API.",
        "MATCH means the registry title contains the expected fragment.",
        "",
    ]
    failures = 0
    for key, doi, fragment in DOI_TABLE:
        columns = check_doi(key, doi, fragment)
        if "MATCH" not in columns:
            failures += 1
        lines.append(" | ".join(columns))
        sys.stderr.write(".")
        time.sleep(0.4)
    lines.append("")
    for key, identifier, fragment in ARXIV_TABLE:
        columns = check_arxiv(key, identifier, fragment)
        if "MATCH" not in columns:
            failures += 1
        lines.append(" | ".join(columns))
        sys.stderr.write(".")
        time.sleep(0.4)
    lines.append("")
    lines.append(
        "summary: %d DOI checks and %d arXiv checks, %d without MATCH"
        % (len(DOI_TABLE), len(ARXIV_TABLE), failures)
    )
    text = "\n".join(lines) + "\n"
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_refs.out")
    with open(out, "w", encoding="utf-8") as handle:
        handle.write(text)
    sys.stdout.write(text)
    sys.stderr.write("\nwrote %s\n" % out)


if __name__ == "__main__":
    main()
