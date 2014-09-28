---
content_type: md
permalink: /
layout: main
title: Konstantin Weitz
description: I'm a PhD student in Computer Science at the University of Washington. My research is focused on Programming Languages and Software Engineering, primarily Program Verification.
cvurl: resume.pdf
---

Projects
--------

#### A Type System for Format Strings

Most programming languages support format strings, but their use is error-prone.
Using the wrong format string syntax, or passing the wrong number or type of
arguments, leads to unintelligible text output, program crashes, or security
vulnerabilities.

This paper presents a type system that guarantees that calls to format string
APIs will never fail. In Java, this means that the API will not throw
exceptions. In C, this means that the API will not return negative values,
corrupt memory, etc.

We instantiated this type system for Java's Formatter API, and evaluated it on 6
large and well-maintained open-source projects. Format string bugs are common in
practice (our type system found 104 bugs), and the annotation burden on the user
of our type system is low (on average, for every bug found, only 1.0 annotations
need to be written).

Download: [Paper (PDF)][TSFS-PAPER-PDF], 
          [Slides (PDF)][TSFS-SLIDES-PDF], 
          [Slides (ODP)][TSFS-SLIDES-ODP], 
          [Demo Paper (PDF)][TSFS-DEMO-PDF], 
          [Format String Checker Implementation][TSFS-IMPL]

Publications
------------

> "A type system for format strings" 
  by Konstantin Weitz, Gene Kim, Siwakorn Srisakaokul, and Michael D. Ernst.
  *In ISSTA 2014.* <br/>
> Download: [Paper (PDF)][TSFS-PAPER-PDF], 
            [BibTeX Entry][TSFS-BIB],
            [Slides (PDF)][TSFS-SLIDES-PDF], 
            [Slides (ODP)][TSFS-SLIDES-ODP]
 
> "A format string checker for Java"
  by Konstantin Weitz, Siwakorn Srisakaokul, Gene Kim, and Michael D. Ernst.
  *In ISSTA 2014.* <br/>
> Download: [Paper (PDF)][TSFS-DEMO-PDF], 
            [BibTeX Entry][TSFS-DEMO-BIB],
            [Slides (PDF)][TSFS-SLIDES-PDF], 
            [Slides (ODP)][TSFS-SLIDES-ODP]
 
> Real-Time Collaborative Analysis with (Almost) Pure SQL: A Case Study in Biogeochemical Oceanography
  by Daniel Halperin, Francois Ribalet, Konstantin Weitz, Mak A. Saito, Bill Howe, and E. Virginia Armbrust.
  *In SSDBM 2013.* <br/>
> Download: [Paper (PDF)][OCEAN-PAPER-PDF], 
            [BibTeX Entry][OCEAN-BIB],
            [Talk][OCEAN-TALK]

Posts
-----

[TSFS-PAPER-PDF]: http://homes.cs.washington.edu/~mernst/pubs/format-string-issta2014.pdf
[TSFS-SLIDES-PDF]: http://homes.cs.washington.edu/~mernst/pubs/format-string-issta2014-slides.pdf
[TSFS-SLIDES-ODP]: http://homes.cs.washington.edu/~mernst/pubs/format-string-issta2014-slides.odp
[TSFS-DEMO-PDF]: http://homes.cs.washington.edu/~mernst/pubs/format-string-issta2014-demo.pdf
[TSFS-IMPL]: http://types.cs.washington.edu/checker-framework/current/checkers-manual.html#formatter-checker
[TSFS-BIB]: papers/tsfs.bib
[TSFS-DEMO-BIB]: papers/tsfs-demo.bib

[OCEAN-PAPER-PDF]: http://homes.cs.washington.edu/~dhalperi/pubs/halperin_2013_ssdbm_geomics_case_study.pdf
[OCEAN-TALK]: http://research.microsoft.com/apps/video/default.aspx?id=200713
[OCEAN-BIB]: papers/ocean.bib
