#import "template.typ": *

#show: doc => conf(
  title: [
    Linear Algebra F$ast$cked Up
  ],
  subtitle: [Higher Algebra],
  date: "2026",
  cover-image: "cover.png",
  doc,
)

This is my personal notes on Higher Algebra.

This work is done along the help of OpenAI's GPT 5.6 sol (codex), in assist of template design and (around 50% of) content generated, under my own supervision.

Most of the content is based on the great work of #emph[Jacob Lurie, Higher Algebra], which is available at #link("https://www.math.ias.edu/~lurie/papers/HA.pdf")[https://www.math.ias.edu/~lurie/papers/HA.pdf]

#pagebreak()

#include "chapters/chapter_00.typ"

#include "chapters/chapter_01.typ"

#include "chapters/chapter_02.typ"

#include "chapters/chapter_03.typ"

#include "chapters/chapter_04.typ"

#include "chapters/chapter_05.typ"

#include "chapters/chapter_06.typ"
