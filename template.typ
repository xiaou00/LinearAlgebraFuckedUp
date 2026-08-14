// ─────────────────────────────────────────────
//  Math Notes Template
// ─────────────────────────────────────────────

#import "@preview/fletcher:0.5.8" as fletcher

#let ink    = rgb("#234f7d")        // deep academic blue for titles and headings
#let muted  = rgb("#60788e")        // muted steel blue for secondary text
#let rule-c = rgb("#c5d7e6")        // pale blue for rules

// environment colors
#let c-thm  = rgb("#245a8d")       // theorem
#let c-def  = rgb("#3c6f9e")       // definition
#let c-prop = rgb("#507fa9")       // proposition / lemma / corollary
#let c-con  = rgb("#658eaf")       // example
#let c-rem  = rgb("#7898b3")       // remark

#let songti-fonts = (
  "SimSun",
  "Songti SC",
  "Noto Serif CJK SC",
  "Source Han Serif SC",
  "LXGW WenKai GB Screen",
  "LXGW WenKai Screen",
  "FreeSerif",
)

#let _env-counter(tag) = counter("env-" + tag)

#let _zero-based-heading-numbering(pattern) = (..numbers) => {
  let numbers = numbers.pos()
  numbering(pattern, numbers.first() - 1, ..numbers.slice(1))
}

// A compact filled 2-simplex, entirely drawn as a Fletcher diagram.
// Examples:
//   #simplex2($x_0$, $x_1$, $x_2$)
//   #simplex2($x_0$, $x_1$, $x_2$, ab: $f$, bc: $g$, ac: $g compose f$)
#let simplex2(a, b, c, ab: none, bc: none, ac: none) = fletcher.diagram(
  spacing: 20pt,
  cell-size: 0pt,
  node-inset: 5pt,
  {
    fletcher.edge(
      (-0.18, 1.02), (1.18, 1.02),
      label: $#ac$, label-side: right, marks: "->",
    )
    fletcher.edge(
      (0.5, -0.18), (1.18, 1.02),
      label: $#bc$, label-side: left, marks: "->",
    )
    fletcher.edge(
      (-0.18, 1.02), (0.5, -0.18),
      label: $#ab$, label-side: left, marks: "->",
    )

    fletcher.node((-0.18, 1.02), $#a$)
    fletcher.node((1.18, 1.02), $#c$)
    fletcher.node((0.5, -0.18), $#b$)
    fletcher.node((0.5, 0.61), text(size: 10pt, "///"))
  },
)
#let simplex2hollow(a, b, c, ab: none, bc: none, ac: none) = fletcher.diagram(
  spacing: 20pt,
  cell-size: 0pt,
  node-inset: 5pt,
  {
    fletcher.edge(
      (-0.18, 1.02), (1.18, 1.02),
      label: $#ac$, label-side: right, marks: "->",
    )
    fletcher.edge(
      (0.5, -0.18), (1.18, 1.02),
      label: $#bc$, label-side: left, marks: "->",
    )
    fletcher.edge(
      (-0.18, 1.02), (0.5, -0.18),
      label: $#ab$, label-side: left, marks: "->",
    )

    fletcher.node((-0.18, 1.02), $#a$)
    fletcher.node((1.18, 1.02), $#c$)
    fletcher.node((0.5, -0.18), $#b$)
  },
)

#let _cover-simplex() = {
  let edge = 1.15pt + c-thm
  let hidden-edge = (paint: c-thm.lighten(28%), thickness: 0.8pt, dash: "dashed")
  let vertex = 3.2pt

  box(width: 132pt, height: 112pt, {
    // A centered equilateral silhouette with three subtly shaded faces.
    place(dx: 18pt, dy: 10pt, polygon(
      fill: c-thm.transparentize(90%),
      stroke: none,
      (48pt, 0pt), (0pt, 82pt), (48pt, 58pt),
    ))
    place(dx: 66pt, dy: 10pt, polygon(
      fill: c-def.transparentize(92%),
      stroke: none,
      (0pt, 0pt), (48pt, 82pt), (0pt, 58pt),
    ))
    place(dx: 18pt, dy: 68pt, polygon(
      fill: c-prop.transparentize(88%),
      stroke: none,
      (48pt, 0pt), (0pt, 24pt), (96pt, 24pt),
    ))

    // The three outer sides stay solid; only the rear inner edge is dashed.
    place(dx: 18pt, dy: 92pt, line(end: (48pt, -24pt), stroke: hidden-edge))
    place(dx: 66pt, dy: 10pt, line(end: (-48pt, 82pt), stroke: edge))
    place(dx: 66pt, dy: 10pt, line(end: (48pt, 82pt), stroke: edge))
    place(dx: 66pt, dy: 10pt, line(end: (0pt, 58pt), stroke: edge))
    place(dx: 18pt, dy: 92pt, line(end: (96pt, 0pt), stroke: edge))
    place(dx: 66pt, dy: 68pt, line(end: (48pt, 24pt), stroke: edge))

    for point in ((66pt, 10pt), (18pt, 92pt), (66pt, 68pt), (114pt, 92pt)) {
      place(
        dx: point.at(0) - vertex,
        dy: point.at(1) - vertex,
        circle(radius: vertex, fill: white, stroke: 1.2pt + c-thm),
      )
    }
  })
}

#let _reset-env-counters() = {
  for tag in ("theorem", "lemma", "corollary", "proposition", "definition", "axiom") {
    _env-counter(tag).update(0)
  }
}

#let _env-labels = (
  "env-theorem": "Theorem",
  "env-lemma": "Lemma",
  "env-corollary": "Corollary",
  "env-proposition": "Proposition",
  "env-definition": "Definition",
  "env-axiom": "Axiom",
)

#let _env-ref(it) = {
  let el = it.element
  if el != none and repr(el.func()) == "block" and repr(el.body.func()) == "align" {
    let inner = el.body.body
    if repr(inner.func()) == "sequence" and inner.children.len() > 0 {
      let first = inner.children.first()
      if repr(first.func()) == "counter-update" and first.has("key") and first.key in _env-labels {
        let hs = counter(heading).at(el.location())
        let chapter = hs.at(0, default: 1) - 1
        let section = hs.at(1, default: 0)
        let n = counter(first.key).at(el.location()).first() + 1
        let number = str(chapter) + "." + str(section) + "." + str(n)
        link(el.location(), _env-labels.at(first.key) + " " + number)
      } else {
        it
      }
    } else {
      it
    }
  } else {
    it
  }
}

// ── Page setup ───────────────────────────────
#let conf(
  title:    "",
  subtitle: "",
  author:   "",
  date:     "",
  cover-image: none,
  easy:     false,
  doc,
) = {
  let header-after = if easy { 0 } else { 2 }

  set page(
    paper:        "a4",
    margin:       (x: 3cm, top: 2.8cm, bottom: 2.5cm),
    header: context {
      if counter(page).get().first() > header-after {
        grid(
          columns: (1fr, 1fr),
          align(left,  text(size: 8pt, fill: muted, title)),
          align(right, text(size: 8pt, fill: muted,
            counter(page).display("1 / 1", both: true))),
        )
        v(-6pt)
        line(length: 100%, stroke: 0.4pt + muted)
      }
    },
    footer: none,
  )

  set text(
    font:   ("Libertinus Serif", "New Computer Modern", "FreeSerif", "LXGW WenKai GB Screen"),
    size:   11pt,
    lang:   "en",
  )

  show math.equation: set text(font: ("Libertinus Math", "LXGW WenKai Screen" ) )

  set par(justify: true, leading: 0.75em, spacing: 1.1em)

  show ref: _env-ref

  // fake bold for CJK fonts that lack a bold variant
  show strong: it => text(stroke: 0.35pt + black, weight: "bold", it)

  set math.equation(numbering: none)

  set heading(numbering: _zero-based-heading-numbering("1.1"))

  // headings
  show heading.where(level: 1): it => {
    _reset-env-counters()
    pagebreak(weak: true)
    v(0.9em)
    text(
      size: 20pt,
      weight: "bold",
      fill: ink,
      [#counter(heading).display(_zero-based-heading-numbering("1"))  #it.body],
    )
    v(0.25em)
    line(length: 100%, stroke: 0.7pt + rule-c)
    v(0.55em)
  }
  show heading.where(level: 2): it => {
    v(0.75em)
    text(
      size: 15pt,
      weight: "bold",
      fill: ink,
      [#counter(heading).display(_zero-based-heading-numbering("1.1"))  #it.body],
    )
    v(0.35em)
  }
  show heading.where(level: 3): it => {
    v(0.55em)
    text(
      size: 12pt,
      weight: "bold",
      fill: ink,
      [#counter(heading).display(_zero-based-heading-numbering("1.1.1"))  #it.body],
    )
    v(0.15em)
  }

  // ── title block ──────────────────────────────
  if not easy {
    align(center, {
      v(1fr)
      text(size: 32pt, weight: "bold", fill: ink, title)
      if subtitle != "" {
        v(4pt)
        text(size: 10pt, style: "italic", fill: muted, subtitle)
      }
      v(10pt)
      line(length: 55%, stroke: 0.8pt + rule-c)
      v(16pt)
      if cover-image == none {
        _cover-simplex()
        v(-20pt)
      } else {
        box(
          width: 300pt,
          height: 300pt,
          clip: true,
          radius: 9pt,
          image(cover-image, width: 100%, height: 100%, fit: "cover"),
        )
        v(14pt)
      }
      text(size: 17pt, fill: ink, 
      [
        $"xiaou0"$
      ])
      v(0pt)
      text(size: 10pt, fill: muted, date)
      v(10pt)
      line(length: 55%, stroke: 0.8pt + rule-c)
      v(-20pt)
      if date != "" {
        linebreak()
        v(5pt)
       
      }
      v(1fr)
    })

    pagebreak()

    // ── table of contents ────────────────────────
    {
      show outline.entry.where(level: 1): it => {
        v(20pt, weak: true)
        strong(it)
      }
      text(size: 20pt, weight: "bold", fill: ink, "Contents")
      v(0.8em)
      outline(
        title: none,
        indent: 1.5em,
        depth: 2,
      )
    }

    pagebreak()
  }

  doc
}

// ── Theorem environments ──────────────────────

#let _env(tag, label, color, title, body, numbering: true) = {
  let cnt = _env-counter(tag)
  block(
    width:   100%,
    breakable: true,
    inset:   (left: 12pt, right: 12pt, top: 9pt, bottom: 9pt),
    radius:  0pt,
    fill:    white,
    stroke:  (left: 3pt + color),
    align(left, {
      if numbering { cnt.step() }
      context {
        let hs = counter(heading).get()
        let chapter = hs.at(0, default: 1) - 1
        let section = hs.at(1, default: 0)
        let n = cnt.get().first()
        let number = str(chapter) + "." + str(section) + "." + str(n)

        text(weight: "semibold", fill: color,
          label
          + if numbering { " " + number } else { "" }
          + if title != "" { " (" + title + ")" } else { "" }
          + ". "
        )
      }
      body
    })
  )
}

#let theorem(body, title: "")    = _env("theorem",    "Theorem",     c-thm,  title, body)
#let lemma(body, title: "")      = _env("lemma",      "Lemma",       c-thm, title, body)
#let proposition(body, title:"") = _env("proposition","Proposition", c-thm, title, body)
#let corollary(body, title: "")  = _env("corollary",  "Corollary",   c-thm, title, body)
#let definition(body, title: "") = _env("definition", "Definition",  c-def,  title, body)
#let axiom(body, title: "")      = _env("axiom",      "Axiom",       c-def,  title, body)
#let example(body, title: "")    = _env("example",    "Example",     c-con,  title, body, numbering: false)
#let remark(body, title: "")     = _env("remark",     "Remark",      c-rem,  title, body, numbering: false)

#let quote(body) = block(
  width: 100%,
  inset: (top: 0.8em, bottom: 0.8em),
  align(center, grid(
    columns: (auto, auto, auto),
    column-gutter: 0.15em,
    align: horizon,
    text(size: 24pt, fill: c-def, "“"),
    body,
    text(size: 24pt, fill: c-def, "”"),
  )),
)

#let proof(body) = block(
  width: 100%, inset: (left: 0pt, right: 0pt, top: 4pt, bottom: 4pt),
  {
    text(style: "italic", fill: muted, "Proof. ")
    body
    h(1fr)
    text(fill: muted, "□")
  }
)

#let proofsketch(body) = block(
  width: 100%, inset: (left: 0pt, right: 0pt, top: 4pt, bottom: 4pt),
  {
    text(style: "italic", fill: muted, "Proof sketch. ")
    body
    h(1fr)
    text(fill: muted, "□")
  }
)

/* defines */

#let rightarrow = $stretch(->, size: #15pt)$
#let movebase(size, x) = text(baseline: size)[#x]
#let injlim = $display(limits(lim_(movebase(#(-1.9pt),rightarrow))))$
#let varinjlim(subscript) = $injlim_movebase(#(-2.8pt), subscript)$

#let leftarrow = $stretch(<-, size: #15pt)$
#let projlim = $display(limits(lim_(movebase(#(-1.9pt),leftarrow))))$
#let varprojlim(subscript) = $projlim_movebase(#(-2.8pt), subscript)$

#let neq(body) = math.equation(
  block: true,
  numbering: "(I)",
  body,
)

#let colim = $limits(op("colim"))$
#let Spec = $op("Spec")$

#let act = $arrow.half.cw$
#let wedge = $or$
#let smash = $and$
#let coprod = $union.sq$

#let et = "ét"
#let Ner = $"N"_bullet$
#let fib = $"fib"$
#let cofib = $"cofib"$
#let coker = $"coker"$
#let dg = $"dg"$

#let Hom = "Hom"
#let Map = "Map"
#let Der = "Der"
#let Aut = "Aut"
#let End = "End"
#let Lan = "Lan"
#let Ran = "Ran"
#let Pic = "Pic"
#let Ext = "Ext"
#let Tor = "Tor"
#let op = "op"
#let pr = "pr"
#let Spf = "Spf"
#let CH = "CH"
#let yo = "よ"

#let Fun = $bold(sans("Fun"))$
#let Exc = $bold(sans("Exc"))$
#let Set = $bold(sans("Set"))$
#let PSh = $bold(sans("PSh"))$
#let Sh = $bold(sans("Sh"))$
#let Ab = $bold(sans("Ab"))$
#let Ring = $bold(sans("Ring"))$
#let Mod = $bold(sans("Mod"))$
#let QCoh = $bold(sans("QCoh"))$
#let Grp = $bold(sans("Grp"))$
#let Sch = $bold(sans("Sch"))$
#let Top = $bold(sans("Top"))$
#let Aff = $bold(sans("Aff"))$
#let Cat = $bold(sans("Cat"))$
#let Grpd = $bold(sans("Grpd"))$
#let Ani = $bold(sans("Ani"))$
#let St = $bold(sans("St"))$
#let PSt = $bold(sans("PSt"))$
#let sSet = $bold(sans("sSet"))$
#let CG = $bold(sans("CG"))$
#let QCat = $bold(sans("QCat"))$
#let Sp = $bold(sans("Sp"))$
#let Ch = $bold(sans("Ch"))$
#let dgCat = $bold(sans("dgCat"))$
#let Kcat = $bold(sans("K"))$
#let Dcat = $bold(sans("D"))$
#let Fin = $bold(sans("Fin"))$

#let cat(name) = $bold(sans(name))$

#let fork = $\u{22D4}$
#let lfork = math.attach(box(width: 0pt)[], t: $fork$)
