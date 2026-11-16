/// TeX point.
#let tp = 1in / 72.27

/// Metrics of the LaTeX `article` class at each base size, in TeX points.
#let class-metrics = (
  "10pt": (
    normal: 10,
    baseline: 12,
    small: 9,
    footnote: 8,
    large: 12,
    Large: 14.4,
    LARGE: 17.28,
    parindent: 15,
    textwidth: 345,
    topsep: 8,
    itemsep: 2,
    parsep: 4,
    display: 10,
    footins: 9,
  ),
  "11pt": (
    normal: 10.95,
    baseline: 13.6,
    small: 10,
    footnote: 9,
    large: 12,
    Large: 14.4,
    LARGE: 17.28,
    parindent: 17,
    textwidth: 360,
    topsep: 9,
    itemsep: 2.25,
    parsep: 4.5,
    display: 11,
    footins: 10,
  ),
  "12pt": (
    normal: 12,
    baseline: 14.5,
    small: 10.95,
    footnote: 10,
    large: 14.4,
    Large: 17.28,
    LARGE: 20.74,
    parindent: 18,
    textwidth: 390,
    topsep: 9,
    itemsep: 2.5,
    parsep: 5,
    display: 12,
    footins: 10.8,
  ),
)

/// Paper sizes supported by the template.
#let paper-sizes = ("a4": (210mm, 297mm), "us-letter": (8.5in, 11in))

/// Kinds of numbered statement and their amsthm styles.
#let statement-styles = (
  theorem: "plain",
  lemma: "plain",
  proposition: "plain",
  observation: "plain",
  corollary: "plain",
  conjecture: "plain",
  definition: "definition",
  example: "definition",
  remark: "remark",
)

/// Whether statements are numbered within sections.
#let statements-within-sections = state("latex-article-statements-within-sections", true)

/// Whether the appendices have started.
#let in-appendix = state("latex-article-in-appendix", false)

/// Typesets the number of the statement at a location.
///
/// - loc (location): The location of the statement.
/// -> content
#let statement-number(loc) = {
  let n = counter(figure.where(kind: "statement")).at(loc).first()
  if statements-within-sections.at(loc) {
    let section = counter(heading).at(loc).first()
    let pattern = if in-appendix.at(loc) { "A" } else { "1" }
    [#numbering(pattern, section).#n]
  } else { [#n] }
}

/// Resolves a margin, given as a length or as a dictionary of sides, into its four sides, with 1in for each side left unspecified.
///
/// - margin (length, dictionary): The margin, as accepted by `page`.
/// -> dictionary
#let resolve-margin(margin) = {
  if type(margin) == length { return (left: margin, right: margin, top: margin, bottom: margin) }
  assert(type(margin) == dictionary, message: "margin must be auto, a length or a dictionary")
  for key in margin.keys() {
    assert(key in ("left", "right", "top", "bottom", "x", "y", "rest"), message: "unknown margin side: " + key)
  }
  let rest = margin.at("rest", default: 1in)
  let x = margin.at("x", default: rest)
  let y = margin.at("y", default: rest)
  (
    left: margin.at("left", default: x),
    right: margin.at("right", default: x),
    top: margin.at("top", default: y),
    bottom: margin.at("bottom", default: y),
  )
}

/// Lays out a paper in the style of the LaTeX `article` class.
///
/// - title (content): The paper's title.
/// - document-title (none, str): The title recorded in the document's metadata, the typeset title when none.
/// - authors (array): The authors, each with a `name` and an optional `affil`, `email` and `thanks`.
/// - date (auto, none, content): The date printed below the authors, today's date when auto.
/// - abstract (none, content): The abstract.
/// - keywords (none, content): The keywords, printed below the abstract.
/// - size (length): The base font size: 10pt, 11pt or 12pt.
/// - paper (str): The paper size: "a4" or "us-letter".
/// - margin (auto, length, dictionary): The margins around the text block, as accepted by `page`; the class's own geometry when auto.
/// - indent-par (bool): Whether paragraphs are indented, as in the class, rather than separated by vertical space.
/// - region (str): The region of the English hyphenation and localisation rules.
/// - numbered-within-sections (bool): Whether statements are numbered within sections.
/// - link-colour (color): The colour of links, references and citations.
/// - body (content): The paper's content.
/// -> content
#let template(
  title: [],
  document-title: none,
  authors: (),
  date: auto,
  abstract: none,
  keywords: none,
  size: 10pt,
  paper: "a4",
  margin: 1in,
  indent-par: false,
  region: "gb",
  numbered-within-sections: true,
  link-colour: black,
  body,
) = {
  assert(type(size) == length and repr(size) in class-metrics, message: "size must be 10pt, 11pt or 12pt")
  assert(paper in paper-sizes, message: "paper must be \"a4\" or \"us-letter\"")
  let m = class-metrics.at(repr(size))
  let fs = m.normal * tp
  let bs = m.baseline * tp
  let leading = bs - fs
  let ex = 0.4306 * fs
  assert(type(indent-par) == bool, message: "indent-par must be a boolean")
  let (pw, ph) = paper-sizes.at(paper)
  let topskip = fs
  let footskip = 30 * tp
  let block-margin = if margin == auto {
    let textwidth = calc.min(pw - 2in, m.textwidth * tp)
    let lines = calc.floor((ph - 3.5in) / bs)
    let textheight = lines * bs + topskip
    let head = 12 * tp + 25 * tp
    let top = 1in + (ph - 2in - head - textheight - footskip) / 2 + head
    (left: (pw - textwidth) / 2, right: (pw - textwidth) / 2, top: top, bottom: ph - top - textheight)
  } else { resolve-margin(margin) }
  let parindent = if indent-par { m.parindent * tp } else { 0pt }
  let parskip = if indent-par { leading } else { leading + 0.5 * bs }

  set document(
    title: if document-title == none { title } else { document-title },
    author: authors.map(author => author.name),
  )
  set footnote.entry(
    separator: block(below: 3 * tp, line(length: 40%, stroke: 0.4 * tp)),
    clearance: m.footins * tp,
    indent: 0em,
    gap: 0.2em,
  )
  show footnote.entry: it => {
    let loc = it.note.location()
    let mark = numbering(it.note.numbering, ..counter(footnote).at(loc))
    set text(size: m.footnote * tp)
    set par(leading: 0.2em, first-line-indent: 0pt)
    block(width: 100%, [#box(width: 1.8em, align(right, link(loc, super(mark))))#it.note.body])
  }

  set page(
    width: pw,
    height: ph,
    margin: (
      left: block-margin.left,
      right: block-margin.right,
      top: block-margin.top + topskip - 0.7 * fs,
      bottom: block-margin.bottom - 0.3 * fs,
    ),
    footer-descent: footskip - fs,
    numbering: "1",
    number-align: center,
  )
  set text(
    lang: "en",
    region: region,
    font: "New Computer Modern",
    size: fs,
    top-edge: 0.7em,
    bottom-edge: -0.3em,
  )
  set par(
    justify: true,
    leading: leading,
    spacing: parskip,
    first-line-indent: parindent,
  )
  statements-within-sections.update(numbered-within-sections)

  set heading(numbering: (..n) => if n.pos().len() <= 3 { numbering("1.1", ..n.pos()) })
  show heading: it => {
    let level = calc.min(it.level, 3)
    let size = (m.Large, m.large, m.normal).at(level - 1) * tp
    let above = if level == 1 { 3.5 * ex } else { 3.25 * ex }
    let below = if level == 1 { 2.3 * ex } else { 1.5 * ex }
    set text(size: size, weight: "bold", hyphenate: false)
    set par(justify: false, first-line-indent: 0pt)
    block(above: above + leading, below: below + leading, sticky: true, context {
      if it.numbering != none and counter(heading).get().len() <= 3 {
        let number = counter(heading).display(it.numbering) + h(1em)
        set par(hanging-indent: measure(number).width)
        number + it.body
      } else { it.body }
    })
  }
  show heading.where(level: 1): it => {
    context if statements-within-sections.get() { counter(figure.where(kind: "statement")).update(0) }
    it
  }

  set list(marker: ([•], text(weight: "bold")[–], [∗], [·]), indent: 1.5em, body-indent: 0.5em)
  set enum(
    full: true,
    numbering: (..n) => numbering(("1.", "(a)", "i.", "A.").at(calc.min(n.pos().len(), 4) - 1), n.pos().last()),
    indent: 1.2em,
    body-indent: 0.5em,
  )
  set list(spacing: (m.itemsep + m.parsep) * tp + leading)
  set enum(spacing: (m.itemsep + m.parsep) * tp + leading)
  show list: set block(above: m.topsep * tp + leading, below: m.topsep * tp + leading)
  show enum: set block(above: m.topsep * tp + leading, below: m.topsep * tp + leading)
  show list: it => {
    show list: set list(indent: 0.6em)
    show enum: set enum(indent: 0.4em)
    it
  }
  show enum: it => {
    show list: set list(indent: 0.6em)
    show enum: set enum(indent: 0.4em)
    it
  }

  show raw: set text(font: ("New Computer Modern Mono", "DejaVu Sans Mono"), size: 1.15em, features: (calt: 0))
  show link: set text(fill: link-colour)
  show ref: set text(fill: link-colour)
  show cite: set text(fill: link-colour)

  show math.equation: set text(font: "New Computer Modern Math")
  show math.equation.where(block: true): set block(above: m.display * tp, below: m.display * tp)
  set math.equation(numbering: "(1)", supplement: none)
  show math.equation.where(block: true): it => {
    if it.has("label") { it } else {
      counter(math.equation).update(v => v - 1)
      [#math.equation(it.body, block: true, numbering: none)<unnumbered>]
    }
  }
  show ref: it => {
    let el = it.element
    if el != none and el.func() == math.equation {
      link(el.location(), numbering("(1)", ..counter(math.equation).at(el.location())))
    } else if el != none and el.func() == figure and el.kind == "statement" {
      link(el.location(), [#el.supplement~#statement-number(el.location())])
    } else { it }
  }

  set table(stroke: none, inset: (x: 6 * tp, y: 0.3em))
  show table: it => block(stroke: (top: 0.08em, bottom: 0.08em), it)
  show table: set par(justify: false)

  set place(clearance: 20 * tp)
  set figure(gap: 10 * tp)
  show figure: set block(above: 12 * tp + leading, below: 12 * tp + leading)
  show figure.where(kind: table): set figure.caption(position: top)
  show figure.where(kind: table): set block(breakable: false)
  show figure.where(kind: "algorithm"): it => {
    set par(justify: false, first-line-indent: 0pt)
    set align(left)
    block(width: 100%, stroke: (top: 0.8pt, bottom: 0.8pt), inset: (y: 0.4em), {
      set block(spacing: 0.4em)
      block[*#it.supplement #context it.counter.display(it.numbering)* #it.caption.body]
      line(length: 100%, stroke: 0.5pt)
      it.body
    })
  }
  show figure.caption: it => layout(region => {
    let caption = [#it.supplement #context it.counter.display(it.numbering): #it.body]
    set par(first-line-indent: 0pt)
    block(width: region.width, align(if measure(caption).width <= region.width { center } else { left }, caption))
  })
  show figure.where(kind: "statement"): set block(
    above: m.topsep * tp + leading,
    below: m.topsep * tp + leading,
    breakable: true,
  )
  show figure.where(kind: "statement"): set align(left)

  set bibliography(title: [References])

  v(2em)
  align(center, {
    set par(justify: false, first-line-indent: 0pt)
    block(text(size: m.LARGE * tp, hyphenate: false, title))
    v(1.5em)
    set text(size: m.large * tp)
    set par(leading: 1em)
    authors
      .map(author => box(inset: (x: 6 * tp), {
        set par(leading: 0.25em)
        let lines = (author.name,)
        if "thanks" in author { lines.at(0) += footnote(numbering: "*", author.thanks) }
        if "affil" in author { lines.push(author.affil) }
        if "email" in author { lines.push(raw(author.email)) }
        lines.join(linebreak())
      }))
      .join(h(1em))
    if date != none {
      v(1em)
      if date == auto { datetime.today().display("[day padding:none] [month repr:long] [year]") } else { date }
    }
  })
  counter(footnote).update(0)
  v(1.5em)

  if abstract != none {
    set text(size: m.small * tp)
    set par(
      leading: 0.2em,
      spacing: if indent-par { 0.2em } else { 0.7em },
      first-line-indent: if indent-par { 1.5em } else { 0pt },
    )
    align(center, strong[Abstract])
    v(-0.5em)
    pad(x: 2.5em, top: m.topsep * tp, bottom: m.topsep * tp, {
      abstract
      if keywords != none {
        parbreak()
        v(0.5em)
        par(first-line-indent: 0pt)[*Keywords:* #keywords]
      }
    })
  }

  body
}

/// Starts the appendices, with lettered sections.
///
/// - body (content): The appendices.
/// -> content
#let appendix(body) = {
  set heading(
    numbering: (..n) => if n.pos().len() <= 3 { numbering("A.1", ..n.pos()) },
    supplement: [Appendix],
  )
  counter(heading).update(0)
  in-appendix.update(true)
  body
}

/// Typesets a statement in an amsthm style: a run-in label followed by its body.
///
/// - kind (str): The label, such as "Theorem" or "Definition".
/// - name (none, content): An optional parenthetical name.
/// - style (str): The amsthm style: "plain", "definition" or "remark".
/// - body (content): The statement.
/// -> content
#let statement(kind, name: none, style: "plain", body) = {
  assert(style in ("plain", "definition", "remark"), message: "unknown statement style: " + style)
  figure(
    kind: "statement",
    supplement: kind,
    numbering: "1",
    outlined: false,
    block(width: 100%, context {
      let head = [#kind #statement-number(here())]
      if style == "remark" { emph(head) } else { strong(head) }
      if name != none [ (#name)]
      if style == "remark" { emph[.] } else { strong[.] }
      h(5 * tp)
      if style == "plain" { emph(body) } else { body }
    }),
  )
}

/// Typesets a theorem.
#let theorem(name: none, body) = statement("Theorem", name: name, style: statement-styles.theorem, body)

/// Typesets a lemma.
#let lemma(name: none, body) = statement("Lemma", name: name, style: statement-styles.lemma, body)

/// Typesets a proposition.
#let proposition(name: none, body) = statement("Proposition", name: name, style: statement-styles.proposition, body)

/// Typesets an observation.
#let observation(name: none, body) = statement("Observation", name: name, style: statement-styles.observation, body)

/// Typesets a corollary.
#let corollary(name: none, body) = statement("Corollary", name: name, style: statement-styles.corollary, body)

/// Typesets a conjecture.
#let conjecture(name: none, body) = statement("Conjecture", name: name, style: statement-styles.conjecture, body)

/// Typesets a definition.
#let definition(name: none, body) = statement("Definition", name: name, style: statement-styles.definition, body)

/// Typesets an example.
#let example(name: none, body) = statement("Example", name: name, style: statement-styles.example, body)

/// Typesets a remark.
#let remark(name: none, body) = statement("Remark", name: name, style: statement-styles.remark, body)

/// Typesets the restatement of a numbered statement, under the kind and number of the original and linked to it.
///
/// - target (label): The label of the original statement.
/// - name (none, content): An optional parenthetical name.
/// - style (str): The amsthm style: "plain", "definition" or "remark".
/// - body (content): The restated statement.
/// -> content
#let restate(target, name: none, style: "plain", body) = context {
  let el = query(target).first()
  block(width: 100%, above: 1em, below: 1em, {
    let head = link(el.location(), [#el.supplement #statement-number(el.location())])
    if style == "remark" { emph(head) } else { strong(head) }
    if name != none [ (#name)]
    if style == "remark" { emph[.] } else { strong[.] }
    h(5 * tp)
    if style == "plain" { emph(body) } else { body }
  })
}

/// Typesets a proof, closed by a square.
///
/// - title (content): The run-in label.
/// - body (content): The proof.
/// -> content
#let proof(title: [Proof], body) = block(width: 100%, above: 1.2em, below: 1.2em, {
  emph(title)
  [.]
  h(0.5em)
  body
  h(1fr)
  sym.square.stroked
})

/// Typesets a run-in paragraph heading.
///
/// - body (content): The heading text.
/// -> content
#let parhead(body) = strong(body) + h(1em)

/// Typesets the body of an algorithm: a title line followed by numbered lines.
///
/// - title (content): The algorithm's signature.
/// - lines (arguments): The lines, each a pair of indentation depth and content.
/// -> content
#let algorithm(title, ..lines) = {
  set par(justify: false, first-line-indent: 0pt)
  set align(left)
  block(
    width: 100%,
    {
      set block(spacing: 0.5em)
      block(title)
      grid(
        columns: (1.6em, 1fr),
        column-gutter: 0.6em,
        row-gutter: 0.55em,
        ..lines
          .pos()
          .enumerate()
          .map(((i, (depth, body))) => (
            align(right, text(size: 0.8em, str(i + 1))),
            pad(left: depth * 1.2em, body),
          ))
          .flatten(),
      )
    },
  )
}
