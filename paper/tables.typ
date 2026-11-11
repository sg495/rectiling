/// Matches a number: an optional sign or comparison prefix, an integer part with optional thousands separators, an optional decimal part, and an optional unit.
#let number-pattern = regex("^((?:\\\\[+~-]|[+~−≈<>])*\d[\d,]*)(\.\d+)?((?:\s|[×%†–#]).*)?$")

/// Parses a cell source as Typst markup.
///
/// - cell (str): The cell source.
/// -> content
#let markup(cell) = eval(cell, mode: "markup")

/// Splits a cell into its integer part, decimal part, unit and unit key; a cell that is not a number is all integer part, with no key.
///
/// The key is the unit without a leading range ("–1,234") or superscript markers, so that "12 ms" and "10–14 ms#super[†]" fall in one group.
///
/// - cell (str): The cell source.
/// -> dictionary
#let number-parts(cell) = {
  let m = cell.trim().match(number-pattern)
  if m == none { return (whole: markup(cell), fraction: none, unit: [], key: none) }
  let (whole, fraction, unit) = m.captures
  (
    whole: markup(whole),
    fraction: fraction,
    unit: if unit == none { [] } else if unit.starts-with(" ") {
      [#sym.space.nobreak#markup(unit.trim())]
    } else { markup(unit) },
    key: if unit == none { "" } else {
      unit.replace(regex("^–[\d,.]+"), "").replace(regex("#super\[[^\]]*\]"), "").trim()
    },
  )
}

/// Collects the header cells and the rules under column groups.
///
/// - kinds (array): The kind of each column.
/// - rows (array): The header rows, each an array of cell sources.
/// -> dictionary
#let header-cells(kinds, rows) = {
  let cells = ()
  let rules = ()
  let gutter = (0pt,) * (kinds.len() - 1)
  for (y, row) in rows.enumerate() {
    let j = 0
    while j < row.len() {
      if row.at(j) == "^" {
        j += 1
        continue
      }
      let span = 1
      while j + span < row.len() and row.at(j + span) == "<" { span += 1 }
      let down = 1
      while y + down < rows.len() and rows.at(y + down).at(j) == "^" { down += 1 }
      cells.push(table.cell(
        colspan: span,
        rowspan: down,
        align: (if span > 1 { center } else if kinds.at(j) == "l" { left } else { right }) + bottom,
        markup(row.at(j)),
      ))
      if span > 1 {
        rules.push(table.hline(y: y + 1, start: j, end: j + span, stroke: 0.4pt))
        if j > 0 { gutter.at(j - 1) = 0.6em }
        if j + span < kinds.len() { gutter.at(j + span - 1) = 0.6em }
      }
      j += span
    }
  }
  (cells: cells, rules: rules, gutter: gutter)
}

/// Splits each cell of a number column into integer part, decimal part, unit and unit key, adding a trailing decimal point to an integer whose unit group has decimals.
///
/// - cells (array): The column's cell sources.
/// -> array
#let number-column(cells) = {
  let parts = cells.map(number-parts)
  parts.map(p => {
    let decimal = p.key != none and parts.any(q => q.key == p.key and q.fraction != none)
    (p.whole, if p.fraction != none [#p.fraction] else if decimal [.] else [], p.unit, p.key)
  })
}

/// Typesets one cell of a number column, aligned at the decimal point with the cells of its unit group.
///
/// - column (array): The column, as returned by `number-column`.
/// - i (int): The row of the cell.
/// -> content
#let number-cell(column, i) = context {
  let key = column.at(i).at(3)
  let group = if key == none { (column.at(i),) } else { column.filter(c => c.at(3) == key) }
  let widths = (group, group, column)
    .enumerate()
    .map(((k, cells)) => calc.max(..cells.map(c => measure(c.at(k)).width)))
  let sides = (right, left, left)
  box(range(3).map(k => box(width: widths.at(k), align(sides.at(k), column.at(i).at(k)))).join())
}

/// Renders a table from rows of cell sources, shrinking it to the text width if it is wider.
///
/// Each column has a kind: `l` for left-aligned text, `r` for right-aligned content, or `n` for numbers.
/// Numbers align at the decimal point with the numbers of the same unit in their column, with the unit left-aligned beside them; an integer takes a trailing decimal point when its unit group has decimals.
/// The first `heads` rows are header rows; in them, `<` merges a cell into the cell on its left, forming a group ruled below, and `^` merges a cell into the cell above.
///
/// - kinds (array): The kind of each column.
/// - rows (array): The rows, each an array of cell sources in Typst markup.
/// - size (length, relative): The text size.
/// - heads (auto, int): The number of header rows; when auto, one, followed by another for as long as a header row contains `<`.
/// -> content
#let render(kinds, rows, size: 1em, heads: auto) = {
  if heads == auto {
    heads = 1
    while heads < rows.len() and rows.at(heads - 1).contains("<") { heads += 1 }
  }
  let header = header-cells(kinds, rows.slice(0, heads))
  let data = rows.slice(heads)
  let columns = range(kinds.len()).map(j => if kinds.at(j) == "n" {
    number-column(data.map(row => row.at(j)))
  })
  let body = ()
  for (i, row) in data.enumerate() {
    for (j, cell) in row.enumerate() {
      body.push(if kinds.at(j) == "n" {
        table.cell(align: right, number-cell(columns.at(j), i))
      } else {
        table.cell(align: if kinds.at(j) == "l" { left } else { right }, markup(cell))
      })
    }
  }
  let content = table(
    columns: kinds.len(),
    column-gutter: header.gutter,
    stroke: none,
    align: horizon,
    table.header(..header.cells, ..header.rules),
    table.hline(y: heads, stroke: 0.5pt),
    ..body,
  )
  set text(size: size)
  layout(region => {
    let width = measure(content).width
    if width <= region.width { content } else {
      set text(size: (region.width / width) * 1em)
      content
    }
  })
}

/// Renders a table from CSV rows whose first row gives the kind of each column.
///
/// - rows (array): The CSV rows, as returned by `csv`.
/// - transpose (bool): Whether to swap rows and columns; the first column becomes the header row, the new first column is right-aligned and the rest are numbers.
/// - corner (none, str): The cell source of the top-left corner after transposition.
/// - size (length, relative): The text size.
/// - heads (auto, int): The number of header rows.
/// -> content
#let datatable(rows, transpose: false, corner: none, size: 1em, heads: auto) = {
  let kinds = rows.at(0)
  let body = rows.slice(1)
  if transpose {
    body = range(body.at(0).len()).map(j => body.map(r => r.at(j)))
    kinds = ("r",) + ("n",) * (body.at(0).len() - 1)
  }
  if corner != none { body.at(0).at(0) = corner }
  render(kinds, body, size: size, heads: heads)
}
